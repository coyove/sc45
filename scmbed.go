package scmbed

import (
	"bytes"
	"fmt"
	"math"
	"os"
	"reflect"
	"runtime/debug"
	"strconv"
	"strings"
	"text/scanner"
	"unicode"
	"unicode/utf8"
	"unsafe"
)

var (
	Default       = &Context{}
	Vararg, Macro = 1 << 30, 1 << 29
	Void, Empty   = Value{}, &Pair{_empty: true}
	Types         = map[byte]string{'s': "string", 'y': "symbol", 'n': "number", 'l': "list", 'i': "any", 'q': "quote", 'f': "function", 'v': "void"}
	TypesRev      = map[string]byte{"string": 's', "symbol": 'y', "number": 'n', "list": 'l', "any": 'i', "quote": 'q', "function": 'f', "void": 'v'}
)

type (
	Value struct {
		val uint64
		ptr unsafe.Pointer
	}
	Pair struct {
		Val    Value
		Next   *Pair
		_empty bool
	}
	Func struct {
		macro bool         // is macro
		varg  bool         // is variadic
		f     func(*State) // builtin function
		fargs int          // builtin: (minimal) arguments required
		n     Value        // native function
		nargs []string     // native: arguments binding list
		cls   *Context     // native: closure
	}
	State struct {
		*Context
		assertable
		argsidx     int
		arglast     Value
		Args        *Pair
		Out, Caller Value
	}
	Context struct {
		assertable
		parent *Context
		m      map[string]Value
	}
	execState struct {
		assertable
		curCaller *Value
		local     *Context
		quasi     bool
	}
	assertable struct{ err error }
)

func New() *Context { return Default.Copy() }

func init() {
	Default.Store("true", Bln(true)).Store("false", Bln(false))
	Default.Install("begin", Macro|Vararg, func(s *State) {
		s.Out = Lst(s.Args, s.Caller.Make("if"), Void, Void)
	}).Install("and", Macro|Vararg, func(s *State) {
		if s.Args.Empty() {
			s.Out = Bln(true)
		} else if !s.Args.HasNext() {
			s.Out = s.In()
		} else {
			s.Out = Lst(Empty, s.Caller.Make("if"), s.In(), Lst(s.Args, s.Caller.Make("and")), Bln(false))
		}
	}).Install("or", Macro|Vararg, func(s *State) {
		if s.Args.Empty() {
			s.Out = Bln(false)
		} else if !s.Args.HasNext() {
			s.Out = s.In()
		} else {
			s.Out = Lst(Empty, s.Caller.Make("if"), s.In(), Bln(true), Lst(s.Args, s.Caller.Make("or")))
		}
	}).Install("==", 1|Vararg, func(s *State) {
		flag := true
		for s.In(); flag && !s.Args.Empty(); {
			flag = s.LastIn().Equals(s.In())
		}
		s.Out = Bln(flag)
	}).Store("=", Default.m["=="]).Install("!=", 1|Vararg, func(s *State) {
		s.Out = Bln(!s.In().Equals(s.In()))
	}).Store("<>", Default.m["!="]).Install("<", 1|Vararg, func(s *State) {
		flag := true
		for s.InType('n'); flag && !s.Args.Empty(); {
			flag = s.LastIn().Num() < s.InType('n').Num()
		}
		s.Out = Bln(flag)
	}).Install("<=", 1|Vararg, func(s *State) {
		flag := true
		for s.InType('n'); flag && !s.Args.Empty(); {
			flag = s.LastIn().Num() <= s.InType('n').Num()
		}
		s.Out = Bln(flag)
	}).Install(">", 1|Vararg|Macro, func(s *State) {
		s.Out = Lst(Empty, s.Caller.Make("not"), Lst(s.Args, s.Caller.Make("<=")))
	}).Install(">=", 1|Vararg|Macro, func(s *State) {
		s.Out = Lst(Empty, s.Caller.Make("not"), Lst(s.Args, s.Caller.Make("<")))
	}).Install("not", 1, func(s *State) {
		s.Out = Bln(s.In().IsFalse())
	}).Install("+", 1|Vararg, func(s *State) {
		switch s.Out = s.In(); s.Out.Type() {
		case 'n':
			vn := s.Out.Num()
			for !s.Args.Empty() {
				vn += s.InType('n').Num()
			}
			s.Out = Num(vn)
		case 's':
			vs := s.Out.Str()
			for !s.Args.Empty() {
				vs += s.InType('s').Str()
			}
			s.Out = Str(vs)
		default:
			panic(fmt.Errorf("can't apply 'add' on %v", s.Out))
		}
	}).Install("-", 1|Vararg, func(s *State) {
		a := s.InType('n').Num()
		if s.Args.Empty() {
			a = -a
		}
		for !s.Args.Empty() {
			a -= s.InType('n').Num()
		}
		s.Out = Num(a)
	}).Install("*", 1|Vararg, func(s *State) {
		a := s.InType('n').Num()
		for !s.Args.Empty() {
			a *= s.InType('n').Num()
		}
		s.Out = Num(a)
	}).Install("/", 1|Vararg, func(s *State) {
		a := s.InType('n').Num()
		for !s.Args.Empty() {
			a /= s.InType('n').Num()
		}
		s.Out = Num(a)
	}).Install("let", 1|Vararg|Macro, func(s *State) {
		var names, values []Value
		s.InType('l').Lst().Range(func(pair Value) bool {
			s.assert(pair.Type() == 'l' || s.panic("invalid binding list format: %v", pair))
			p := pair.Lst()
			s.assert(p.HasNext() && p.Val.Type() == 'y' && p.Val.Str() != "" || s.panic("invalid binding list format: %v", pair))
			names, values = append(names, p.Val), append(values, p.Next.Val)
			return true
		})
		fn := Lst(Empty, s.Caller.Make("lambda"), Lst(Empty, names...), Lst(s.Args, s.Caller.Make("if"), Void, Void))
		s.Out = Lst(Lst(Empty, values...).Lst(), fn)
	}).Install("eval", 1, func(s *State) {
		s.Out = ev2(s.Context.Exec(s.In()))
	}).Install("parse", 1, func(s *State) {
		s.Out = ev2(s.Context.Parse(s.InType('s').Str()))
	}).Install("set-car!", 2, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("set-car!: empty list"))
		l.Val = s.In()
	}).Install("set-cdr!", 2, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("set-cdr!: empty list"))
		l.Next = s.InType('l').Lst()
	}).Install("list", Vararg, func(s *State) {
		s.Out = Lst(s.Args)
	}).Install("append", 2, func(s *State) {
		s.Out = Lst(s.InType('l').Lst().Append(s.InType('l').Lst()))
	}).Install("cons", 2, func(s *State) {
		p := &Pair{Val: s.In()}
		if s.In().Type() == 'l' {
			p.Next = s.LastIn().Lst()
		} else {
			p.Next = &Pair{Val: s.LastIn()}
		}
		s.Out = Lst(p)
	}).Install("car", 1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("car: empty list"))
		s.Out = l.Val
	}).Install("cdr", 1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("cdr: empty list"))
		s.Out = Lst(l.Next)
	}).Install("last", 1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("last: empty list"))
		s.Out = l.Last().Val
	}).Install("init", 1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("init: empty list"))
		s.Out = Lst(l.Take(-1))
	}).Install("length", 1, func(s *State) {
		s.Out = Num(float64(s.InType('l').Lst().Len()))
	}).Install("pcall", 2, func(s *State) {
		rc := s.In()
		defer func() {
			if r := recover(); r != nil {
				if rc.Type() != 'f' {
					s.Out = Val(r)
				} else {
					s.Out = ev2(rc.Fun().Call(Val(r)))
				}
			}
		}()
		s.Out = __exec(Lst(Empty, _Qt(s.In())), execState{curCaller: &s.Out, local: s.Context})
	}).Install("apply", 2, func(s *State) {
		v, err := s.InType('f').Fun().Call(s.InType('l').Lst().ToSlice()...)
		s.assert(err == nil || s.panic("apply panic: %v", err))
		s.Out = v
	}).
		Install("raise", 1, func(s *State) { panic(s.In()) }).
		Install("string->number", 1, func(s *State) { s.Out = ev2(strconv.ParseFloat(s.InType('s').Str(), 64)) }).
		Install("symbol->string", 1, func(s *State) { s.Out = Str(s.InType('y').Str()) }).
		Install("number->string", 1, func(s *State) { s.Out = Str(strconv.FormatFloat(s.InType('n').Num(), 'f', -1, 64)) }).
		Install("string->symbol", 1, func(s *State) { s.Out = Sym(s.InType('s').Str(), 0, 0) }).
		Install("string->error", 1, func(s *State) { s.Out = Val(fmt.Errorf(s.InType('s').Str())) }).
		Install("null?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'l' && s.LastIn().Lst().Empty()) }).
		Install("error?", 1, func(s *State) { _, ok := s.In().Val().(error); s.Out = Bln(ok) }).
		Install("void?", 1, func(s *State) { s.Out = Bln(s.In().IsVoid()) }).
		Install("list?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'l' && s.LastIn().Lst().Proper()) }).
		Install("pair?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'l') }).
		Install("symbol?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'y') }).
		Install("bool?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'b') }).
		Install("number?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'n') }).
		Install("string?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 's') }).
		Install("stringify", 1, func(s *State) { s.Out = Str(s.In().String()) })
}

func (ctx *Context) Install(name string, minArgsFlag int, f func(*State)) *Context {
	ctx.assert(len(name) > 0 && minArgsFlag >= 0 || ctx.panic("invalid inputs"))
	fn := &Func{f: f, fargs: minArgsFlag & 0xffff, varg: minArgsFlag&Vararg != 0, macro: minArgsFlag&Macro != 0}
	return ctx.Store(name, Fun(fn))
}

func (f *Func) Call(a ...Value) (Value, error) {
	expr := make([]Value, len(a)+1)
	expr[0] = _Qt(Fun(f))
	for i := range a {
		expr[i+1] = _Qt(a[i])
	}
	return ((*Context)(nil)).Exec(Lst(Empty, expr...))
}

func (f *Func) String() string {
	switch {
	case f.n.IsVoid():
		return "#" + ifstr(f.varg, "variadic-", "") + ifstr(f.macro, "builtin-macro-", "builtin-function-") + strconv.Itoa(f.fargs)
	case f.varg && len(f.nargs) == 1:
		return ifstr(f.macro, "(lambda-macro ", "(lambda ") + f.nargs[0] + " " + f.n.String() + ")"
	case f.varg:
		return ifstr(f.macro, "(lambda-macro (", "(lambda (") + strings.Join(f.nargs[:len(f.nargs)-1], " ") + " . " + f.nargs[len(f.nargs)-1] + ") " + f.n.String() + ")"
	default:
		return ifstr(f.macro, "(lambda-macro (", "(lambda (") + strings.Join(f.nargs, " ") + ") " + f.n.String() + ")"
	}
}

// In pops an argument
func (s *State) In() Value {
	s.assert(!s.Args.Empty() || s.panic("too few arguments, expect at least %d", s.argsidx+1))
	v := s.Args.Val
	s.argsidx, s.arglast = s.argsidx+1, v
	s.Args = s.Args.Next
	return v
}

func (s *State) InType(t byte) Value {
	v := s.In()
	s.assert(t == 0 || v.Type() == t || s.panic("invalid argument #%d, expect %s, got %v", s.argsidx, Types[t], v))
	return v
}

func (s *State) LastIn() Value { return s.arglast }

func (m *Context) find(k string) (Value, *Context) {
	for ; m != nil; m = m.parent {
		if v, ok := m.m[k]; ok {
			return v, m
		}
	}
	return Void, nil
}

func (m *Context) set(k string, v Value) {
	if m.m == nil {
		m.m = make(map[string]Value, 4)
	}
	m.m[k] = v
}

func (m *Context) Store(k string, v Value) *Context {
	if _, mv := m.find(k); mv == nil {
		m.set(k, v)
	} else {
		mv.set(k, v)
	}
	return m
}

func (m *Context) Load(k string) (Value, bool) {
	v, mv := m.find(k)
	return v, mv != nil
}

func (m *Context) Delete(k string) (Value, bool) {
	v, mv := m.find(k)
	if mv != nil {
		delete(mv.m, k)
	}
	return v, mv != nil
}

func (m *Context) Len() int { return len(m.m) }

func (m *Context) Unsafe() map[string]Value { return m.m }

func (m *Context) Copy() *Context {
	m2 := &Context{m: make(map[string]Value, len(m.m)), parent: m.parent}
	for k, v := range m.m {
		m2.m[k] = v
	}
	return m2
}

func __exec(expr Value, state execState) Value {
	if state.quasi {
		if expr.Type() == 'l' && !expr.Lst().Empty() {
			lst := expr.Lst()
			if x := lst.Val; x.Type() == 'y' && x.Str() == "unquote" {
				state.assert(lst.HasNext() || state.panic("invalid unquote syntax"))
				state.quasi = false
				v := __exec(lst.Next.Val, state)
				return v
			}
			results := initlistbuilder()
			for ; !lst.Empty(); lst = lst.Next {
				results = results.append(__exec(lst.Val, state))
			}
			return results.value()
		}
		return expr
	}

TAIL_CALL:
	switch expr.Type() {
	case 'q':
		return expr._Qt()
	case 'y':
		v, ok := state.local.Load(expr.Str())
		state.assert(ok || state.panic("unbound %v", expr))
		return v
	case 'l': // evaluating the list
	default:
		return expr
	}

	c := expr.Lst()
	if c.Empty() {
		return Lst(Empty)
	}

	head := c.Val
	if *state.curCaller = c.Val; state.curCaller.Type() == 'y' {
		switch va := state.curCaller.Str(); va {
		case "if":
			state.assert(c.MoveNext(&c) || state.panic("invalid if syntax, missing condition"))
			if !__exec(c.Val, state).IsFalse() {
				state.assert(c.MoveNext(&c) || state.panic("invalid if syntax, missing true branch"))
				expr = c.Val // execute true-branch
				goto TAIL_CALL
			}
			c.MoveNext(&c)                     // skip condition
			c.MoveNext(&c)                     // skip true branch
			for ; !c.Empty(); c.MoveNext(&c) { // execute rest statements: (if cond true-branch false-1 ... false-n)
				if !c.HasNext() {
					expr = c.Val
					goto TAIL_CALL
				}
				__exec(c.Val, state)
			}
			return Void
		case "lambda":
			state.assert(c.MoveNext(&c) || state.panic("invalid lambda syntax, missing parameters"))
			f := &Func{cls: state.local}
			switch c.Val.Type() {
			case 'y': // (lambda args body)
				f.nargs, f.varg = []string{c.Val.Str()}, true
			case 'l': // (lambda (a1 a2 ... an) body)
				for bindings := c.Val.Lst(); bindings != nil; bindings = bindings.Next {
					switch bindings.testEmpty() {
					case 'i':
						f.varg = true
						fallthrough
					case 'f':
						state.assert(bindings.Val.Type() == 'y' || state.panic("invalid parameter, expect valid symbol"))
						f.nargs = append(f.nargs, bindings.Val.Str())
					}
				}
			default:
				panic(fmt.Errorf("invalid binding list: %v", c.Val))
			}
			state.assert(c.MoveNext(&c) || state.panic("invalid lambda syntax, missing lambda body"))
			if f.n = c.Val; c.HasNext() {
				f.n = Lst(c, state.curCaller.Make("if"), Void, Void)
			}
			return Fun(f)
		case "match":
			state.assert(c.MoveNext(&c) || state.panic("invalid match syntax, missing source"))
			source := __exec(c.Val, state)
			state.assert(source.Type() == 'l' || state.panic("invalid match syntax, expect source to be list"))
			state.assert(c.MoveNext(&c) && c.Val.Type() == 'l' || state.panic("invalid match syntax, missing symbol list"))
			symbols := c.Val.Lst().ToSlice()
		MATCH_NEXT:
			state.assert(c.MoveNext(&c) && c.Val.Type() == 'l' || state.panic("invalid match syntax, missing pattern"))
			pattern := c.Val.Lst()
			state.assert(c.MoveNext(&c) || state.panic("invalid match syntax, missing body"))
			var symbolmap map[string]struct{}
			if len(symbols) > 0 {
				symbolmap = map[string]struct{}{}
				for _, s := range symbols {
					symbolmap[s.Str()] = struct{}{}
				}
			}
			m := &Context{parent: state.local, m: map[string]Value{}}
			if source.Lst().match(state, pattern, false, symbolmap, m.m) {
				return __exec(c.Val, execState{curCaller: state.curCaller, local: m})
			}
			if c.HasNext() {
				goto MATCH_NEXT
			}
			return Void
		case "quote":
			state.assert(c.MoveNext(&c) || state.panic("invalid quote syntax"))
			return c.Val
		case "quasiquote":
			state.assert(c.MoveNext(&c) || state.panic("invalid quasiquote syntax"))
			state.quasi = true
			v := __exec(c.Val, state)
			return v
		case "unquote":
			panic(fmt.Errorf("unquote outside quasiquote"))
		case "set!":
			state.assert(c.MoveNext(&c) && c.Val.Type() == 'y' || state.panic("invalid set! syntax, missing symbol"))
			x := c.Val.Str()
			_, m := state.local.find(x)
			state.assert(m != nil || state.panic("set!: unbound %s", x))
			state.assert(c.MoveNext(&c) || state.panic("invalid set! syntax, missing bound value"))
			m.set(x, __exec(c.Val, state))
			return Void
		case "define-macro":
			state.assert(c.MoveNext(&c) && c.Val.Type() == 'y' || state.panic("invalid define-macro syntax, missing symbol"))
			x := c.Val.Str()
			state.assert(state.local.m[x].IsVoid() || state.panic("re-define %s", x)).
				assert(c.MoveNext(&c) || state.panic("invalid define-macro syntax, missing bound value"))
			f := __exec(c.Val, state)
			state.assert(f.Type() == 'f' || state.panic("invalid define-macro syntax, expect function"))
			f.Fun().macro = true
			state.local.set(x, f)
			return Void
		case "define":
			switch c.MoveNext(&c); c.Val.Type() {
			case 'y':
				x := c.Val.Str()
				state.assert(state.local.m[x].IsVoid() || state.panic("re-define %s", x)).
					assert(c.MoveNext(&c) || state.panic("invalid define syntax, missing bound value"))
				state.local.set(x, __exec(c.Val, state))
			case 'l':
				lst := c.Val.Lst()
				state.assert(!lst.Empty() || state.panic("invalid define syntax, missing function name")).
					assert(c.MoveNext(&c) || state.panic("invalid define syntax, missing bound value"))
				s := Lst(Empty, head.Make("define"), lst.Val, Lst(c, head.Make("lambda"), Lst(lst.Next)))
				return __exec(s, state)
			default:
				panic("invalid define syntax, missing binding symbol")
			}
			return Void
		}
	}

	fn := __exec(head, state)
	state.assert(fn.Type() == 'f' || state.panic("invalid function: %v", head))
	cc := fn.Fun()

	if cc.f == nil {
		m := &Context{parent: cc.cls}
		for i, name := range cc.nargs {
			if cc.varg && i == len(cc.nargs)-1 {
				values := initlistbuilder()
				c.Next.Range(func(v Value) bool { values = values.append(__exec(v, state)); return true })
				m.set(name, values.value())
				break
			}
			state.assert(c.MoveNext(&c) || state.panic("too few arguments, expect at least %d", i+1))
			m.set(name, __exec(c.Val, state))
		}
		*state.curCaller, state.local, expr = head, m, cc.n
		goto TAIL_CALL
	}

	s := State{Context: state.local, Out: Void, Caller: head}
	args := initlistbuilder()
	c.Next.Range(func(v Value) bool { args = args.append(__exec(v, state)); return true })

	*state.curCaller = head
	state.assert(args.count == cc.fargs || (cc.varg && args.count >= cc.fargs) ||
		state.panic("call: expect "+ifstr(cc.varg, "at least ", "")+strconv.Itoa(cc.fargs)+" arguments"))

	s.Args = args.L
	cc.f(&s)
	return s.Out
}

func (ctx *Context) Parse(text string) (expr Value, err error) {
	var s scanner.Scanner
	s.Init(strings.NewReader(text))
	s.Mode &^= scanner.ScanChars | scanner.ScanRawStrings
	s.Error = func(s *scanner.Scanner, msg string) {
		pos := s.Position
		if !pos.IsValid() {
			pos = s.Pos()
		}
		err = fmt.Errorf("parse: %s at %d:%d", msg, pos.Line, pos.Column)
	}
	v, perr := ctx.scan(&s, false)
	if perr != nil {
		return Void, fmt.Errorf("parse: %v at %d:%d", perr, s.Pos().Line, s.Pos().Column)
	}
	if err != nil {
		return Void, err
	}
	if v.Type() == 'l' {
		v = Lst(v.Lst(), Sym("if", 0, 0), Void, Void)
	} else {
		v = Lst(Empty, Sym("if", 0, 0), Void, Void, v)
	}
	// log.Println(v)
	return ctx.UnwrapMacro(v)
}

func (ctx *Context) Exec(c Value) (output Value, err error) {
	var curCaller Value
	defer func() {
		if r := recover(); r != nil {
			if os.Getenv("SBD_STACK") != "" {
				fmt.Println(string(debug.Stack()))
			}
			err = fmt.Errorf("%v at %v", r, curCaller)
		}
	}()
	return __exec(c, execState{local: ctx, curCaller: &curCaller}), nil
}

func (ctx *Context) Run(tmpl string) (result Value, err error) {
	c, err := ctx.Parse(tmpl)
	if err != nil {
		return Void, err
	}
	return ctx.Exec(c)
}

func (ctx *Context) scan(s *scanner.Scanner, scanOne bool) (Value, error) {
	comp := initlistbuilder()
LOOP:
	for tok := s.Scan(); tok != scanner.EOF; tok = s.Scan() {
		// fmt.Println(s.TokenText())
		switch tok {
		case scanner.String, scanner.RawString:
			t, err := strconv.Unquote(s.TokenText())
			if err != nil {
				return Value{}, err
			}
			comp = comp.append(Str(t))
		case '#':
			switch pr := s.Peek(); pr {
			case '|': // #| comment |#
				for s.Scan(); ; {
					if current, next := s.Scan(), s.Peek(); current == scanner.EOF {
						return Void, fmt.Errorf("incomplete comment block")
					} else if current == '|' && next == '#' {
						s.Scan()
						break
					}
				}
			case '/': // #/char
				s.Scan()
				switch n := scanToDelim(s); strings.ToLower(n) {
				case "space", "newline", "return", "tab", "backspace", "alert", "form", "backslash":
					comp = comp.append(Num(float64(map[string]rune{
						"space": ' ', "newline": '\n', "return": '\r', "tab": '\t', "backspace": '\b', "alert": '\a', "form": '\f', "backslash": '\\',
					}[strings.ToLower(n)])))
				default:
					r, l := utf8.DecodeRuneInString(n)
					if l == 0 {
						return Void, fmt.Errorf("invalid char")
					}
					comp = comp.append(Num(float64(r)))
				}
			case 't', 'f':
				s.Scan()
				comp = comp.append(Bln(pr == 't'))
			case 'v':
				s.Scan()
				comp = comp.append(Void)
			default:
				comp = comp.append(Sym("#"+scanToDelim(s), s.Pos().Line, s.Pos().Column))
			}
		case ';':
			for ; ; s.Scan() {
				if next := s.Peek(); next == scanner.EOF || next == '\n' {
					break
				}
			}
		case '(', '[':
			c, err := ctx.scan(s, false)
			if err != nil {
				return Value{}, err
			}
			comp = comp.append(c)
		case ')', ']':
			break LOOP
		case '.':
			c, err := ctx.scan(s, true)
			if err != nil {
				return Void, err
			}
			comp.p.Val, comp.p._empty = c, false
			if s := s.Scan(); s != scanner.EOF && s != ']' && s != ')' {
				return Void, fmt.Errorf("invalid dot syntax")
			}
			return comp.value(), nil
		case '\'', '`', ',':
			c, err := ctx.scan(s, true)
			if err != nil {
				return Void, err
			}
			if c.IsVoid() {
				return Void, fmt.Errorf("invalid *quote syntax")
			}
			comp = comp.append(Lst(Empty, Sym(ifstr(tok == '\'', "quote", ifstr(tok == '`', "quasiquote", "unquote")), 0, 0), c))
		default:
			text := s.TokenText() + scanToDelim(s)
			if v, ok := strconv.ParseInt(text, 0, 64); ok == nil || tok == scanner.Int {
				comp = comp.append(NumStr(float64(v), text))
			} else if v, ok := strconv.ParseFloat(text, 64); ok == nil || tok == scanner.Float {
				comp = comp.append(NumStr(v, text))
			} else {
				comp = comp.append(Sym(text, (s.Pos().Line), (s.Pos().Column)))
			}
		}
		if scanOne && comp.count >= 1 {
			return comp.L.Val, nil
		}
	}
	return comp.value(), nil
}

func (ctx *Context) UnwrapMacro(v Value) (result Value, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("macro unwrap panic: %v", r)
		}
	}()
	return ctx.unwrapMacro(v, false), err
}

func (ctx *Context) unwrapMacro(v Value, quasi bool) Value {
	if v.Type() != 'l' || v.Lst().Empty() {
		return v
	}

	comp := v.Lst()
	if head := comp.Val; head.Type() == 'y' {
		switch head.Str() {
		case "quote":
			return v
		case "quasiquote":
			quasi = true
		case "unquote":
			quasi = false
		default:
			if quasi {
				return v
			}
			if m, _ := ctx.Load(head.Str()); m.Type() == 'f' && m.Fun().macro {
				args := initlistbuilder().append(head)
				for comp.MoveNext(&comp); !comp.Empty(); comp.MoveNext(&comp) {
					args = args.append(_Qt(ctx.unwrapMacro(comp.Val, false)))
				}
				v, err := ctx.Exec(args.value())
				if err != nil {
					panic(err)
				}
				return ctx.unwrapMacro(v, false)
			}
		}
	}
	old := comp
	for ; comp != nil; comp = comp.Next {
		if comp.testEmpty() == 't' {
			break
		}
		comp.Val = ctx.unwrapMacro(comp.Val, quasi)
	}
	return Lst(old)
}

func scanToDelim(s *scanner.Scanner) string {
	for p := (bytes.Buffer{}); ; {
		next := s.Peek()
		if unicode.IsSpace(next) ||
			next < 0 || // Special scanner.XXXX runes
			next == '[' || next == ']' || next == '(' || next == ')' || next == ';' {
			return p.String()
		}
		s.Scan()
		p.WriteString(s.TokenText())
	}
}

func (e *assertable) assert(ok bool) *assertable {
	if !ok {
		panic(e.err)
	}
	return e
}

func (e *assertable) panic(t string, a ...interface{}) bool {
	e.err = fmt.Errorf(t, a...)
	return false
}

func ev2(v interface{}, err error) Value { return [2]Value{Val(v), Val(err)}[Bln(err != nil).BlnNum()] }
func ifstr(v bool, t, f string) string   { return [2]string{f, t}[Bln(v).BlnNum()] }
func ifbyte(v bool, t, f byte) byte      { return [2]byte{f, t}[Bln(v).BlnNum()] }

// Val creates Value from interface{}. uint64 and int64 will be stored as they were because float64 can't handle them correctly
func Val(v interface{}) Value {
	if v, ok := v.(Value); ok {
		return v
	}
	switch rv := reflect.ValueOf(v); rv.Kind() {
	case reflect.Interface:
		return Val(rv.Elem())
	case reflect.Invalid:
		return Void
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32:
		return Num(float64(rv.Int()))
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32:
		return Num(float64(rv.Uint()))
	case reflect.Float32, reflect.Float64:
		return Num(rv.Float())
	case reflect.String:
		return Str(rv.String())
	case reflect.Bool:
		return Bln(rv.Bool())
	}
	va := Value{}
	*va._itfptr() = v
	return va
}

func Bln(v bool) Value {
	if v {
		return Value{val: 2}
	}
	return Value{val: 1}
}
func Sym(v string, line, col int) Value {
	return Value{ptr: unsafe.Pointer(&v), val: 1<<51 | (uint64(line)&0xffffff)<<24 | (uint64(col) & 0xffffff)}
}
func Lst(lst *Pair, l ...Value) Value {
	for i := len(l) - 1; i >= 0; i-- {
		n := &Pair{Val: l[i], Next: lst}
		lst = n
	}
	return Value{val: 'l', ptr: unsafe.Pointer(lst)}
}
func Num(v float64) Value {
	if math.IsNaN(v) {
		return Value{val: 0x800FFFFFFFFFFFFE} // ^7FF0000000000001
	}
	return Value{val: ^math.Float64bits(v)}
}
func NumStr(v float64, o string) Value { n := Num(v); n.ptr = unsafe.Pointer(&o); return n }
func Str(v string) (vs Value)          { return Value{val: 's', ptr: unsafe.Pointer(&v)} }
func Fun(f *Func) Value                { return Value{val: 'f', ptr: unsafe.Pointer(f)} }
func _Qt(v Value) Value                { return Value{val: 'q', ptr: unsafe.Pointer(&v)} } // internal use

//go:nosplit
func (v *Value) _itfptr() *interface{} { return (*interface{})(unsafe.Pointer(v)) }
func (v Value) IsVoid() bool           { return v == Value{} }
func (v Value) IsFalse() bool          { return v.val < 2 } // 0: void, 1: false

// Type returns the type of Value: 'b'ool, 'n'umber, 'l'ist, 's'tring, 'f'unc, s'y'mbol, 'i'nterface, 'v'oid
func (v Value) Type() byte {
	switch v.val {
	case 1, 2:
		return 'b'
	case 'l', 'q', 'f', 's':
		return byte(v.val)
	default:
		if v.val >= 1<<51 {
			return ifbyte(v.val < 1<<52-1, 'y', 'n')
		}
		return ifbyte(v == (Value{}), 'v', 'i')
	}
}

func (v Value) String() string {
	switch v.Type() {
	case 'q':
		return "'" + v._Qt().String()
	case 'n':
		return strconv.FormatFloat(v.Num(), 'f', -1, 64)
	case 's':
		return strconv.Quote(v.Str())
	case 'y':
		line, col := v.Pos()
		return v.Str() + ifstr(line > 0, fmt.Sprintf(" /*%d:%d*/", line, col), "")
	case 'l':
		vl, p := v.Lst(), bytes.NewBufferString("(")
		for vl != nil && !vl._empty {
			if vl.Next == nil {
				p.WriteString(". ")
				p.WriteString(vl.Val.String())
			} else {
				p.WriteString(vl.Val.String())
				p.WriteString(" ")
			}
			vl = vl.Next
		}
		for p.Len() > 0 && p.Bytes()[p.Len()-1] == ' ' {
			p.Truncate(p.Len() - 1)
		}
		p.WriteString(")")
		return p.String()
	case 'b':
		return ifstr(v.Bln(), "#t", "#f")
	case 'i':
		return "#" + fmt.Sprint(*v._itfptr())
	case 'f':
		return v.Fun().String()
	default:
		return "#v"
	}
}
func (v Value) GoString() string { return fmt.Sprintf("{val:%016x ptr:%016x}", v.val, v.ptr) }

func (v Value) Val() interface{} {
	switch v.Type() {
	case 'n':
		return v.Num()
	case 's', 'y':
		return v.Str()
	case 'l':
		a := []interface{}{}
		v.Lst().Range(func(v Value) bool { a = append(a, v.Val()); return true })
		return a
	case 'b':
		return v.Bln()
	case 'i':
		return *v._itfptr()
	case 'f':
		return v.Fun()
	default:
		return nil
	}
}

func (v Value) Make(text string) Value {
	if v.Type() == 'y' {
		v.ptr = unsafe.Pointer(&text)
		return v
	}
	return Sym(text, 0, 0)
}

func (v Value) Equals(v2 Value) bool {
	if v == v2 {
		return true
	} else if vflag, v2flag := v.Type(), v2.Type(); vflag == v2flag {
		switch vflag {
		case 'n':
			return v.val == v2.val
		case 'y', 's':
			return v.Str() == v2.Str()
		case 'i':
			return *v._itfptr() == *v2._itfptr()
		}
	}
	return false
}

func (v Value) Fun() *Func      { return (*Func)(v.ptr) }
func (v Value) Bln() bool       { return v.val == 2 }
func (v Value) BlnNum() int     { return int(v.val - 1) } // true: 1, false: 0
func (v Value) Num() float64    { return math.Float64frombits(^v.val) }
func (v Value) Str() string     { return *(*string)(v.ptr) }
func (v Value) Pos() (int, int) { return int((v.val >> 24) & 0xffffff), int(v.val & 0xffffff) }
func (v Value) Lst() *Pair      { return (*Pair)(v.ptr) }
func (v Value) _Qt() Value      { return *(*Value)(v.ptr) }

func (l *Pair) Empty() bool {
	if r := l.testEmpty(); r == 'i' {
		panic("improper list")
	} else {
		return r == 't'
	}
}
func (l *Pair) testEmpty() byte {
	if l.Next == nil {
		return ifbyte(l._empty, 't', 'i')
	}
	return 'f'
}
func (l *Pair) HasNext() bool { return l.Next != nil && !l.Next.Empty() }
func (l *Pair) MoveNext(ll **Pair) bool {
	if l.HasNext() {
		*ll = l.Next
		return true
	}
	*ll = Empty
	return false
}
func (l *Pair) Len() (length int) {
	for ; !l.Empty(); l = l.Next {
		length++
	}
	return
}
func (l *Pair) Range(cb func(Value) bool) {
	for flag := true; flag && !l.Empty(); l = l.Next {
		flag = cb(l.Val)
	}
}
func (l *Pair) ToSlice() (s []Value) {
	l.Range(func(v Value) bool { s = append(s, v); return true })
	return
}

type listbuilder struct {
	count int
	L, p  *Pair
}

func initlistbuilder() listbuilder {
	b := listbuilder{p: &Pair{_empty: true}}
	b.L = b.p
	return b
}
func (b listbuilder) append(v Value) listbuilder {
	b.p._empty, b.p.Val, b.p.Next = false, v, &Pair{_empty: true}
	b.p = b.p.Next
	b.count++
	return b
}
func (b listbuilder) value() Value { return Lst(b.L) }

func (source *Pair) match(state execState, pattern *Pair, metWildcard bool, symbols map[string]struct{}, m map[string]Value) bool {
	if pattern.Empty() && source.Empty() {
		return true
	}
	if pattern.Empty() {
		return false
	}
	isWildcard := func(s string) string {
		if strings.HasSuffix(s, "*") {
			if metWildcard {
				panic("multiple wildcards in one pattern")
			}
			return ifstr(len(s) == 1, "*", s[:len(s)-1])
		}
		return ""
	}
	if source.Empty() {
		if pattern.Val.Type() == 'y' && !pattern.HasNext() {
			if w := isWildcard(pattern.Val.Str()); w != "" {
				m[w] = Lst(Empty)
				return true
			}
		}
		return false
	}
	switch pattern.Val.Type() {
	case 'y':
		sym := pattern.Val.Str()
		if sym == "_" {
			break
		}
		if _, ok := symbols[sym]; ok {
			if !pattern.Val.Equals(source.Val) {
				return false
			}
			break
		}
		if w := isWildcard(sym); w != "" {
			if pattern.HasNext() {
				n := source.Len() - pattern.Next.Len()
				if n < 0 { // the remaining symbols in 'source' is less than 'pattern'
					return false
				}
				// The first n symbols will go into 'ww'
				ww := initlistbuilder()
				for ; n > 0; n-- {
					ww = ww.append(source.Val)
					source = source.Next
				}
				m[w] = ww.value()
				return source.match(state, pattern.Next, true, symbols, m)
			}
			m[w] = Lst(source)
			return true
		}
		if strings.HasPrefix(sym, "#:") {
			if x := TypesRev[sym[2:]]; x > 0 && source.Val.Type() != x {
				return false
			}
			break
		}
		m[sym] = source.Val
	case 'l':
		if lst := pattern.Val.Lst(); lst.Val.Type() == 'y' && lst.Val.Str() == "quote" {
			m := &Context{parent: state.local, m: map[string]Value{"_": source.Val}}
			if __exec(lst.Next.Val, execState{curCaller: state.curCaller, local: m}).IsFalse() {
				return false
			}
			break
		}
		if source.Val.Type() != 'l' {
			return false
		}
		if !source.Val.Lst().match(state, pattern.Val.Lst(), false, symbols, m) {
			return false
		}
	default:
		if !source.Val.Equals(pattern.Val) {
			return false
		}
	}
	return source.Next.match(state, pattern.Next, false, symbols, m)
}
func (l *Pair) Take(n int) *Pair {
	if n == 0 {
		return Empty
	}
	b := initlistbuilder()
	for ; !l.Empty(); l = l.Next {
		b = b.append(l.Val)
		if n == -1 {
			if !l.HasNext() { // we are at the last position, this means l.Len() == 1
				return Empty
			} else if /* l.HasNext() &&*/ !l.Next.HasNext() { // we are at second to last position
				return b.L
			}
		}
		if b.count == n {
			break
		}
	}
	if b.count != n {
		panic(fmt.Errorf("take: not enough values to take, need %d out of %d", n, b.count))
	}
	return b.L
}
func (l *Pair) Append(l2 *Pair) *Pair {
	b := initlistbuilder()
	l.Range(func(v Value) bool { b = b.append(v); return true })
	*b.p = *l2
	return b.L
}
func (l *Pair) Last() (last *Pair) {
	for ; !l.Empty(); l = l.Next {
		last = l
	}
	return
}
func (l *Pair) Proper() bool {
	for ; ; l = l.Next {
		if f := l.testEmpty(); f == 'i' {
			return false
		} else if f == 't' {
			return true
		}
	}
}
