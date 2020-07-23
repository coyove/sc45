package scmbed

import (
	"bytes"
	"errors"
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
	Default.Store("true", Bln(true))
	Default.Store("false", Bln(false))
	Default.Store("#t", Bln(true))
	Default.Store("#f", Bln(false))
	Default.Install("begin", Macro|Vararg, func(s *State) { s.Out = Lst(s.Args, s.Caller.Make("if"), Lst(Empty), Lst(Empty)) })
	Default.Install("and", Macro|Vararg, func(s *State) {
		if s.Args.Empty() {
			s.Out = Sym("#t", 0, 0)
			return
		}
		var build func(lhs *Pair) Value
		build = func(lhs *Pair) Value {
			if !lhs.HasNext() {
				return lhs.Val
			}
			return Lst(Empty, s.Caller.Make("if"), lhs.Val, build(lhs.Next), Sym("#f", 0, 0))
		}
		s.Out = build(s.Args)
	})
	Default.Install("or", Macro|Vararg, func(s *State) {
		if s.Args.Empty() {
			s.Out = Sym("#f", 0, 0)
			return
		}
		var build func(lhs *Pair) Value
		build = func(lhs *Pair) Value {
			if !lhs.HasNext() {
				return lhs.Val
			}
			return Lst(Empty, s.Caller.Make("if"), lhs.Val, Sym("#t", 0, 0), build(lhs.Next))
		}
		s.Out = build(s.Args)
	})
	Default.Install("==", 1|Vararg, func(s *State) {
		flag := true
		for s.In(); flag && !s.Args.Empty(); {
			flag = s.LastIn().Equals(s.In())
		}
		s.Out = Bln(flag)
	})
	Default.Store("=", Default.m["=="])
	Default.Install("!=", 1|Vararg, func(s *State) { s.Out = Bln(!s.In().Equals(s.In())) })
	Default.Install("<", 1|Vararg, func(s *State) {
		flag := true
		for s.InType('n'); flag && !s.Args.Empty(); {
			flag = s.LastIn().Num() < s.InType('n').Num()
		}
		s.Out = Bln(flag)
	})
	Default.Install("<=", 1|Vararg, func(s *State) {
		flag := true
		for s.InType('n'); flag && !s.Args.Empty(); {
			flag = s.LastIn().Num() <= s.InType('n').Num()
		}
		s.Out = Bln(flag)
	})
	Default.Install(">", 1|Vararg|Macro, func(s *State) { s.Out = Lst(Empty, s.Caller.Make("not"), Lst(s.Args, s.Caller.Make("<="))) })
	Default.Install(">=", 1|Vararg|Macro, func(s *State) { s.Out = Lst(Empty, s.Caller.Make("not"), Lst(s.Args, s.Caller.Make("<"))) })
	Default.Install("not", 1, func(s *State) { s.Out = Bln(!s.In().IsTrue()) })
	Default.Install("+", 1|Vararg, func(s *State) {
		s.Out = s.In()
		switch vn, vs, _, _, vtype := s.Out._value(); vtype {
		case 'n':
			for !s.Args.Empty() {
				vn += s.InType('n').Num()
			}
			s.Out = Num(vn)
		case 's':
			for !s.Args.Empty() {
				vs += s.InType('s').Str()
			}
			s.Out = Str(vs)
		default:
			panic(fmt.Errorf("can't apply 'add' on %v", s.Out))
		}
	})
	Default.Install("-", 1|Vararg, func(s *State) {
		a := s.InType('n').Num()
		if s.Args.Empty() {
			a = -a
		}
		for !s.Args.Empty() {
			a -= s.InType('n').Num()
		}
		s.Out = Num(a)
	})
	Default.Install("*", 1|Vararg, func(s *State) {
		a := s.InType('n').Num()
		for !s.Args.Empty() {
			a *= s.InType('n').Num()
		}
		s.Out = Num(a)
	})
	Default.Install("/", 1|Vararg, func(s *State) {
		a := s.InType('n').Num()
		for !s.Args.Empty() {
			a /= s.InType('n').Num()
		}
		s.Out = Num(a)
	})
	Default.Install("let", 1|Vararg|Macro, func(s *State) {
		var names, values []Value
		s.InType('l').Lst().Range(func(pair Value) bool {
			s.assert(pair.Type() == 'l' || s.panic("invalid binding list format: %v", pair))
			p := pair.Lst()
			s.assert(p.HasNext() && p.Val.Type() == 'y' && p.Val.Str() != "" || s.panic("invalid binding list format: %v", pair))
			names, values = append(names, p.Val), append(values, p.Next.Val)
			return true
		})
		fn := Lst(Empty, s.Caller.Make("lambda"), Lst(Empty, names...), Lst(s.Args, s.Caller.Make("if"), Lst(Empty), Lst(Empty)))
		s.Out = Lst(Lst(Empty, values...).Lst(), fn)
	})
	// Default.Install("unwrap-macro", 1, func(s *State) { s.Out = errorOrValue(s.Context.UnwrapMacro(s.In(0, 0))) })
	Default.Install("eval", 1, func(s *State) { s.Out = errorOrValue(s.Context.Exec(s.In())) })
	Default.Install("parse", 1, func(s *State) { s.Out = errorOrValue(s.Context.Parse(s.InType('s').Str())) })
	Default.Install("null?", 1, func(s *State) {
		if s.In().Type() == 'l' {
			s.Out = Bln(s.LastIn().Lst().Empty())
		} else {
			s.Out = Bln(false)
		}
	})
	Default.Install("set-car!", 2, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("set-car!: empty list"))
		l.Val = s.In()
	})
	Default.Install("set-cdr!", 2, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("set-cdr!: empty list"))
		l.Next = s.InType('l').Lst()
	})
	Default.Install("string->number", 1, func(s *State) { s.Out = errorOrValue(strconv.ParseFloat(s.InType('s').Str(), 64)) })
	Default.Install("symbol->string", 1, func(s *State) { s.Out = Str(s.InType('y').Str()) })
	Default.Install("number->string", 1, func(s *State) { s.Out = Str(strconv.FormatFloat(s.InType('n').Num(), 'f', -1, 64)) })
	Default.Install("string->symbol", 1, func(s *State) { s.Out = Sym(s.InType('s').Str(), 0, 0) })
	Default.Install("list", Vararg, func(s *State) { s.Out = Lst(s.Args) })
	Default.Install("append", 2, func(s *State) { s.Out = Lst(s.InType('l').Lst().Append(s.In())) })
	Default.Install("cons", 2, func(s *State) {
		p := &Pair{Val: s.In()}
		if s.In().Type() == 'l' {
			p.Next = s.LastIn().Lst()
		} else {
			p.Next = &Pair{Val: s.LastIn()}
		}
		s.Out = Lst(p)
	})
	Default.Install("car", 1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("car: empty list"))
		s.Out = l.Val
	})
	Default.Install("cdr", 1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("cdr: empty list"))
		s.Out = Lst(l.Next)
	})
	Default.Install("last", 1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("last: empty list"))
		s.Out = l.Last().Val
	})
	Default.Install("init", 1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("init: empty list"))
		s.Out = Lst(l.Take(-1))
	})
	Default.Install("length", 1, func(s *State) { s.Out = Num(float64(s.InType('l').Lst().Len())) })
	// Default.Install("raise", 1, func(s *State) { panic(s.In(0, 0)) })
	// Default.Install("pcall", 2, func(s *State) {
	// 	defer func() {
	// 		if r := recover(); r != nil {
	// 			if s.In(0, 0).Type() != 'f' {
	// 				s.Out = Val(r)
	// 			} else {
	// 				s.Out = errorOrValue(s.In(0, 'f').Fun().Call(Val(r)))
	// 			}
	// 		}
	// 	}()
	// 	s.Out = __exec(Lst(_Vquote(s.In(1, 0))), execState{curCaller: &s.Out, local: s.Context})
	// })
	Default.Install("apply", 2, func(s *State) {
		v, err := s.InType('f').Fun().Call(s.InType('l').Lst().ToSlice()...)
		s.assert(err == nil || s.panic("apply panic: %v", err))
		s.Out = v
	})
	Default.Install("error", 1, func(s *State) { s.Out = Val(errors.New(s.InType('s').Str())) })
	Default.Install("error?", 1, func(s *State) { _, ok := s.In().Val().(error); s.Out = Bln(ok) })
	Default.Install("void?", 1, func(s *State) { s.Out = Bln(s.In().IsVoid()) })
	Default.Install("list?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'l' && s.LastIn().Lst().Proper()) })
	Default.Install("pair?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'l') })
	Default.Install("symbol?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'y') })
	Default.Install("bool?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'b') })
	Default.Install("number?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'n') })
	Default.Install("string?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 's') })
	Default.Install("quote?", 1, func(s *State) { s.Out = Bln(s.In().Type() == 'q') })
	Default.Install("stringify", 1, func(s *State) { s.Out = Str(s.In().String()) })
}

func (ctx *Context) Install(name string, minArgsFlag int, f func(*State)) Value {
	ctx.assert(len(name) > 0 && minArgsFlag >= 0 || ctx.panic("invalid inputs"))
	fn := &Func{f: f, fargs: minArgsFlag & 0xffff, varg: minArgsFlag&Vararg != 0, macro: minArgsFlag&Macro != 0}
	ctx.Store(name, Fun(fn))
	return Fun(fn)
}

func (f *Func) Call(a ...Value) (Value, error) {
	expr := make([]Value, len(a)+1)
	expr[0] = _Vquote(Fun(f))
	for i := range a {
		expr[i+1] = _Vquote(a[i])
	}
	return ((*Context)(nil)).Exec(Lst(Empty, expr...))
}

func (f *Func) String() string {
	switch {
	case f.n.IsVoid():
		return "#" + ifstr(f.varg, "variadic-", "") + ifstr(f.macro, "builtin-macro-", "builtin-function-") + strconv.Itoa(f.fargs)
	case f.varg && len(f.nargs) == 1:
		return ifstr(f.macro, "(lambda# ", "(lambda ") + f.nargs[0] + " " + f.n.String() + ")"
	case f.varg:
		return ifstr(f.macro, "(lambda# (", "(lambda (") + strings.Join(f.nargs[:len(f.nargs)-1], " ") + " . " + f.nargs[len(f.nargs)-1] + ") " + f.n.String() + ")"
	default:
		return ifstr(f.macro, "(lambda# (", "(lambda (") + strings.Join(f.nargs, " ") + ") " + f.n.String() + ")"
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
	s.assert(t == 0 || v.Type() == t || s.panic("invalid argument #%d, expect '%v', got %v", s.argsidx, string(t), v))
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

func (m *Context) Store(k string, v Value) {
	if _, mv := m.find(k); mv == nil {
		m.set(k, v)
	} else {
		mv.set(k, v)
	}
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
				state.quasi = true
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
	switch _, va, vq, _, vtype := expr._value(); vtype {
	case 'q':
		return vq
	case 'y':
		v, ok := state.local.Load(va)
		state.assert(ok || state.panic("unbound %q", va))
		return v
	case 'l':
		// Try evaluating
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
			if __exec(c.Val, state).IsTrue() {
				state.assert(c.MoveNext(&c) || state.panic("invalid if syntax, missing true branch"))
				expr = c.Val // execute true-branch
				goto TAIL_CALL
			}
			c.MoveNext(&c)                     // skip if
			c.MoveNext(&c)                     // skip true branch
			for ; !c.Empty(); c.MoveNext(&c) { // execute rest statements: (if cond true-branch false-branch1 ... false-branchn)
				if !c.HasNext() {
					expr = c.Val
					goto TAIL_CALL
				}
				__exec(c.Val, state)
			}
			return Void
		case "lambda", "lambda#":
			state.assert(c.MoveNext(&c) || state.panic("invalid lambda syntax, missing parameters"))
			f := &Func{cls: state.local, macro: va == "lambda#"}
			switch _, va, _, bindings, vtype := c.Val._value(); vtype {
			case 'y': // (lambda args body)
				f.nargs, f.varg = []string{va}, true
			case 'l': // (lambda (a1 a2 ... an) body)
				for ; bindings != nil; bindings = bindings.Next {
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
				f.n = Lst(c, state.curCaller.Make("if"), Lst(Empty), Lst(Empty))
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
			state.assert(c.MoveNext(&c) && c.Val.Type() == 'l' || state.panic("invalid match syntax, missing body"))
			var symbolmap map[string]struct{}
			if len(symbols) > 0 {
				symbolmap = map[string]struct{}{}
				for _, s := range symbols {
					symbolmap[s.Str()] = struct{}{}
				}
			}
			m := &Context{parent: state.local, m: map[string]Value{}}
			if source.Lst().Match(pattern, symbolmap, m.m) {
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
			state.quasi = false
			return v
		case "unquote":
			panic(fmt.Errorf("unquote outside quasiquote"))
		case "set!":
			state.assert(c.MoveNext(&c) && c.Val.Type() == 'y' || state.panic("invalid set! syntax, missing binding symbol"))
			x := c.Val.Str()
			_, m := state.local.find(x)
			state.assert(m != nil || state.panic("set!: unbound %s", x))
			state.assert(c.MoveNext(&c) || state.panic("invalid set! syntax, missing binded value"))
			m.set(x, __exec(c.Val, state))
			return Void
		case "define", "define#":
			switch c.MoveNext(&c); c.Val.Type() {
			case 'y':
				x := c.Val.Str()
				_, ok := state.local.m[x]
				state.assert(!ok || state.panic("re-define %s", x))
				state.assert(c.MoveNext(&c) || state.panic("invalid define syntax, missing binded value"))
				state.local.set(x, __exec(c.Val, state))
			case 'l':
				lst := c.Val.Lst()
				state.assert(!lst.Empty() || state.panic("invalid define syntax, missing function name"))
				state.assert(c.MoveNext(&c) || state.panic("invalid define syntax, missing binded value"))
				s := Lst(Empty, head.Make("define"), lst.Val,
					Lst(c, head.Make(ifstr(va == "define", "lambda", "lambda#")), Lst(lst.Next)))
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
				for c.MoveNext(&c); !c.Empty(); c.MoveNext(&c) {
					values = values.append(__exec(c.Val, state))
				}
				m.set(name, values.value())
				break
			}
			state.assert(c.MoveNext(&c) || state.panic("too few arguments, expect at least %d", i+1))
			m.set(name, __exec(c.Val, state))
		}
		*state.curCaller = head
		state.local, expr = m, cc.n
		goto TAIL_CALL
	}

	s := State{Context: state.local, Out: Void, Caller: head}
	args := initlistbuilder()
	for c.MoveNext(&c); !c.Empty(); c.MoveNext(&c) {
		args = args.append(__exec(c.Val, state))
	}

	state.assert(args.count == cc.fargs || (cc.varg && args.count >= cc.fargs) ||
		state.panic("call: expect "+ifstr(cc.varg, "at least ", "")+strconv.Itoa(cc.fargs)+" arguments"))

	s.Args = args.L
	*state.curCaller = head
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
		v = Lst(v.Lst(), Sym("if", 0, 0), Lst(Empty), Lst(Empty))
	} else {
		v = Lst(Empty, Sym("if", 0, 0), Lst(Empty), Lst(Empty), v)
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

func (ctx *Context) Run(tmpl string) (result interface{}, err error) {
	c, err := ctx.Parse(tmpl)
	if err != nil {
		return nil, err
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
			switch s.Peek() {
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
				r, l := utf8.DecodeRuneInString(scanToDelim(s))
				if l == 0 {
					return Void, fmt.Errorf("invalid char")
				}
				comp = comp.append(Num(float64(r)))
			default:
				comp = comp.append(Sym("#"+scanToDelim(s), (s.Pos().Line), (s.Pos().Column)))
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
				comp = comp.append(Num(float64(v)))
			} else if v, ok := strconv.ParseFloat(text, 64); ok == nil || tok == scanner.Float {
				comp = comp.append(Num(v))
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
	return ctx.unwrapMacro(v), err
}

func (ctx *Context) unwrapMacro(v Value) Value {
	if v.Type() != 'l' || v.Lst().Empty() {
		return v
	}

	unwrapRest := func(v *Pair) Value {
		old := v
		// fmt.Println(Lst(old))
		for ; v != nil; v = v.Next {
			if v.testEmpty() == 't' {
				break
			}
			v.Val = ctx.unwrapMacro(v.Val)
		}
		// fmt.Println(Lst(old))
		return Lst(old)
	}

	comp := v.Lst()
	head := comp.Val
	if head.Type() != 'y' {
		return unwrapRest(comp)
	}

	va := head.Str()
	m, _ := ctx.Load(va)
	if !(m.Type() == 'f' && m.Fun().macro) {
		return unwrapRest(comp)
	}

	args := initlistbuilder().append(head)
	for comp.MoveNext(&comp); !comp.Empty(); comp.MoveNext(&comp) {
		args = args.append(_Vquote(ctx.unwrapMacro(comp.Val)))
	}

	v, err := ctx.Exec(args.value())
	if err != nil {
		panic(err)
	}
	return ctx.unwrapMacro(v)
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

func (e *assertable) assert(ok bool) {
	if !ok {
		panic(e.err)
	}
}

func (e *assertable) panic(t string, a ...interface{}) bool {
	e.err = fmt.Errorf(t, a...)
	return false
}

func errorOrValue(v interface{}, err error) Value {
	if err != nil {
		return Val(err)
	}
	return Val(v)
}

func ifstr(v bool, a, b string) string {
	if v {
		return a
	}
	return b
}

// zzzzzzzz

// Val creates Value from interface{}. uint64 and int64 will be stored as they were because float64 can't handle them correctly
func Val(v interface{}) Value {
	switch v := v.(type) {
	case Value:
		return v
	case nil:
		return Lst(Empty)
	case int:
		return Num(float64(v))
	case int8:
		return Num(float64(v))
	case int16:
		return Num(float64(v))
	case int32:
		return Num(float64(v))
	case uint:
		return Num(float64(v))
	case uint8:
		return Num(float64(v))
	case uint16:
		return Num(float64(v))
	case uint32:
		return Num(float64(v))
	case float32:
		return Num(float64(v))
	case float64:
		return Num(v)
	case string:
		return Str(v)
	case bool:
		return Bln(v)
	case []Value:
		return Lst(Empty, v...)
	default:
		va := Value{}
		*va._itfptr() = v
		return va
	}
}

// ValRec creates Value from interface{} recursively with slice, array or map being handled accordingly
func ValRec(v interface{}) Value {
	switch rv := reflect.ValueOf(v); rv.Kind() {
	case reflect.Slice, reflect.Array:
		res := make([]Value, rv.Len())
		for i := range res {
			res[i] = ValRec(rv.Index(i).Interface())
		}
		return Lst(Empty, res...)
	case reflect.Map:
		if rv.Type().Key().Kind() == reflect.String { // map[string]any
			res, iter := make(map[string]Value, rv.Len()), rv.MapRange()
			for iter.Next() {
				res[iter.Key().String()] = ValRec(iter.Value().Interface())
			}
			return Val(res)
		}
	}
	return Val(v)
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
func Str(v string) (vs Value) { return Value{val: 's', ptr: unsafe.Pointer(&v)} }
func Fun(f *Func) Value       { return Value{val: 'f', ptr: unsafe.Pointer(f)} }
func _Vquote(v Value) Value   { return Value{val: 'q', ptr: unsafe.Pointer(&v)} } // internal use

//go:nosplit
func (v *Value) _itfptr() *interface{} { return (*interface{})(unsafe.Pointer(v)) }
func (v Value) IsVoid() bool           { return v == Value{} }
func (v Value) IsTrue() bool           { return v.val == 2 }

// Type returns the type of Value: 'b'ool, 'n'umber, 'l'ist, 's'tring, 'f'unc, s'y'mbol, 'i'nterface, 'v'oid
func (v Value) Type() byte {
	switch v.val {
	case 1, 2:
		return 'b'
	case 'l', 'q', 'f', 's':
		return byte(v.val)
	default:
		if v.val >= 1<<51 {
			if v.val < 1<<52-1 {
				return 'y'
			}
			return 'n'
		}
		if v == (Value{}) {
			return 'v'
		}
		return 'i'
	}
}

func (v Value) String() string {
	switch vn, vs, vq, vl, vtype := v._value(); vtype {
	case 'q':
		return "'" + vq.String()
	case 'n':
		return strconv.FormatFloat(vn, 'f', -1, 64)
	case 's':
		return strconv.Quote(vs)
	case 'y':
		line, col := v.Pos()
		return vs + ifstr(line > 0, fmt.Sprintf(" /*%d:%d*/", line, col), "")
	case 'l':
		p := bytes.NewBufferString("(")
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
	default:
		switch v.Type() {
		case 'b':
			return strconv.FormatBool(v.Bln())
		case 'i':
			return "#" + fmt.Sprint(*v._itfptr())
		case 'f':
			return v.Fun().String()
		default:
			return "#void"
		}
	}
}
func (v Value) GoString() string {
	return fmt.Sprintf("{val:%016x ptr:%016x}", v.val, v.ptr)
}

func (v Value) Val() interface{} {
	switch vn, vs, vl, _, vtype := v._value(); vtype {
	case 'n':
		return vn
	case 's':
		return vs
	case 'l':
		return vl
	}
	switch v.Type() {
	case 'b':
		return v.Bln()
	case 'i':
		return *v._itfptr()
	case 'f':
		return v.Fun()
	default:
		return v
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
	}
	if vflag, v2flag := v.Type(), v2.Type(); vflag == v2flag {
		if vflag == 'y' || vflag == 's' {
			return *(*string)(v.ptr) == *(*string)(v2.ptr)
		}
		if vflag == 'i' {
			return *v._itfptr() == *v2._itfptr()
		}
	}
	return false
}

func (v Value) Fun() *Func      { return (*Func)(v.ptr) }
func (v Value) Bln() bool       { return v.val == 2 }
func (v Value) Num() float64    { return math.Float64frombits(^v.val) }
func (v Value) Str() string     { return *(*string)(v.ptr) }
func (v Value) Pos() (int, int) { return int((v.val >> 24) & 0xffffff), int(v.val & 0xffffff) }
func (v Value) Lst() *Pair      { return (*Pair)(v.ptr) }

func (v Value) _value() (vn float64, vs string, vq Value, vl *Pair, vtype byte) {
	switch vt := v.Type(); vt {
	case 'n':
		vn, vtype = v.Num(), 'n'
	case 'l':
		vl, vtype = v.Lst(), 'l'
	case 'q':
		vq, vtype = *(*Value)(v.ptr), 'q'
	case 's', 'y':
		vs, vtype = *(*string)(v.ptr), vt
	default:
		if v.IsVoid() {
			vtype = 'v'
		}
	}
	return
}

func (l *Pair) Empty() bool {
	if r := l.testEmpty(); r == 'i' {
		panic("improper list")
	} else {
		return r == 't'
	}
}
func (l *Pair) testEmpty() byte {
	if l.Next == nil {
		if !l._empty {
			return 'i'
		}
		return 't'
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
	b := listbuilder{}
	b.p = &Pair{_empty: true}
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

func (source *Pair) Match(pattern *Pair, symbols map[string]struct{}, m map[string]Value) bool {
	if pattern.Empty() && source.Empty() {
		return true
	}
	if pattern.Empty() {
		return false
	}
	isWildcard := func(s string) string {
		if len(s) > 1 && strings.HasSuffix(s, "*") {
			return s[:len(s)-1]
		}
		return ""
	}
	if source.Empty() {
		if pattern.Val.Type() == 'y' {
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
		if sym != "_" {
			if _, ok := symbols[sym]; ok {
				if !pattern.Val.Equals(source.Val) {
					return false
				}
				break
			}
			if w := isWildcard(sym); w != "" {
				m[w] = Lst(source)
				return true
			} else {
				m[sym] = source.Val
			}
		}
	case 'l':
		if source.Val.Type() != 'l' {
			return false
		}
		if !source.Val.Lst().Match(pattern.Val.Lst(), symbols, m) {
			return false
		}
	default:
		if !source.Val.Equals(pattern.Val) {
			return false
		}
	}
	return source.Next.Match(pattern.Next, symbols, m)
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
			}
			if l.HasNext() && !l.Next.HasNext() { // we are at second to last position
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
func (l *Pair) Append(v Value) *Pair {
	if l.Empty() {
		return &Pair{Val: v, Next: Empty}
	}
	b := initlistbuilder()
	for ; !l.Empty(); l = l.Next {
		b = b.append(l.Val)
	}
	return b.append(v).L
}
func (l *Pair) Last() (last *Pair) {
	for ; !l.Empty(); l = l.Next {
		last = l
	}
	return
}
func (l *Pair) Proper() bool {
	for {
		switch l.testEmpty() {
		case 'i':
			return false
		case 't':
			return true
		default:
			l = l.Next
		}
	}
}
