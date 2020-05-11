package scmbed

import (
	"bytes"
	"errors"
	"fmt"
	"log"
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
	Default     = &Context{}
	Void, Empty = Value{}, Lst()
)

type (
	Value struct {
		flag int            // interface{} 0
		ptr  unsafe.Pointer // interface{} 1
		val  float64
	}
	Func struct {
		macro, varg bool
		// Used by Go builtin functions
		sig string
		f   func(*State)
		// Used by native functions
		n     Value
		nargs []string
		cls   *Context
	}
	State struct {
		*Context
		assertable
		Args        []Value
		Out, Caller Value
	}
	Context struct {
		assertable
		parent *Context
		m      map[string]Value
	}
	execState struct {
		assertable
		callAtom *Value
		local    *Context
		quasi    bool
		args     struct { // all go native calls share the same stack: args.list, each used region is identified by args.start
			start int
			list  *[]Value
		}
	}
	assertable struct{ err error }
)

func New() *Context { return Default.Copy() }

func init() {
	Default.Store("define", Fun(&Func{sig: "(syntax·define var val)", f: func(*State) {}}))
	Default.Store("set!", Fun(&Func{sig: "(syntax·set! var val)", f: func(*State) {}}))
	Default.Store("lambda", Fun(&Func{sig: "(syntax·lambda paramlist body)", f: func(*State) {}}))
	Default.Store("lambda#", Fun(&Func{sig: "(syntax·lambda# paramlist body)", f: func(*State) {}}))
	Default.Store("if", Fun(&Func{sig: "(syntax·if cond true-branch false-branch ...)", f: func(*State) {}}))
	Default.Store("quote", Fun(&Func{sig: "(syntax·quote a)", f: func(*State) {}}))
	Default.Store("unquote", Fun(&Func{sig: "(syntax·unquote a)", f: func(*State) {}}))
	Default.Store("quasiquote", Fun(&Func{sig: "(syntax·quasiquote a)", f: func(*State) {}}))
	Default.Store("true", Bln(true))
	Default.Store("false", Bln(false))
	Default.Store("#t", Bln(true))
	Default.Store("#f", Bln(false))
	Default.Install("#(begin ...)", func(s *State) { s.Out = begin(s.Caller, s.Args...) })
	Default.Install("(rest-args)", func(s *State) {
		s.Out = Empty
		if v, ok := s.Context.m["\x00"]; ok {
			s.Out = v
		}
	})
	Default.Install("#(and bool...)", func(s *State) {
		if len(s.Args) == 0 {
			s.Out = Atm("true", 0, 0)
			return
		}
		var build func(lhs Value, args []Value) Value
		build = func(lhs Value, args []Value) Value {
			if len(args) == 0 {
				return lhs
			}
			return Lst(s.Caller.Rename("if"), lhs, build(args[0], args[1:]), Atm("false", 0, 0))
		}
		s.Out = build(s.Args[0], s.Args[1:])
	})
	Default.Install("#(or bool...)", func(s *State) {
		if len(s.Args) == 0 {
			s.Out = Atm("false", 0, 0)
			return
		}
		var build func(lhs Value, args []Value) Value
		build = func(lhs Value, args []Value) Value {
			if len(args) == 0 {
				return lhs
			}
			return Lst(s.Caller.Rename("if"), lhs, Atm("true", 0, 0), build(args[0], args[1:]))
		}
		s.Out = build(s.Args[0], s.Args[1:])
	})
	Default.Install("(== a a...)", func(s *State) {
		for i, a := 1, s.In(0, 0); i < len(s.Args); i++ {
			if !a.Equals(s.Args[i]) {
				s.Out = Bln(false)
				return
			}
		}
		s.Out = Bln(true)
	})
	Default.Store("=", Default.m["=="])
	Default.Install("(!= a a)", func(s *State) { s.Out = Bln(!s.In(0, 0).Equals(s.In(1, 0))) })
	Default.Install("(< a a...)", func(s *State) {
		for i, _ := 1, s.In(0, 0); i < len(s.Args); i++ {
			if !itfLess(s, s.Args[i-1], i) {
				s.Out = Bln(false)
				return
			}
		}
		s.Out = Bln(true)
	})
	Default.Install("(<= a a...)", func(s *State) {
		for i, _ := 1, s.In(0, 0); i < len(s.Args); i++ {
			if !itfLess(s, s.Args[i-1], i) && !s.Args[i-1].Equals(s.Args[i]) {
				s.Out = Bln(false)
				return
			}
		}
		s.Out = Bln(true)
	})
	Default.Install("#(> a a...)", func(s *State) {
		s.Out = Lst(s.Caller.Rename("not"), Lst(append([]Value{s.Caller.Rename("<=")}, s.Args...)...))
	})
	Default.Install("#(>= a a...)", func(s *State) {
		s.Out = Lst(s.Caller.Rename("not"), Lst(append([]Value{s.Caller.Rename("<")}, s.Args...)...))
	})
	Default.Install("(not bool)", func(s *State) { s.Out = Bln(!s.In(0, 0).IsTrue()) })
	Default.Install("(+ num-str num-str...)", func(s *State) {
		s.Out = s.In(0, 0)
		switch vn, vs, _, vl, vtype := s.Out._value(); vtype {
		case 'n':
			for i := 1; i < len(s.Args); i++ {
				vn += s.In(i, 'n').Num()
			}
			s.Out = Num(vn)
		case 'l':
			for i := 1; i < len(s.Args); i++ {
				vl = []Value{_Vddd(vl...), _Vddd(s.In(i, 'l').Lst()...)}
			}
			s.Out = Lst(vl...)
		case 's':
			for i := 1; i < len(s.Args); i++ {
				vs += s.In(i, 's').Str()
			}
			s.Out = Str(vs)
		default:
			panic(fmt.Errorf("can't apply 'add' on %v", s.Out))
		}
	})
	Default.Install("(- number number...)", func(s *State) {
		a := s.In(0, 'n').Num()
		if len(s.Args) == 1 {
			a = -a
		}
		for i := 1; i < len(s.Args); i++ {
			a -= s.In(i, 'n').Num()
		}
		s.Out = Num(a)
	})
	Default.Install("(* number number...)", func(s *State) {
		a := s.In(0, 'n').Num()
		for i := 1; i < len(s.Args); i++ {
			a *= s.In(i, 'n').Num()
		}
		s.Out = Num(a)
	})
	Default.Install("(/ number number...)", func(s *State) {
		a := s.In(0, 'n').Num()
		for i := 1; i < len(s.Args); i++ {
			a /= s.In(i, 'n').Num()
		}
		s.Out = Num(a)
	})
	Default.Install("#(let ((var1 val1) ... (varn valn)) expr...)", func(s *State) {
		names, values := []Value{}, []Value{}
		for _, pair := range s.In(0, 'l').Lst() {
			s.assert(pair.Type() == 'l' || s.panic("invalid binding list format: %v", pair))
			p := pair.Lst()
			s.assert(len(p) == 2 && p[0].Type() == 'a' && p[0].Str() != "" || s.panic("invalid binding list format: %v", pair))
			names, values = append(names, p[0]), append(values, p[1])
		}
		fn := Lst(s.Caller.Rename("lambda"), Lst(names...), begin(s.Caller, s.Args[1:]...))
		s.Out = Lst(Lst(fn, _Vddd(values...))._flatten(true)...) // call fn
	})
	Default.Install("(unwrap-macro expr)", func(s *State) { s.Out = errorOrValue(s.Context.UnwrapMacro(s.In(0, 0))) })
	Default.Install("(eval expr)", func(s *State) { s.Out = errorOrValue(s.Context.Exec(s.In(0, 0))) })
	Default.Install("(parse expr-string)", func(s *State) { s.Out = errorOrValue(s.Context.Parse(s.In(0, 's').Str())) })
	Default.Install("(null? a)", func(s *State) { s.Out = Bln(IsEmpty(s.In(0, 0))) })
	Default.Install("(set-car! list value)", func(s *State) {
		_, ok := Head(s.In(0, 'l').Lst(), func(Value) Value { return s.In(1, 0) })
		s.assert(ok || s.panic("set-car!: empty list"))
	})
	Default.Install("(set-last! list value)", func(s *State) {
		_, ok := Last(s.In(0, 'l').Lst(), func(Value) Value { return s.In(1, 0) })
		s.assert(ok || s.panic("set-last!: empty list"))
	})
	Default.Install("(number text)", func(s *State) { s.Out = errorOrValue(strconv.ParseFloat(s.In(0, 's').Str(), 64)) })
	Default.Install("(string a)", func(s *State) {
		if x := s.In(0, 0).Type(); x == 'a' || x == 's' {
			s.Out = s.In(0, 0)
		} else {
			s.Out = Str(s.In(0, 0).String())
		}
	})
	Default.Install("(atom string)", func(s *State) { s.Out = Atm(s.In(0, 's').Str(), 0, 0) })
	Default.Install("(list v1 v2 ... vn)", func(s *State) { s.Out = Lst(append([]Value{}, s.Args...)...) })
	Default.Install("(append list list2)", func(s *State) { s.Out = Lst(_Vddd(s.In(0, 'l').Lst()...), _Vddd(s.In(1, 'l').Lst()...)) })
	Default.Install("(add list a)", func(s *State) { s.Out = Lst(_Vddd(s.In(0, 'l').Lst()...), s.In(1, 0)) })
	Default.Install("(cons a list)", func(s *State) { s.Out = Lst(s.In(0, 0), _Vddd(s.In(1, 'l').Lst()...)) })
	Default.Install("(car list)", func(s *State) {
		v, ok := Head(s.In(0, 'l').Lst(), nil)
		s.assert(ok || s.panic("car: empty list"))
		s.Out = v
	})
	Default.Install("(cdr list)", func(s *State) {
		v, ok := Tail(s.In(0, 'l').Lst())
		s.assert(ok || s.panic("cdr: empty list"))
		s.Out = Lst(v...)
	})
	Default.Install("(last list)", func(s *State) {
		v, ok := Last(s.In(0, 'l').Lst(), nil)
		s.assert(ok || s.panic("last: empty list"))
		s.Out = v
	})
	Default.Install("(init list)", func(s *State) {
		v, ok := Init(s.In(0, 'l').Lst())
		s.assert(ok || s.panic("init: empty list"))
		s.Out = Lst(v...)
	})
	Default.Install("(length list)", func(s *State) { s.Out = Num(float64(Length(s.In(0, 'l').Lst()))) })
	Default.Install("(raise a)", func(s *State) { panic(s.In(0, 0)) })
	Default.Install("(pcall handler function)", func(s *State) {
		defer func() {
			if r := recover(); r != nil {
				if s.In(0, 0).Type() != 'f' {
					s.Out = Val(r)
				} else {
					s.Out = errorOrValue(s.In(0, 'f').Fun().Call(Val(r)))
				}
			}
		}()
		s.Out = __exec(Lst(_Vquote(s.In(1, 0))), execState{callAtom: &s.Out, local: s.Context})
	})
	Default.Install("(apply function (list a1 a2 ... an))", func(s *State) {
		v, err := s.In(0, 'f').Fun().Call(s.In(1, 'l')._flatten(true)...)
		s.assert(err == nil || s.panic("apply panic: %v", err))
		s.Out = v
	})
	Default.Install("(error text)", func(s *State) { s.Out = Val(errors.New(s.In(0, 's').Str())) })
	Default.Install("(error? a)", func(s *State) { _, ok := s.In(0, 0).Val().(error); s.Out = Bln(ok) })
	Default.Install("(void? a)", func(s *State) { s.Out = Bln(s.In(0, 0).IsVoid()) })
	Default.Install("(list? a)", func(s *State) { s.Out = Bln(s.In(0, 0).Type() == 'l') })
	Default.Install("(atom? a)", func(s *State) { s.Out = Bln(s.In(0, 0).Type() == 'a') })
	Default.Install("(bool? a)", func(s *State) { s.Out = Bln(s.In(0, 0).Type() == 'b') })
	Default.Install("(number? a)", func(s *State) { s.Out = Bln(s.In(0, 0).Type() == 'n') })
	Default.Install("(string? a)", func(s *State) { s.Out = Bln(s.In(0, 0).Type() == 's') })
	Default.Install("(quote? a)", func(s *State) { s.Out = Bln(s.In(0, 0).Type() == 'q') })
	Default.Install("(stringify a)", func(s *State) { s.Out = Str(s.In(0, 0).String()) })
}

func (ctx *Context) Install(name string, f func(*State)) Value {
	fn := &Func{f: f, sig: strings.TrimSpace(name)}
	if strings.HasPrefix(fn.sig, "#") {
		fn.sig, fn.macro = fn.sig[1:], true
	}
	if strings.HasPrefix(fn.sig, "(") && strings.HasSuffix(fn.sig, ")") {
		name = fn.sig[1:strings.IndexAny(fn.sig, " )")]
	}
	ctx.Store(name, Fun(fn))
	return Fun(fn)
}

func (f *Func) Call(a ...Value) (Value, error) {
	expr := make([]Value, len(a)+1)
	expr[0] = _Vquote(Fun(f))
	for i := range a {
		expr[i+1] = _Vquote(a[i])
	}
	return ((*Context)(nil)).Exec(Lst(expr...))
}

func (f *Func) String() string {
	if f.n.IsVoid() {
		return f.sig[1:strings.IndexAny(f.sig, " )")] + " /* " + f.sig + ifstr(f.macro, " ; builtin macro */", " */")
	}
	return ifstr(f.macro, "(lambda# ", "(lambda ") +
		ifstr(f.varg, "", "(") + strings.Join(f.nargs, " ") + ifstr(f.varg, "", ") ") + f.n.String() + ")"
}

// In returns nth argument and panics when: t != 0 && t != v.Type()
func (s *State) In(i int, t byte) Value {
	s.assert(i >= 0 && i < len(s.Args) || s.panic("too few arguments, expect at least %d", i+1))
	s.assert(t == 0 || s.Args[i].Type() == t || s.panic("invalid argument #%d, expect '%v', got %v", i, string(t), s.Args[i]))
	return s.Args[i]
}

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

func (m *Context) Copy() *Context {
	m2 := &Context{m: make(map[string]Value, len(m.m)), parent: m.parent}
	for k, v := range m.m {
		m2.m[k] = v
	}
	return m2
}

func __exec(expr Value, state execState) Value {
	if state.quasi {
		if expr.Type() == 'l' && expr._len() > 0 {
			if x := expr._at(0); x.Type() == 'a' && x.Str() == "unquote" {
				state.assert(expr._len() == 2 || state.panic("invalid unquote syntax"))
				state.quasi = false
				v := __exec(expr._at(1), state)
				state.quasi = true
				return v
			}
			e := make([]Value, expr._len())
			for i := range e {
				e[i] = __exec(expr._at(i), state)
			}
			return Lst(e...)
		}
		return expr
	}

TAIL_CALL:
	switch _, va, vq, _, vtype := expr._value(); vtype {
	case 'q':
		return vq
	case 'a':
		v, ok := state.local.Load(va)
		state.assert(ok || state.panic("unbound %q", va))
		return v
	case 'l':
		// Try evaluating
	default:
		return expr
	}

	c := expr
	if c._len() == 0 {
		return Empty
	}

	*state.callAtom = c._at(0)
	switch va, _ := c._at(0)._atm(); va {
	case "if":
		state.assert(c._len() >= 3 || state.panic("invalid if syntax"))
		if __exec(c._at(1), state).IsTrue() {
			expr = c._at(2) // execute true-branch
			goto TAIL_CALL
		}
		for i := 3; i < c._len(); i++ { // execute rest statements: (if cond true-branch false-branch1 ... false-branchn)
			if i == c._len()-1 {
				expr = c._at(i)
				goto TAIL_CALL
			}
			__exec(c._at(i), state)
		}
		return Void
	case "lambda", "lambda#":
		state.assert(c._len() >= 3 || state.panic("invalid lambda syntax"))
		f := &Func{n: c._at(2), cls: state.local, macro: va == "lambda#"}
		if c._len() > 3 {
			f.n = begin(c._at(0), c.Lst()[2:]...)
		}
		switch _, va, _, bindings, vtype := c._at(1)._value(); vtype {
		case 'a':
			f.nargs, f.varg = []string{va}, true
		case 'l':
			for i, n := range bindings {
				va, ok := n._atm()
				state.assert(ok || state.panic("invalid parameter %d, expect valid atom", i+1))
				f.nargs = append(f.nargs, va)
			}
		default:
			panic(fmt.Errorf("invalid binding list: %v", c._at(1)))
		}
		return Fun(f)
	case "quote":
		state.assert(c._len() == 2 || state.panic("invalid quote syntax"))
		return c._at(1)
	case "quasiquote":
		state.assert(c._len() == 2 || state.panic("invalid quasiquote syntax"))
		state.quasi = true
		v := __exec(c._at(1), state)
		state.quasi = false
		return v
	case "unquote":
		panic(fmt.Errorf("unquote outside quasiquote"))
	case "set!":
		state.assert(c._len() == 3 && c._at(1).Type() == 'a' || state.panic("invalid set! syntax"))
		x := c._at(1).Str()
		_, m := state.local.find(x)
		state.assert(m != nil || state.panic("set!: unbound %s", x))
		m.set(x, __exec(c._at(2), state))
		return Void
	case "define":
		state.assert(c._len() == 3 && c._at(1).Type() == 'a' || state.panic("invalid define syntax"))
		x := c._at(1).Str()
		_, ok := state.local.m[x]
		state.assert(!ok || state.panic("re-define %s", x))
		state.local.set(x, __exec(c._at(2), state))
		return Void
	default:
		fn := __exec(c._at(0), state)
		state.assert(fn.Type() == 'f' || state.panic("invalid function: %v", c._at(0)))
		cc := fn.Fun()

		if cc.f == nil {
			m := &Context{parent: cc.cls}
			if !cc.varg {
				for i, name := range cc.nargs {
					state.assert(i+1 < c._len() || state.panic("too few arguments, expect at least %d", i+1))
					m.set(name, __exec(c._at(i+1), state))
				}
				if c._len()-1 > len(cc.nargs) {
					values := make([]Value, 0, c._len())
					for i := len(cc.nargs) + 1; i < c._len(); i++ {
						values = append(values, __exec(c._at(i), state))
					}
					m.set("\x00", Lst(values...))
				}
			} else {
				values := make([]Value, 0, c._len())
				for i := 1; i < c._len(); i++ {
					values = append(values, __exec(c._at(i), state))
				}
				m.set(cc.nargs[0], Lst(values...))
				m.set("\x00", Lst(values...))
			}
			*state.callAtom = c._at(0)
			state.local, expr = m, cc.n
			goto TAIL_CALL
		}

		s := State{Context: state.local, Out: Void, Caller: c._at(0)}
		if state.args.list == nil {
			state.args.list = new([]Value)
		}

		// tail, _ := Tail(c.Lst())
		args := state.args
		for i := 1; i < c._len(); i++ {
			// _range(0, tail, func(i int, v Value) (Value, bool) {
			state.args.start = len(*args.list)
			*args.list = append(*args.list, __exec(c._at(i), state))
			// 	return v, true
			// })
		}
		s.Args = (*args.list)[args.start:]
		*state.callAtom = c._at(0)
		cc.f(&s)
		*args.list = (*args.list)[:args.start]
		return s.Out
	}
}

func (ctx *Context) Parse(text string) (Value, error) {
	var s scanner.Scanner
	var err error
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
		v = begin(Void, v.Lst()...)
	} else {
		v = begin(Void, v)
	}
	// log.Println(v)
	return ctx.UnwrapMacro(v)
	// log.Println(v)
}

func (ctx *Context) Exec(c Value) (output Value, err error) {
	var callAtom Value
	defer func() {
		if r := recover(); r != nil {
			if os.Getenv("ONE_STACK") != "" {
				log.Println(string(debug.Stack()))
			}
			err = fmt.Errorf("%v at %v", r, callAtom)
		}
	}()
	return __exec(c, execState{local: ctx, callAtom: &callAtom}), nil
}

func (ctx *Context) Run(tmpl string) (result interface{}, err error) {
	c, err := ctx.Parse(tmpl)
	if err != nil {
		return nil, err
	}
	return ctx.Exec(c)
}

func (ctx *Context) scan(s *scanner.Scanner, scanOne bool) (Value, error) {
	var comp []Value
LOOP:
	for tok := s.Scan(); tok != scanner.EOF; tok = s.Scan() {
		// fmt.Println(s.TokenText())
		switch tok {
		case scanner.String, scanner.RawString:
			t, err := strconv.Unquote(s.TokenText())
			if err != nil {
				return Value{}, err
			}
			comp = append(comp, Str(t))
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
				comp = append(comp, Num(float64(r)))
			default:
				comp = append(comp, Atm("#"+scanToDelim(s), (s.Pos().Line), (s.Pos().Column)))
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
			comp = append(comp, c)
		case ')', ']':
			break LOOP
		case '\'', '`', ',':
			c, err := ctx.scan(s, true)
			if err != nil {
				return Void, err
			}
			if c.IsVoid() {
				return Void, fmt.Errorf("invalid *quote syntax")
			}
			comp = append(comp, Lst(Atm(ifstr(tok == '\'', "quote", ifstr(tok == '`', "quasiquote", "unquote")), 0, 0), c))
		default:
			text := s.TokenText() + scanToDelim(s)
			if v, ok := strconv.ParseInt(text, 0, 64); ok == nil || tok == scanner.Int {
				comp = append(comp, Num(float64(v)))
			} else if v, ok := strconv.ParseFloat(text, 64); ok == nil || tok == scanner.Float {
				comp = append(comp, Num(v))
			} else {
				comp = append(comp, Atm(text, (s.Pos().Line), (s.Pos().Column)))
			}
		}
		if scanOne && len(comp) >= 1 {
			return comp[0], nil
		}
	}
	return Lst(comp...), nil
}

func (ctx *Context) UnwrapMacro(v Value) (Value, error) {
	var err error
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("macro unwrap panic: %v", r)
		}
	}()
	return ctx.unwrapMacro(v).Flatten(true), err
}

func (ctx *Context) unwrapMacro(v Value) Value {
	if v.Type() != 'l' || IsEmpty(v) {
		return v
	}

	unwrapRest := func(v []Value) Value {
		for comp := v; ; comp, _ = Tail(comp) {
			if _, ok := Head(comp, ctx.unwrapMacro); !ok {
				break
			}
		}
		return Lst(v...)
	}

	comp := v.Lst()
	head, _ := Head(comp, nil)
	if head.Type() != 'a' {
		return unwrapRest(comp)
	}

	va := head.Str()
	if va == "define" || va == "define#" {
		comp, _ := Tail(comp)                     // skip 'define*'
		x, ok := Head(comp, nil)                  // get identifier
		if ok && x.Type() == 'l' && !IsEmpty(x) { // (define (func paramlist) body...)
			x := x._flatten(true) // flattern
			comp, _ = Tail(comp)  // skip identifier
			comp = unwrapRest(comp).Lst()
			return Lst(head.Rename("define"), x[0],
				Lst(append([]Value{head.Rename(ifstr(va == "define#", "lambda#", "lambda")),
					Lst(x[1:]...)}, _Vddd(comp...))...))
		}
	}

	m, _ := ctx.Load(va)
	if !(m.Type() == 'f' && m.Fun().macro) {
		return unwrapRest(comp)
	}

	args := []Value{_Vquote(m)}

	comp, _ = Tail(comp) // skip macro itself
	for v, ok := Head(comp, nil); ok; v, ok = Head(comp, nil) {
		args = append(args, _Vquote(ctx.unwrapMacro(v).Flatten(true)))
		comp, _ = Tail(comp)
	}

	v, err := ctx.Exec(Lst(args...))
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

func itfLess(s *State, a Value, i int) bool {
	switch vn, vs, _, _, vtype := a._value(); vtype {
	case 'n':
		return vn < s.In(i, 'n').Num()
	case 's':
		return vs < s.In(i, 's').Str()
	}
	panic(fmt.Errorf("argument #%d: %v and %v are not comparable", i, a, s.In(i, 0)))
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

func Head(v []Value, setter func(Value) Value) (Value, bool) {
	for i := range v {
		if v[i].Type() != 'd' {
			if setter != nil {
				v[i] = setter(v[i])
			}
			return v[i], true
		} else if h, ok := Head(v[i].Lst(), setter); ok {
			return h, true
		}
	}
	return Void, false
}

func Last(v []Value, setter func(Value) Value) (Value, bool) {
	for i := len(v) - 1; i >= 0; i-- {
		if v[i].Type() != 'd' {
			if setter != nil {
				v[i] = setter(v[i])
			}
			return v[i], true
		} else if h, ok := Last(v[i].Lst(), setter); ok {
			return h, true
		}
	}
	return Void, false
}

func _range(idx int, v []Value, fn func(int, Value) (Value, bool)) (newidx int, cont bool) {
	for i, el := range v {
		if el.Type() != 'd' {
			v[i], cont = fn(idx, el)
			idx++
		} else {
			idx, cont = _range(idx, el.Lst(), fn)
		}
		if !cont {
			return idx, false
		}
	}
	return idx, true
}

func Tail(v []Value) ([]Value, bool) {
	if len(v) == 0 {
		return nil, false
	}
	if d := v[0]; d.Type() == 'd' {
		t, ok := Tail(d.Lst())
		if len(v) == 1 {
			return t, ok
		} else if !ok {
			return Tail(v[1:])
		} else if len(t) > 0 {
			return []Value{_Vddd(t...), _Vddd(v[1:]...)}, true
		}
	}
	return v[1:], true
}

func Init(v []Value) ([]Value, bool) {
	if len(v) == 0 {
		return nil, false
	}
	if d := v[len(v)-1]; d.Type() == 'd' {
		t, ok := Init(d.Lst())
		if len(v) == 1 {
			return t, ok
		} else if !ok {
			return Init(v[:len(v)-1])
		} else if len(t) > 0 {
			return []Value{_Vddd(v[:len(v)-1]...), _Vddd(t...)}, true
		}
	}
	return v[:len(v)-1], true
}

func Length(v []Value) (l int) {
	for _, v := range v {
		if v.Type() == 'd' {
			l += Length(v.Lst())
		} else {
			l++
		}
	}
	return
}

func IsEmpty(v Value) bool {
	if v.Type() == 'l' {
		_, ok := Head(v.Lst(), nil)
		return !ok
	}
	return false
}

func ifstr(v bool, a, b string) string {
	if v {
		return a
	}
	return b
}

func begin(lead Value, exprs ...Value) Value {
	return Lst(append([]Value{lead.Rename("if"), Empty, Empty}, exprs...)...)
}

// zzzzzzzz

// Val creates Value from interface{}. uint64 and int64 will be stored as they were because float64 can't handle them correctly
func Val(v interface{}) Value {
	switch v := v.(type) {
	case Value:
		return v
	case nil:
		return Empty
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
		return Lst(v...)
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
		return Lst(res...)
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
		return Value{val: 1, flag: -'b'}
	}
	return Value{val: 0, flag: -'b'}
}
func Atm(v string, line, col int) Value {
	return Value{flag: -'a', ptr: unsafe.Pointer(&v), val: math.Float64frombits(uint64(line)<<32 | uint64(col))}
}
func Lst(l ...Value) Value {
	if len(l) == 0 {
		return Value{flag: -'l'}
	}
	return Value{flag: -'l', ptr: unsafe.Pointer(&l)}
}
func Str(v string) (vs Value) { return Value{flag: -'s', ptr: unsafe.Pointer(&v)} }
func Fun(f *Func) Value       { return Value{flag: -'f', ptr: unsafe.Pointer(f)} }
func Num(v float64) Value     { return Value{flag: -'n', val: v} }
func _Vddd(l ...Value) Value  { return Value{flag: -'d', ptr: unsafe.Pointer(&l)} } // internal use
func _Vquote(v Value) Value   { return Value{flag: -'q', ptr: unsafe.Pointer(&v)} } // internal use

//go:nosplit
func (v *Value) _itfptr() *interface{} { return (*interface{})(unsafe.Pointer(v)) }
func (v Value) IsVoid() bool           { return v == Value{} }
func (v Value) IsTrue() bool           { return v.flag == -'b' && v.val == 1 }

// Type returns the type of Value: 'b'ool, 'n'umber, 'l'ist, 's'tring, 'f'unc, 'a'tom, 'i'nterface, 'v'oid
func (v Value) Type() byte {
	switch v.flag {
	case -'n', -'b', -'l', -'d', -'q', -'f', -'s', -'a':
		return byte(-v.flag)
	default:
		if v == (Value{}) {
			return 'v'
		}
		if v.flag > 0 {
			return 'i'
		}
	}
	panic("corrupted value")
}

func (v Value) String() string {
	switch vn, vs, vq, vl, vtype := v._value(); vtype {
	case 'q':
		return "'" + vq.String()
	case 'n':
		return strconv.FormatFloat(vn, 'f', -1, 64)
	case 's':
		return strconv.Quote(vs)
	case 'a':
		if line, col := v.Pos(); line > 0 {
			return vs + fmt.Sprintf(" /*%d:%d*/", line, col)
		}
		return vs
	case 'l', 'd':
		p := bytes.NewBufferString(ifstr(vtype == 'l', "(", "/*{*/ "))
		for _, e := range vl {
			p.WriteString(e.String())
			p.WriteString(" ")
		}
		for p.Len() > 0 && p.Bytes()[p.Len()-1] == ' ' {
			p.Truncate(p.Len() - 1)
		}
		p.WriteString(ifstr(vtype == 'l', ")", " /*}*/"))
		return p.String()
	default:
		switch v.Type() {
		case 'b':
			return strconv.FormatBool(v.val == 1)
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
	return fmt.Sprintf("{val:%v(%016x) ptr:%016x flag:%v}", v.val, math.Float64bits(v.val), v.ptr, v.flag)
}

func (v Value) Val() interface{} {
	switch vn, vs, _, _, vtype := v._value(); vtype {
	case 'n':
		return vn
	case 's':
		return vs
	case 'l', 'd':
		return v._flatten(false)
	}
	switch v.Type() {
	case 'b':
		return v.val == 1
	case 'i':
		return *v._itfptr()
	case 'f':
		return v.Fun()
	default:
		return v
	}
}

func (v Value) Rename(text string) Value {
	if v.Type() == 'a' {
		v.ptr = unsafe.Pointer(&text)
		return v
	}
	return Atm(text, 0, 0)
}

func (v Value) Equals(v2 Value) bool {
	if v == v2 {
		return true
	}
	if v.flag == v2.flag {
		if v.flag == -'a' || v.flag == -'s' {
			return *(*string)(v.ptr) == *(*string)(v2.ptr)
		}
		if v.flag > 0 {
			return *v._itfptr() == *v2._itfptr()
		}
	}
	return false
}

func (v Value) Fun() *Func      { return (*Func)(v.ptr) }
func (v Value) Bln() bool       { return v.val == 1 }
func (v Value) Num() float64    { return v.val }
func (v Value) Str() string     { return *(*string)(v.ptr) }
func (v Value) Pos() (int, int) { x := math.Float64bits(v.val); return int(x >> 32), int(x << 32 >> 32) }
func (v Value) Lst() []Value {
	if v.ptr == nil {
		return nil
	}
	return *(*[]Value)(v.ptr)
}

//go:nosplit
func (v Value) _at(i int) Value {
	hdr := (*reflect.SliceHeader)(v.ptr)
	return *(*Value)(unsafe.Pointer(hdr.Data + unsafe.Sizeof(v)*uintptr(i)))
}
func (v Value) _len() int {
	if v.ptr == nil {
		return 0
	}
	return (*reflect.SliceHeader)(v.ptr).Len
}
func (v Value) _value() (vn float64, vs string, vq Value, vl []Value, vtype byte) {
	switch v.flag {
	case -'n':
		vn, vtype = v.val, 'n'
	case -'l', -'d':
		vl, vtype = v.Lst(), byte(-v.flag)
	case -'q':
		vq, vtype = *(*Value)(v.ptr), 'q'
	case -'s', -'a':
		vs, vtype = *(*string)(v.ptr), byte(-v.flag)
	default:
		if v.IsVoid() {
			vtype = 'v'
		}
	}
	return
}

func (v Value) Flatten(inplace bool) Value {
	if v.Type() != 'l' {
		return v
	}
	return Lst(v._flatten(inplace)...)
}

func (v Value) _flatten(inplaceIfPossible bool) []Value {
	ex := 0
	for _, e := range v.Lst() {
		if x := e.Type(); x == 'd' || x == 'l' {
			ex += e._len() + 1
		}
	}
	if ex == 0 {
		if inplaceIfPossible {
			return v.Lst()
		}
		return append([]Value{}, v.Lst()...)
	}
	r := make([]Value, 0, ex+v._len())
	for _, e := range v.Lst() {
		switch e.Type() {
		case 'd':
			r = append(r, e._flatten(inplaceIfPossible)...)
		case 'l':
			r = append(r, Lst(e._flatten(inplaceIfPossible)...))
		default:
			r = append(r, e)
		}
	}
	return r
}
func (v Value) _atm() (string, bool) {
	if v.Type() == 'a' {
		return v.Str(), true
	}
	return "", false
}
