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
	"unsafe"
)

var (
	predefined  = Interpreter{Globals: &Map{}} // pre-defined functions go here
	Void, Empty = Value{}, VList()
)

type (
	Interpreter struct {
		assertable
		Globals *Map
	}
	Value struct {
		flag int            // interface{} 0
		ptr  unsafe.Pointer // interface{} 1
		val  float64
	}
	Func struct {
		macro bool
		// Used by Go builtin functions
		sig string
		f   func(*State)
		// Used by native functions
		n     Value
		nargs []string
		cls   *Map
	}
	State struct {
		*Map
		assertable
		It          *Interpreter
		Args        []Value
		Out, Caller Value
	}
	Map struct {
		parent *Map
		m      map[string]Value
	}
	execState struct {
		assertable
		callAtom     *Value
		local        *Map
		macro, quasi bool
		args         struct { // all go native calls share the same stack: args.list, each used region is identified by args.start
			start int
			list  *[]Value
		}
	}
	assertable struct {
		err error
	}
)

func New() *Interpreter {
	it := &Interpreter{}
	it.Globals = predefined.Globals.Copy()
	return it
}

func init() {
	predefined.Globals.Store("define", VFunc(&Func{sig: "(syntax·define var val)", f: func(*State) {}}))
	predefined.Globals.Store("set!", VFunc(&Func{sig: "(syntax·set! var val)", f: func(*State) {}}))
	predefined.Globals.Store("lambda", VFunc(&Func{sig: "(syntax·lambda paramlist body)", f: func(*State) {}}))
	predefined.Globals.Store("lambda#", VFunc(&Func{sig: "(syntax·lambda# paramlist body)", f: func(*State) {}}))
	predefined.Globals.Store("if", VFunc(&Func{sig: "(syntax·if cond true-branch false-branch ...)", f: func(*State) {}}))
	predefined.Globals.Store("quote", VFunc(&Func{sig: "(syntax·quote a)", f: func(*State) {}}))
	predefined.Globals.Store("unquote", VFunc(&Func{sig: "(syntax·unquote a)", f: func(*State) {}}))
	predefined.Globals.Store("quasiquote", VFunc(&Func{sig: "(syntax·quasiquote a)", f: func(*State) {}}))
	predefined.Globals.Store("true", VBool(true))
	predefined.Globals.Store("false", VBool(false))
	predefined.Globals.Store("#t", VBool(true))
	predefined.Globals.Store("#f", VBool(false))
	predefined.Install("#(begin ...)", func(s *State) { s.Out = begin(s.Caller, s.Args...) })
	predefined.Install("(rest-args)", func(s *State) {
		s.Out = Empty
		if v, ok := s.Map.m["\x00rest"]; ok {
			s.Out = v
		}
	})
	predefined.Install("#(and bool...)", func(s *State) {
		if len(s.Args) == 0 {
			s.Out = VAtom("true", 0, 0)
			return
		}
		var build func(lhs Value, args []Value) Value
		build = func(lhs Value, args []Value) Value {
			if len(args) == 0 {
				return lhs
			}
			if len(args) == 1 {
				return VList(s.Caller.DupAtom("if"), lhs, args[0], VAtom("false", 0, 0))
			}
			return VList(s.Caller.DupAtom("if"), lhs, build(args[0], args[1:]), VAtom("false", 0, 0))
		}
		s.Out = build(s.Args[0], s.Args[1:])
	})
	predefined.Install("#(or bool...)", func(s *State) {
		if len(s.Args) == 0 {
			s.Out = VAtom("false", 0, 0)
			return
		}
		var build func(lhs Value, args []Value) Value
		build = func(lhs Value, args []Value) Value {
			if len(args) == 0 {
				return lhs
			}
			if len(args) == 1 {
				return VList(s.Caller.DupAtom("if"), lhs, VAtom("true", 0, 0), args[0])
			}
			return VList(s.Caller.DupAtom("if"), lhs, VAtom("true", 0, 0), build(args[0], args[1:]))
		}
		s.Out = build(s.Args[0], s.Args[1:])
	})
	predefined.Install("(== a a...)", func(s *State) {
		for i, a := 1, s.In(0); i < len(s.Args); i++ {
			if !a.Equals(s.Args[i]) {
				s.Out = VBool(false)
				return
			}
		}
		s.Out = VBool(true)
	})
	predefined.Globals.Store("=", predefined.Globals.m["=="])
	predefined.Install("(!= a a)", func(s *State) { s.Out = VBool(!s.In(0).Equals(s.In(1))) })
	predefined.Globals.Store("<>", predefined.Globals.m["!="])
	predefined.Install("(< a a...)", func(s *State) {
		for i, _ := 1, s.In(0); i < len(s.Args); i++ {
			if !itfLess(s, s.Args[i-1], i) {
				s.Out = VBool(false)
				return
			}
		}
		s.Out = VBool(true)
	})
	predefined.Install("(<= a a...)", func(s *State) {
		for i, _ := 1, s.In(0); i < len(s.Args); i++ {
			if !itfLess(s, s.Args[i-1], i) && s.Args[i-1] != s.Args[i] {
				s.Out = VBool(false)
				return
			}
		}
		s.Out = VBool(true)
	})
	predefined.Install("#(> a a...)", func(s *State) {
		s.Out = VList(s.Caller.DupAtom("not"), VList(append([]Value{s.Caller.DupAtom("<=")}, s.Args...)...))
	})
	predefined.Install("#(>= a a...)", func(s *State) {
		s.Out = VList(s.Caller.DupAtom("not"), VList(append([]Value{s.Caller.DupAtom("<")}, s.Args...)...))
	})
	predefined.Install("(not bool)", func(s *State) { s.Out = VBool(!s.In(0).IsTrue()) })
	predefined.Install("(+ num_str num_str...)", func(s *State) {
		s.Out = s.In(0)
		switch vn, vs, _, vl, vtype := s.Out._value(); vtype {
		case 'n':
			for i := 1; i < len(s.Args); i++ {
				vn += s.InNumber(i)
			}
			s.Out = VNumber(vn)
		case 'l':
			for i := 1; i < len(s.Args); i++ {
				vl = []Value{_Vddd(vl...), _Vddd(s.InList(i)...)}
			}
			s.Out = VList(vl...)
		case 's':
			for i := 1; i < len(s.Args); i++ {
				vs += s.InString(i)
			}
			s.Out = VString(vs)
		default:
			panic(fmt.Errorf("can't apply 'add' on %v", s.Out))
		}
	})
	predefined.Install("(- number number...)", func(s *State) {
		a := s.InNumber(0)
		if len(s.Args) == 1 {
			a = -a
		}
		for i := 1; i < len(s.Args); i++ {
			a -= s.InNumber(i)
		}
		s.Out = VNumber(a)
	})
	predefined.Install("(* number number...)", func(s *State) {
		a := s.InNumber(0)
		for i := 1; i < len(s.Args); i++ {
			a *= s.InNumber(i)
		}
		s.Out = VNumber(a)
	})
	predefined.Install("(/ number number...)", func(s *State) {
		a := s.InNumber(0)
		for i := 1; i < len(s.Args); i++ {
			a /= s.InNumber(i)
		}
		s.Out = VNumber(a)
	})
	predefined.Install("#(let ((var1 val1) ... (varn valn)) expr...)", func(s *State) {
		names, values := []Value{}, []Value{}
		for _, pair := range s.InList(0) {
			p, _ := pair.Lst()
			s.assert(len(p) == 2 || s.panic("invalid binding list format: %v", pair))
			a, _ := p[0].Atm()
			s.assert(a != "" || s.panic("invalid binding list format: %v", pair))
			names, values = append(names, p[0]), append(values, p[1])
		}
		fn := VList(s.Caller.DupAtom("lambda"), VList(names...), begin(s.Caller, s.Args[1:]...))
		s.Out = VList(VList(fn, _Vddd(values...))._flatten()...) // call fn
	})
	predefined.Install("#(letrec ((var1 val1) ... (varn valn)) expr...)", func(s *State) {
		/* Unwrap to:
		(let ((var1 ()) ... (varn ())                  // outer binds
			(let ((var1_tmp val1) ... (varn_tmp valn)) // inner binds
				(set! 'var1 var1_tmp)                  // inner sets
				...
				(set! 'varn varb_tmp)
				expr...                                // expressions
		*/
		let, binds := s.Caller.DupAtom("let"), s.InList(0)
		innersets := make([]Value, len(binds))
		innerbinds := make([]Value, len(binds))
		outerbinds := make([]Value, len(binds))
		for i := range binds {
			b, _ := binds[i].Lst()
			s.assert(len(b) == 2 || s.panic("invalid binding list format: %v", binds[i]))
			a, _ := b[0].Atm()
			s.assert(a != "" || s.panic("invalid binding list format: %v", binds[i]))
			tmpvar := VAtom(a+"tmp", 0, 0)
			innersets[i] = VList(VAtom("set!", 0, 0), b[0], tmpvar)
			innerbinds[i] = VList(tmpvar, b[1])
			outerbinds[i] = VList(b[0], Void)
		}
		inner, _ := s.It.UnwrapMacro(VList(let, VList(innerbinds...), _Vddd(innersets...), _Vddd(s.Args[1:]...))._flatten())
		outer, _ := s.It.UnwrapMacro([]Value{let, VList(outerbinds...), inner})
		s.Out = outer
	})
	predefined.Install("(eval string)", func(s *State) { s.Out = errorOrValue(s.It.Run(s.InString(0))) })
	predefined.Install("(null? a)", func(s *State) { s.Out = VBool(IsEmpty(s.In(0))) })
	predefined.Install("(set-car! list value)", func(s *State) {
		_, ok := Head(s.InList(0), func(Value) Value { return s.In(1) })
		s.assert(ok || s.panic("set-car!: empty list"))
	})
	predefined.Install("(set-last! list value)", func(s *State) {
		_, ok := Last(s.InList(0), func(Value) Value { return s.In(1) })
		s.assert(ok || s.panic("set-last!: empty list"))
	})
	predefined.Install("(number text)", func(s *State) { s.Out = errorOrValue(strconv.ParseFloat(s.InString(0), 64)) })
	predefined.Install("(string a)", func(s *State) {
		if a, ok := s.In(0).Atm(); ok {
			s.Out = VString(a)
		} else {
			s.Out = VString(s.In(0).String())
		}
	})
	predefined.Install("(atom string)", func(s *State) { s.Out = VAtom(s.InString(0), 0, 0) })
	predefined.Install("(list v1 v2 ... vn)", func(s *State) { s.Out = VList(append([]Value{}, s.Args...)...) })
	predefined.Install("(append list list2)", func(s *State) { s.Out = VList(_Vddd(s.InList(0)...), _Vddd(s.InList(1)...)) })
	predefined.Install("(add list a)", func(s *State) { s.Out = VList(_Vddd(s.InList(0)...), s.In(1)) })
	predefined.Install("(cons a list)", func(s *State) { s.Out = VList(s.In(0), _Vddd(s.InList(1)...)) })
	predefined.Install("(car list)", func(s *State) {
		v, ok := Head(s.InList(0), nil)
		s.assert(ok || s.panic("car: empty list"))
		s.Out = v
	})
	predefined.Install("(cdr list)", func(s *State) {
		v, ok := Tail(s.InList(0))
		s.assert(ok || s.panic("cdr: empty list"))
		s.Out = VList(v...)
	})
	predefined.Install("(last list)", func(s *State) {
		v, ok := Last(s.InList(0), nil)
		s.assert(ok || s.panic("last: empty list"))
		s.Out = v
	})
	predefined.Install("(init list)", func(s *State) {
		v, ok := Init(s.InList(0))
		s.assert(ok || s.panic("init: empty list"))
		s.Out = VList(v...)
	})
	predefined.Install("(length list)", func(s *State) { s.Out = VNumber(float64(Length(s.InList(0)))) })
	predefined.Install("(raise a)", func(s *State) { panic(s.In(0)) })
	predefined.Install("(pcall handler function)", func(s *State) {
		defer func() {
			if r := recover(); r != nil {
				if _, ok := s.In(0).GoValue().(*Func); !ok {
					s.Out = Val(r)
				} else {
					s.Out = errorOrValue(s.InGoFunc(0)(Val(r)))
				}
			}
		}()
		s.Out = s.It.exec(VList(_Vquote(s.In(1))), execState{callAtom: &s.Out, local: s.Map})
	})
	predefined.Install("(apply function (list a1 a2 ... an))", func(s *State) {
		s.InList(1)
		v, err := s.InGoFunc(0)(s.In(1)._flatten()...)
		s.assert(err == nil || s.panic("apply panic: %v", err))
		s.Out = v
	})
	predefined.Install("(error text)", func(s *State) { s.Out = VInterface(errors.New(s.InString(0))) })
	predefined.Install("(error? a)", func(s *State) { _, ok := s.In(0).GoValue().(error); s.Out = VBool(ok) })
	predefined.Install("(void? a)", func(s *State) { s.Out = VBool(s.In(0).IsVoid()) })
	predefined.Install("(list? a)", func(s *State) { s.Out = VBool(s.In(0).Type() == 'l') })
	predefined.Install("(atom? a)", func(s *State) { s.Out = VBool(s.In(0).Type() == 'a') })
	predefined.Install("(bool? a)", func(s *State) { s.Out = VBool(s.In(0).Type() == 'b') })
	predefined.Install("(number? a)", func(s *State) { s.Out = VBool(s.In(0).Type() == 'n') })
	predefined.Install("(string? a)", func(s *State) { s.Out = VBool(s.In(0).Type() == 's') })
	predefined.Install("(quote? a)", func(s *State) { s.Out = VBool(s.In(0).Type() == 'q') })
	predefined.Install("(stringify a)", func(s *State) { s.Out = VString(s.In(0).String()) })
}

func (it *Interpreter) Install(name string, f func(*State)) *Func {
	fn := &Func{f: f, sig: strings.TrimSpace(name)}
	if strings.HasPrefix(fn.sig, "#") {
		fn.sig, fn.macro = fn.sig[1:], true
	}
	it.assert(strings.HasPrefix(fn.sig, "(") && strings.HasSuffix(fn.sig, ")") ||
		it.panic("expect function name format: \"(name ...)\" or \"#(name ...)\", not: %q", fn.sig))
	it.Globals.Store(fn.sig[1:strings.IndexAny(fn.sig, " )")], VFunc(fn))
	return fn
}

func (f *Func) Vararg() bool { return len(f.nargs) == 1 && strings.HasPrefix(f.nargs[0], "\x00") }

func (f *Func) String() string {
	if f.n.IsVoid() {
		return f.sig[1:strings.IndexAny(f.sig, " )")] + " /* " + f.sig + ifstr(f.macro, " ; builtin macro */", " */")
	}
	lm := ifstr(f.macro, "(lambda# (", "(lambda (")
	if f.Vararg() {
		return lm + f.nargs[0][1:] + " " + f.n.String() + ")"
	}
	return lm + strings.Join(f.nargs, " ") + ") " + f.n.String() + ")"
}

func (s *State) In(i int) Value {
	s.assert(i >= 0 && i < len(s.Args) || s.panic("too few arguments, expect at least %d", i+1))
	return s.Args[i]
}

func (s *State) InInterface(i int) interface{} {
	v, ok := s.In(i).Itf()
	s.assert(ok || s.panic("invalid argument #%d, expect interface{}, got %v", i, s.Args[i]))
	return v
}

func (s *State) InList(i int) []Value {
	vl, ok := s.In(i).Lst()
	s.assert(ok || s.panic("invalid argument #%d, expect list, got %v", i, s.Args[i]))
	return vl
}

func (s *State) InBool(i int) bool {
	v, ok := s.In(i).Bln()
	s.assert(ok || s.panic("invalid argument #%d, expect bool, got %v", i, s.Args[i]))
	return v
}

func (s *State) InNumber(i int) float64 {
	vn, ok := s.In(i).Num()
	s.assert(ok || s.panic("invalid argument #%d, expect number, got %v", i, s.Args[i]))
	return vn
}

func (s *State) InString(i int) string {
	vs, ok := s.In(i).Str()
	s.assert(ok || s.panic("invalid argument #%d, expect string, got %v", i, s.Args[i]))
	return vs
}

func (s *State) InAtom(i int, c ...string) string {
	v, ok := s.In(i).Atm()
	s.assert(ok || s.panic("invalid argument #%d, expect atom, got %v", i, s.Args[i]))
	for _, c := range c {
		if v == c {
			return v
		}
	}
	s.assert(len(c) == 0 || s.panic("invalid atom #%d, expect one of (%v), got %v", i, strings.Join(c, ", "), v))
	return v
}

func (s *State) InGoFunc(i int) func(...Value) (Value, error) {
	return func(a ...Value) (Value, error) {
		expr := make([]Value, len(a)+1)
		expr[0] = _Vquote(VFunc(s.InFunc(i)))
		for i := range a {
			expr[i+1] = _Vquote(a[i])
		}
		return s.It.Exec(VList(expr...), &Map{parent: s.Map})
	}
}

func (s *State) InFunc(i int) *Func {
	f, ok := s.In(i).Fun()
	s.assert(ok || s.panic("invalid argument #%d, expect closure, got %v", i, s.Args[i]))
	return f
}

func (m *Map) find(k string) (Value, *Map) {
	for ; m != nil; m = m.parent {
		if v, ok := m.m[k]; ok {
			return v, m
		}
	}
	return Void, nil
}

func (m *Map) set(k string, v Value) {
	if m.m == nil {
		m.m = make(map[string]Value, 4)
	}
	m.m[k] = v
}

func (m *Map) Store(k string, v Value) {
	if _, mv := m.find(k); mv == nil {
		m.set(k, v)
	} else {
		mv.set(k, v)
	}
}

func (m *Map) Load(k string) (Value, bool) {
	v, mv := m.find(k)
	return v, mv != nil
}

func (m *Map) Delete(k string) (Value, bool) {
	v, mv := m.find(k)
	if mv != nil {
		delete(mv.m, k)
	}
	return v, mv != nil
}

func (m *Map) Len() int { return len(m.m) }

func (m *Map) Unsafe() map[string]Value { return m.m }

func (m *Map) Copy() *Map {
	m2 := &Map{m: make(map[string]Value, len(m.m)), parent: m.parent}
	for k, v := range m.m {
		m2.m[k] = v
	}
	return m2
}

func (it *Interpreter) exec(expr Value, state execState) Value {
	if state.quasi {
		if expr.Type() == 'l' && expr._len() > 0 {
			if a, _ := expr._at(0).Atm(); a == "unquote" {
				state.assert(expr._len() == 2 || state.panic("invalid unquote syntax"))
				state.quasi = false
				v := it.exec(expr._at(1), state)
				state.quasi = true
				return v
			}
			e := make([]Value, expr._len())
			for i := range e {
				e[i] = it.exec(expr._at(i), state)
			}
			return VList(e...)
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
	switch va, _ := c._at(0).Atm(); va {
	case "if":
		state.assert(c._len() >= 3 || state.panic("invalid if syntax"))
		if it.exec(c._at(1), state).IsTrue() {
			expr = c._at(2) // execute true-branch
			goto TAIL_CALL
		}
		for i := 3; i < c._len(); i++ { // execute rest statements: (if cond true-branch false-branch1 ... false-branchn)
			if i == c._len()-1 {
				expr = c._at(i)
				goto TAIL_CALL
			}
			it.exec(c._at(i), state)
		}
		return Void
	case "lambda", "lambda#":
		state.assert(c._len() >= 3 || state.panic("invalid lambda syntax"))
		f := &Func{n: c._at(2), cls: state.local, macro: va == "lambda#"}
		if c._len() > 3 {
			f.n = begin(c._at(0), c._lst()[2:]...)
		}
		switch _, va, _, bindings, vtype := c._at(1)._value(); vtype {
		case 'a':
			f.nargs = []string{"\x00" + va}
		case 'l':
			for i, n := range bindings {
				va, ok := n.Atm()
				state.assert(ok || state.panic("invalid parameter %d, expect valid atom", i+1))
				f.nargs = append(f.nargs, va)
			}
		default:
			panic(fmt.Errorf("invalid binding list: %v", c._at(1)))
		}
		return VFunc(f)
	case "quote":
		state.assert(c._len() == 2 || state.panic("invalid quote syntax"))
		return c._at(1)
	case "quasiquote":
		state.assert(c._len() == 2 || state.panic("invalid quasiquote syntax"))
		state.quasi = true
		v := it.exec(c._at(1), state)
		state.quasi = false
		return v
	case "unquote":
		panic(fmt.Errorf("unquote outside quasiquote"))
	case "set!":
		state.assert(c._len() == 3 || state.panic("invalid set! syntax"))
		x, ok := c._at(1).Atm()
		state.assert(ok || state.panic("invalid set! syntax"))
		_, m := state.local.find(x)
		state.assert(m != nil || state.panic("set!: unbound %s", x))
		m.set(x, it.exec(c._at(2), state))
		return Void
	case "define":
		state.assert(c._len() == 3 || state.panic("invalid define syntax"))
		x, ok := c._at(1).Atm()
		state.assert(ok || state.panic("invalid define syntax"))
		_, ok = state.local.m[x]
		state.assert(!ok || state.panic("re-define %s", x))
		state.local.set(x, it.exec(c._at(2), state))
		return Void
	default:
		cc, ok := it.exec(c._at(0), state).Fun()
		state.assert(ok || state.panic("invalid function: %v", c._at(0)))
		state.assert(!cc.macro || state.macro || state.panic("mis-calling macro: %v", c._at(0)))

		if cc.f == nil {
			m := &Map{parent: cc.cls}
			if !cc.Vararg() {
				for i, name := range cc.nargs {
					state.assert(i+1 < c._len() || state.panic("too few arguments, expect at least %d", i+1))
					m.set(name, it.exec(c._at(i+1), state))
				}
				if c._len()-1 > len(cc.nargs) {
					values := make([]Value, 0, c._len())
					for i := len(cc.nargs) + 1; i < c._len(); i++ {
						values = append(values, it.exec(c._at(i), state))
					}
					m.set("\x00rest", VList(values...))
				}
			} else {
				values := make([]Value, 0, c._len())
				for i := 1; i < c._len(); i++ {
					values = append(values, it.exec(c._at(i), state))
				}
				m.set(cc.nargs[0][1:], VList(values...))
				m.set("\x00rest", VList(values...))
			}
			*state.callAtom = c._at(0)
			state.local, expr = m, cc.n
			goto TAIL_CALL
		}

		s := State{Map: state.local, It: it, Out: Void, Caller: c._at(0)}
		if state.args.list == nil {
			state.args.list = new([]Value)
		}

		args := state.args
		for i := 1; i < c._len(); i++ {
			state.args.start = len(*args.list)
			*args.list = append(*args.list, it.exec(c._at(i), state))
		}
		s.Args = (*args.list)[args.start:]
		*state.callAtom = c._at(0)
		cc.f(&s)
		*args.list = (*args.list)[:args.start]
		return s.Out
	}
}

func (it *Interpreter) parse(tmpl string) (Value, error) {
	var s scanner.Scanner
	var err error
	s.Init(strings.NewReader(tmpl))
	s.Mode &^= scanner.ScanChars | scanner.ScanRawStrings
	s.Error = func(s *scanner.Scanner, msg string) {
		pos := s.Position
		if !pos.IsValid() {
			pos = s.Pos()
		}
		err = fmt.Errorf("parse: %s at %d:%d", msg, pos.Line, pos.Column)
	}
	v, perr := it.scan(&s, false)
	if perr != nil {
		return Void, fmt.Errorf("parse: %v at %d:%d", perr, s.Pos().Line, s.Pos().Column)
	}
	return begin(Void, v._lst()...), err
}

func (it *Interpreter) Exec(c Value, local *Map) (Value, error) {
	return it.executeState(c, execState{local: local})
}

func (it *Interpreter) executeState(c Value, state execState) (result Value, err error) {
	var callAtom Value
	defer func() {
		if r := recover(); r != nil {
			if os.Getenv("ONE_STACK") != "" {
				log.Println(string(debug.Stack()))
			}
			err = fmt.Errorf("%v at %v", r, callAtom)
		}
	}()
	state.callAtom = &callAtom
	return it.exec(c, state), nil
}

func (it *Interpreter) Run(tmpl string) (result interface{}, err error) {
	c, err := it.parse(tmpl)
	if err != nil {
		return nil, err
	}
	return it.Exec(c, it.Globals)
}

func (it *Interpreter) scan(s *scanner.Scanner, scanOne bool) (Value, error) {
	var comp []Value
	for tok := s.Scan(); tok != scanner.EOF; tok = s.Scan() {
		// fmt.Println(s.TokenText())
		switch tok {
		case scanner.String, scanner.RawString:
			t, err := strconv.Unquote(s.TokenText())
			if err != nil {
				return Value{}, err
			}
			comp = append(comp, VString(t))
		case '#':
			if s.Peek() == '|' { // #| comment |#
				for s.Scan(); ; {
					if current, next := s.Scan(), s.Peek(); current == scanner.EOF {
						return Void, fmt.Errorf("incomplete comment block")
					} else if current == '|' && next == '#' {
						s.Scan()
						break
					}
				}
			} else {
				comp = append(comp, VAtom("#"+scanToDelim(s), uint32(s.Pos().Line), uint32(s.Pos().Column)))
			}
		case ';':
			for ; ; s.Scan() {
				if next := s.Peek(); next == scanner.EOF || next == '\n' {
					break
				}
			}
		case '(', '[':
			c, err := it.scan(s, false)
			if err != nil {
				return Value{}, err
			}
			comp = append(comp, c)
		case ')', ']':
			return it.UnwrapMacro(comp)
		case '\'', '`', ',':
			c, err := it.scan(s, true)
			if err != nil {
				return Void, err
			}
			if c.IsVoid() {
				return Void, fmt.Errorf("invalid *quote syntax")
			}
			comp = append(comp, VList(VAtom(ifstr(tok == '\'', "quote", ifstr(tok == '`', "quasiquote", "unquote")), 0, 0), c))
		default:
			text := s.TokenText() + scanToDelim(s)
			if v, ok := strconv.ParseFloat(text, 64); ok == nil || tok == scanner.Float || tok == scanner.Int {
				comp = append(comp, VNumber(v))
			} else {
				comp = append(comp, VAtom(text, uint32(s.Pos().Line), uint32(s.Pos().Column)))
			}
		}
		if scanOne && len(comp) >= 1 {
			return comp[0], nil
		}
	}
	return it.UnwrapMacro(comp)
}

func (it *Interpreter) UnwrapMacro(comp []Value) (Value, error) {
	if len(comp) == 0 {
		return VList(), nil
	}

	va, ok := comp[0].Atm()
	if !ok {
		return VList(comp...), nil
	}

	if (va == "define" || va == "define#") && len(comp) >= 3 && comp[1].Type() == 'l' {
		x := comp[1]._lst()
		if len(x) == 0 {
			return Void, fmt.Errorf("invalid binding list: %v", comp[1])
		}
		return VList(comp[0].DupAtom("define"), x[0],
			VList(append([]Value{comp[0].DupAtom(ifstr(va == "define#", "lambda#", "lambda")),
				VList(x[1:]...)}, comp[2:]...)...)), nil
	}

	m, _ := it.Globals.Load(va)
	if f, ok := m.Fun(); !(ok && f.macro) {
		return VList(comp...), nil
	}
	for i := 1; i < len(comp); i++ {
		comp[i] = _Vquote(comp[i])
	}
	v, err := it.executeState(VList(comp...), execState{local: it.Globals, macro: true})
	if err != nil {
		return Void, err
	}
	if v.Type() != 'l' {
		return v, nil
	}
	return VList(v._flatten()...), nil
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
		return vn < s.InNumber(i)
	case 's':
		return vs < s.InString(i)
	}
	panic(fmt.Errorf("argument #%d: %v and %v are not comparable", i, a, s.In(i)))
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
		return VInterface(err)
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
		} else if h, ok := Head(v[i]._lst(), setter); ok {
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
		} else if h, ok := Last(v[i]._lst(), setter); ok {
			return h, true
		}
	}
	return Void, false
}

func _range(idx int, v []Value, fn func(int, Value)) int {
	for _, el := range v {
		if el.Type() != 'd' {
			fn(idx, el)
			idx++
		} else {
			idx = _range(idx, el._lst(), fn)
		}
	}
	return idx
}

func Tail(v []Value) ([]Value, bool) {
	if len(v) == 0 {
		return nil, false
	}
	if d := v[0]; d.Type() == 'd' {
		t, ok := Tail(d._lst())
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
		t, ok := Init(d._lst())
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
			l += Length(v._lst())
		} else {
			l++
		}
	}
	return
}

func IsEmpty(v Value) bool {
	if v.Type() == 'l' {
		_, ok := Head(v._lst(), nil)
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
	return VList(append([]Value{lead.DupAtom("if"), Empty, Empty}, exprs...)...)
}

// zzzzzzzz

// Val creates Value from interface{}. uint64 and int64 will be stored as they were because float64 can't store them correctly
func Val(v interface{}) Value {
	switch v := v.(type) {
	case Value:
		return v
	case nil:
		return Empty
	case int:
		return VNumber(float64(v))
	case int8:
		return VNumber(float64(v))
	case int16:
		return VNumber(float64(v))
	case int32:
		return VNumber(float64(v))
	case uint:
		return VNumber(float64(v))
	case uint8:
		return VNumber(float64(v))
	case uint16:
		return VNumber(float64(v))
	case uint32:
		return VNumber(float64(v))
	case float32:
		return VNumber(float64(v))
	case float64:
		return VNumber(v)
	case string:
		return VString(v)
	case bool:
		return VBool(v)
	case []Value:
		return VList(v...)
	default:
		return VInterface(v)
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
		return VList(res...)
	case reflect.Map:
		if rv.Type().Key().Kind() == reflect.String { // map[string]any
			res, iter := &Map{m: make(map[string]Value, rv.Len())}, rv.MapRange()
			for iter.Next() {
				res.set(iter.Key().String(), ValRec(iter.Value().Interface()))
			}
			return VInterface(res)
		}
	}
	return Val(v)
}

func VBool(v bool) Value {
	if v {
		return Value{val: 1, flag: -'b'}
	}
	return Value{val: 0, flag: -'b'}
}

func VAtom(v string, line, col uint32) Value {
	return Value{flag: -'a', ptr: unsafe.Pointer(&v), val: math.Float64frombits(uint64(line)<<32 | uint64(col))}
}

func VString(v string) (vs Value)        { return Value{flag: -'s', ptr: unsafe.Pointer(&v)} }
func VList(l ...Value) Value             { return Value{flag: -'l', ptr: unsafe.Pointer(&l)} }
func VFunc(f *Func) Value                { return Value{flag: -'f', ptr: unsafe.Pointer(f)} }
func VNumber(v float64) Value            { return Value{flag: -'n', val: v} }
func VInterface(i interface{}) (v Value) { *v._itfptr() = i; return }
func _Vddd(l ...Value) Value             { return Value{flag: -'d', ptr: unsafe.Pointer(&l)} } // internal use
func _Vquote(v Value) Value              { return Value{flag: -'q', ptr: unsafe.Pointer(&v)} } // internal use

//go:nosplit
func (v *Value) _itfptr() *interface{} { return (*interface{})(unsafe.Pointer(v)) }
func (v Value) IsVoid() bool           { return v == Value{} }
func (v Value) IsTrue() bool           { return v.flag == -'b' && v.val == 1 }

//go:nosplit
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
	panic(fmt.Errorf("corrupted value: %x", v.GoString()))
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
		if line, col, _ := v.Pos(); line > 0 {
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
			i, _ := v.Itf()
			return "#" + fmt.Sprint(i)
		case 'f':
			return (*Func)(v.ptr).String()
		default:
			return "#void"
		}
	}
}

func (v Value) GoValue() interface{} {
	switch vn, vs, _, _, vtype := v._value(); vtype {
	case 'n':
		return vn
	case 's':
		return vs
	case 'l', 'd':
		return v._flatten() // TODO
	}
	switch v.Type() {
	case 'b':
		return v.val == 1
	case 'i':
		i, _ := v.Itf()
		return i
	case 'f':
		return (*Func)(v.ptr)
	default:
		return v
	}
}

func (v Value) DupAtom(text string) Value {
	if v.Type() == 'a' {
		v.ptr = unsafe.Pointer(&text)
		return v
	}
	return VAtom(text, 0, 0)
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

func (v Value) Itf() (interface{}, bool) {
	if v.flag < 0 {
		return nil, false
	}
	return *v._itfptr(), true
}

func (v Value) Fun() (*Func, bool) {
	if v.flag != -'f' {
		return nil, false
	}
	return (*Func)(v.ptr), true
}

func (v Value) Bln() (bool, bool)    { return v.val == 1, v.flag == -'b' }
func (v Value) Num() (float64, bool) { return v.val, v.flag == -'n' }

func (v Value) Str() (a string, ok bool) {
	if v.Type() == 's' {
		a, ok = *(*string)(v.ptr), true
	}
	return
}

func (v Value) Pos() (uint32, uint32, bool) {
	x := math.Float64bits(v.val)
	return uint32(x >> 32), uint32(x), v.flag == -'a'
}

func (v Value) Atm() (a string, ok bool) {
	if v.Type() == 'a' {
		a, ok = *(*string)(v.ptr), true
	}
	return
}

func (v Value) Lst() ([]Value, bool) {
	if v.flag != -'l' {
		return nil, false
	}
	return v._lst(), true
}

//go:nosplit
func (v Value) _at(i int) Value {
	hdr := (*reflect.SliceHeader)(v.ptr)
	return *(*Value)(unsafe.Pointer(hdr.Data + unsafe.Sizeof(v)*uintptr(i)))
}
func (v Value) _len() int     { return (*reflect.SliceHeader)(v.ptr).Len }
func (v Value) _lst() []Value { return *(*[]Value)(v.ptr) }
func (v Value) _value() (vn float64, vs string, vq Value, vl []Value, vtype byte) {
	switch v.flag {
	case -'n':
		vn, vtype = v.val, 'n'
	case -'l', -'d':
		vl, vtype = v._lst(), byte(-v.flag)
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
func (v Value) _flatten() []Value {
	ex := 0
	for _, e := range v._lst() {
		if x := e.Type(); x == 'd' || x == 'l' {
			ex += e._len() + 1
		}
	}
	if ex == 0 {
		return append([]Value{}, v._lst()...)
	}
	r := make([]Value, 0, ex+v._len())
	for _, e := range v._lst() {
		switch e.Type() {
		case 'd':
			r = append(r, e._flatten()...)
		case 'l':
			r = append(r, VList(e._flatten()...))
		default:
			r = append(r, e)
		}
	}
	return r
}

func (v Value) GoString() string {
	return fmt.Sprintf("{val:%v(%016x) ptr:%016x flag:%v}", v.val, math.Float64bits(v.val), v.ptr, v.flag)
}
