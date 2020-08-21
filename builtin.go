package sc45

import (
	"bytes"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io"
	"io/ioutil"
	"os"
	"reflect"
	"strconv"
	"strings"
	"unsafe"
)

var DefaultStdout io.Writer = os.Stdout
var stateType = reflect.TypeOf(&State{})

func (s *State) InMap() map[string]Value {
	v, _ := s.PopArgAs(INTF).V().(map[string]Value)
	return v
}

func (ctx *Context) String() string {
	p := bytes.NewBufferString("{")
	for k, v := range ctx.M {
		p.WriteString(strconv.Quote(k))
		p.WriteString(":")
		p.WriteString(v.String())
		p.WriteString(" ")
	}
	if p.Bytes()[p.Len()-1] == ' ' {
		p.Truncate(p.Len() - 1)
	}
	p.WriteString("}")
	if ctx.parent != nil {
		p.WriteString(" -> ")
		p.WriteString(ctx.parent.String())
	}
	return p.String()
}

func NewGoFunc(fn interface{}) Value {
	var ctx assertable
	rf, rt := reflect.ValueOf(fn), reflect.TypeOf(fn)
	ctx.assert(rf.Kind() == reflect.Func || ctx.panic("not func"))
	ctx.assert(rt.NumOut() <= 2 || ctx.panic("too many return values, expect 0, 1 or 2"))
	ctx.assert(rt.NumOut() < 2 || (rt.Out(1).Implements(reflect.TypeOf((*error)(nil)).Elem())) || ctx.panic("require func (...) (*, error)"))
	count := rt.NumIn()
	if rt.IsVariadic() {
		count = Vararg | (count - 1)
	}
	if count > 0 && rt.In(0) == stateType {
		count--
	}
	return NewFunc(count, func(s *State) {
		ins := make([]reflect.Value, 0, rt.NumIn())
		if rt.IsVariadic() {
			for i := 0; i < rt.NumIn()-1; i++ {
				if t := rt.In(i); i == 0 && t == stateType {
					ins = append(ins, reflect.ValueOf(s))
				} else {
					ins = append(ins, s.PopArg().TypedVal(t))
				}
			}
			for !s.Args.ProEmpty() {
				ins = append(ins, s.PopArg().TypedVal(rt.In(rt.NumIn()-1).Elem()))
			}
		} else {
			for i := 0; i < rt.NumIn(); i++ {
				if t := rt.In(i); i == 0 && t == stateType {
					ins = append(ins, reflect.ValueOf(s))
				} else {
					ins = append(ins, s.PopArg().TypedVal(t))
				}
			}
		}
		outs := rf.Call(ins)
		switch rt.NumOut() {
		case 1:
			s.Out = V(outs[0].Interface())
		case 2:
			if err, _ := outs[1].Interface().(error); err != nil {
				s.Out = V(err)
			} else {
				s.Out = V(outs[0].Interface())
			}
		}
	})
}

func _Ft(t ValueType) Value { return NewFunc(1, func(s *State) { s.Out = B(s.PopArg().Type() == t) }) }

func init() {
	Default.Store("true", B(true)).Store("false", B(false)).Store("begin", NewFunc(Macro|Vararg, func(s *State) {
		s.Out = L(s.Args, s.Caller.Y("if"), Void, Void)
	})).Store("and", NewFunc(Macro|Vararg, func(s *State) {
		if s.Args.ProEmpty() {
			s.Out = B(true)
		} else if !s.Args.HasProNext() {
			s.Out = s.PopArg()
		} else {
			s.Out = L(Empty, s.Caller.Y("if"), s.PopArg(), L(s.Args, s.Caller.Y("and")), B(false))
		}
	})).Store("or", NewFunc(Macro|Vararg, func(s *State) {
		if s.Args.ProEmpty() {
			s.Out = B(false)
		} else if !s.Args.HasProNext() {
			s.Out = s.PopArg()
		} else {
			s.Out = L(Empty, s.Caller.Y("if"), s.PopArg(), B(true), L(s.Args, s.Caller.Y("or")))
		}
	})).Store("==", NewFunc(1|Vararg, func(s *State) {
		flag := true
		for last := s.PopArg(); flag && !s.Args.ProEmpty(); last = s.LastIn {
			flag = last.Equals(s.PopArg())
		}
		s.Out = B(flag)
	})).Store("=", Default.M["=="]).Store("!=", NewFunc(1|Vararg, func(s *State) {
		s.Out = B(!s.PopArg().Equals(s.PopArg()))
	})).Store("<>", Default.M["!="]).Store("<", NewFunc(1|Vararg, func(s *State) {
		flag := true
		for last := s.PopArgAs('n'); flag && !s.Args.ProEmpty(); last = s.LastIn {
			flag = last.Less(s.PopArgAs('n'), false)
		}
		s.Out = B(flag)
	})).Store("<=", NewFunc(1|Vararg, func(s *State) {
		flag := true
		for last := s.PopArgAs('n'); flag && !s.Args.ProEmpty(); last = s.LastIn {
			flag = last.Less(s.PopArgAs('n'), true)
		}
		s.Out = B(flag)
	})).Store(">", NewFunc(1|Vararg, func(s *State) {
		flag := true
		for last := s.PopArgAs('n'); flag && !s.Args.ProEmpty(); last = s.LastIn {
			flag = !last.Less(s.PopArgAs('n'), true)
		}
		s.Out = B(flag)
	})).Store(">=", NewFunc(1|Vararg|Macro, func(s *State) {
		s.Out = L(Empty, s.Caller.Y("not"), L(s.Args, s.Caller.Y("<")))
	})).Store("not", NewFunc(1, func(s *State) {
		s.Out = B(s.PopArg().IsFalse())
	})).Store("+", NewFunc(1|Vararg, func(s *State) {
		switch s.Out = s.PopArg(); s.Out.Type() {
		case NUM:
			for !s.Args.ProEmpty() {
				s.Out = s.Out.Add(s.PopArgAs('n'))
			}
		case STR:
			vs := s.Out.S()
			for !s.Args.ProEmpty() {
				vs += s.PopArgAs(STR).S()
			}
			s.Out = S(vs)
		default:
			panic(fmt.Errorf("can't apply 'add' on %v", s.Out))
		}
	})).Store("-", NewFunc(1|Vararg, func(s *State) {
		a := s.PopArgAs('n')
		if s.Args.ProEmpty() {
			af, ai, aIsInt := a.N()
			if aIsInt {
				s.Out = I(-ai)
			} else {
				s.Out = N(-af)
			}
			return
		}
		for !s.Args.ProEmpty() {
			a = a.Sub(s.PopArgAs('n'))
		}
		s.Out = a
	})).Store("*", NewFunc(1|Vararg, func(s *State) {
		s.Out = s.PopArgAs('n')
		for !s.Args.ProEmpty() {
			s.Out = s.Out.Mul(s.PopArgAs('n'))
		}
	})).Store("/", NewFunc(1|Vararg, func(s *State) {
		s.Out = s.PopArgAs('n')
		for !s.Args.ProEmpty() {
			s.Out = s.Out.Div(s.PopArgAs('n'), false)
		}
	})).Store("idiv", NewFunc(1|Vararg, func(s *State) {
		s.Out = s.PopArgAs('n')
		for !s.Args.ProEmpty() {
			s.Out = s.Out.Div(s.PopArgAs('n'), true)
		}
	})).Store("let", NewFunc(1|Vararg|Macro, func(s *State) {
		var names, values []Value
		s.PopArgAs(LIST).L().ProRange(func(pair Value) bool {
			s.assert(pair.Type() == LIST || s.panic("invalid binding list format: %v", pair))
			p := pair.L()
			s.assert(p.HasProNext() && p.Val().Type() == SYM && p.Val().S() != "" || s.panic("invalid binding list format: %v", pair))
			names, values = append(names, p.Val()), append(values, p.Next().Val())
			return true
		})
		fn := L(Empty, s.Caller.Y("lambda"), L(Empty, names...), L(s.Args, s.Caller.Y("if"), Void, Void))
		s.Out = L(L(Empty, values...).L(), fn)
	})).Store("eval", NewFunc(1, func(s *State) {
		s.Out = __exec(s.PopArg(), execState{local: s.Context, debug: s.Stack})
	})).Store("parse", NewFunc(1, func(s *State) {
		x := s.PopArgAs(STR).S()
		if _, err := os.Stat(x); err == nil {
			buf, err := ioutil.ReadFile(x)
			if err != nil {
				s.Out = V(err)
			} else {
				s.Out = ev2(s.Context.Parse(x, *(*string)(unsafe.Pointer(&buf))))
			}
		} else {
			s.Out = ev2(s.Context.Parse("(parse)", x))
		}
	})).Store("set-car!", NewFunc(2, func(s *State) {
		l := s.PopArgAs(LIST).L()
		s.assert(!l.ProEmpty() || s.panic("set-car!: empty list"))
		l.setVal(s.PopArg())
	})).Store("set-cdr!", NewFunc(2, func(s *State) {
		s.Out = L(s.PopArgAs(LIST).L().SetCdr(s.PopArg()))
	})).Store("list", NewFunc(Vararg, func(s *State) {
		s.Out = L(s.Args)
	})).Store("append", NewFunc(2, func(s *State) {
		s.Out = L(s.PopArgAs(LIST).L().ProAppend(s.PopArgAs(LIST).L()))
	})).Store("cons", NewFunc(2, func(s *State) {
		s.Out = L(Cons(s.PopArg(), s.PopArg()))
	})).Store("car", NewFunc(1, func(s *State) {
		s.Out = s.PopArgAs(LIST).L().Car()
	})).Store("cdr", NewFunc(1, func(s *State) {
		s.Out = s.PopArgAs(LIST).L().Cdr()
	})).Store("last", NewFunc(1, func(s *State) {
		l := s.PopArgAs(LIST).L()
		s.assert(!l.ProEmpty() || s.panic("last: empty list"))
		s.Out = l.Last().Val()
	})).Store("init", NewFunc(1, func(s *State) {
		l := s.PopArgAs(LIST).L()
		s.assert(!l.ProEmpty() || s.panic("init: empty list"))
		s.Out = L(l.ProTake(-1))
	})).Store("length", NewFunc(1, func(s *State) {
		s.Out = I(int64(s.PopArgAs(LIST).L().ProLen()))
	})).Store("pcall", NewFunc(2, func(s *State) {
		rc, old := s.PopArg(), s.Stack.Frames
		defer func() {
			if r := recover(); r != nil {
				if rc.Type() != FUNC {
					s.Out = V(r)
				} else {
					s.Out = ev2(rc.F().Call(s.Stack, V(r)))
				}
				s.Stack.Frames = old
			}
		}()
		s.Out = __exec(L(Empty, s.PopArg().Quote()), execState{debug: s.Stack, local: s.Context})
	})).Store("apply", NewFunc(2, func(s *State) {
		expr := InitListBuilder().Append(s.PopArgAs(FUNC).Quote())
		s.PopArgAs(LIST).L().ProRange(func(v Value) bool { expr = expr.Append(v.Quote()); return true })
		v, err := (*Context)(nil).Exec(expr.Build())
		s.assert(err == nil || s.panic("apply panic: %v", err))
		s.Out = v
	})).
		Store("raise", NewFunc(1, func(s *State) { panic(s.PopArg()) })).
		Store("symbol->string", NewFunc(1, func(s *State) { s.Out = S(s.PopArgAs(SYM).S()) })).
		Store("number->string", NewFunc(1, func(s *State) { s.Out = S(fmt.Sprint(s.PopArgAs('n').V())) })).
		Store("string->symbol", NewFunc(1, func(s *State) { s.Out = Y(s.PopArgAs(STR).S(), 0) })).
		Store("string->error", NewFunc(1, func(s *State) { s.Out = V(fmt.Errorf(s.PopArgAs(STR).S())) })).
		Store("error?", NewFunc(1, func(s *State) { _, ok := s.PopArg().V().(error); s.Out = B(ok) })).
		Store("null?", NewFunc(1, func(s *State) { s.Out = B(s.PopArg().Type() == LIST && s.LastIn.L().ProEmpty()) })).
		Store("list?", NewFunc(1, func(s *State) { s.Out = B(s.PopArg().Type() == LIST && s.LastIn.L().IsProperList()) })).
		Store("void?", NewFunc(1, func(s *State) { s.Out = B(s.PopArg() == Void) })).Store("pair?", _Ft(LIST)).Store("symbol?", _Ft(SYM)).Store("boolean?", _Ft('b')).Store("number?", _Ft('n')).Store("string?", _Ft(STR)).
		Store("string->number", NewFunc(1, func(s *State) {
			x := s.PopArgAs(STR).S()
			if v, err := strconv.ParseInt(x, 0, 64); err == nil {
				s.Out = I(v)
			} else {
				s.Out = ev2(strconv.ParseFloat(x, 64))
			}
		})).
		Store("stringify", NewFunc(1, func(s *State) { s.Out = S(s.PopArg().String()) }))
	Default.Store("letrec", NewFunc(1|Vararg|Macro, func(s *State) {
		/* Unwrap to:
		(let ((var1 ()) ... (varn ())                  // outer binds
			(let ((var1_tmp val1) ... (varn_tmp valn)) // inner binds
				(set! 'var1 var1_tmp)                  // inner sets
				...
				(set! 'varn varb_tmp)
				expr...                                // expressions
		*/
		let, setq := s.Caller.Y("let"), s.Caller.Y("set!")
		var innersets, innerbinds, outerbinds []Value
		s.PopArgAs(LIST).L().ProRange(func(v Value) bool {
			s.assert(v.Type() == LIST || s.panic("invalid binding list format: %v", v))
			b := v.L()
			s.assert(b.HasProNext() && b.Val().Type() == SYM && b.Val().S() != "" || s.panic("invalid binding list format: %v", v))
			tmpvar := Y(b.Val().S()+"tmp", 0)
			innersets = append(innersets, L(Empty, setq, b.Val(), tmpvar))
			innerbinds = append(innerbinds, L(Empty, tmpvar, b.Next().Val()))
			outerbinds = append(outerbinds, L(Empty, b.Val(), Void))
			return true
		})
		inner := L(L(s.Args, innersets...).L(), let, L(Empty, innerbinds...))
		outer := []Value{let, L(Empty, outerbinds...), inner}
		s.Out = L(Empty, outer...)
	}))
	Default.Store("let*", NewFunc(1|Vararg|Macro, func(s *State) {
		/* Unwrap to:
		(let ((var1 val1)
			(let ((var2 val2))
				...
					expr...
		*/
		let, binds := s.Caller.Y("let"), s.PopArgAs(LIST).L().ProSlice()
		last := L(s.Args, s.Caller.Y("begin"))
		for i := len(binds) - 1; i >= 0; i-- {
			bd := binds[i]
			s.assert(bd.Type() == LIST || s.panic("invalid binding list format: %v", bd))
			lst := bd.L()
			s.assert(lst.HasProNext() && lst.Val().Type() == SYM && lst.Val().S() != "" || s.panic("invalid binding list format: %v", bd))
			last = L(Empty, let, L(Empty, bd), last)
		}
		s.Out = last
	}))
	Default.Store("define-modules", NewFunc(1|Vararg, func(s *State) {
	}))

	Default.Store("go->value", NewFunc(1, func(s *State) {
		rv := reflect.ValueOf(s.PopArg().V())
		switch rv.Kind() {
		case reflect.Slice, reflect.Array:
			l := InitListBuilder()
			for i := 0; i < rv.Len(); i++ {
				l = l.Append(V(rv.Index(i).Interface()))
			}
			s.Out = l.Build()
		default:
			s.Out = s.LastIn
		}
	}))
	Default.Store("hash-new", NewFunc(Vararg, func(s *State) {
		m := map[string]Value{}
		for !s.Args.ProEmpty() {
			m[s.PopArgAs(STR).S()] = s.PopArg()
		}
		s.Out = V(m)
	}))
	Default.Store("hash-set!", NewFunc(3, func(s *State) { s.InMap()[s.PopArgAs(STR).S()] = s.PopArg() }))
	Default.Store("hash-delete!", NewFunc(2, func(s *State) { delete(s.InMap(), s.PopArgAs(STR).S()) }))
	Default.Store("hash-get", NewFunc(2, func(s *State) { s.Out = s.InMap()[s.PopArgAs(STR).S()] }))
	Default.Store("hash-contains?", NewFunc(2, func(s *State) { _, ok := s.InMap()[s.PopArgAs(STR).S()]; s.Out = B(ok) }))
	Default.Store("hash-keys", NewFunc(1, func(s *State) {
		ret := InitListBuilder()
		for i := range s.InMap() {
			ret = ret.Append(S(i))
		}
		s.Out = ret.Build()
	}))

	Default.Store("string-length", NewFunc(1, func(s *State) { s.Out = I(int64(len(s.PopArgAs(STR).S()))) }))
	Default.Store("substring?", NewFunc(2, func(s *State) { s.Out = B(strings.Contains(s.PopArgAs(STR).S(), s.PopArgAs(STR).S())) }))
	// 	Default.Install("skip", 2, func(s *State) {
	// 		l := s.In(1, LIST).L()
	// 		for i := 0; i < int(s.In(0, 'n').N()); i++ {
	// 			l, _ = Tail(l)
	// 		}
	// 		s.Out = L(l...)
	// 	})
	// 	Default.Install("lambda*", 2|Vararg|Macro, func(s *State) {
	// 		tmpvar := "a" + strconv.FormatInt(time.Now().Unix(), 10)
	// 		pl, body := s.In(0, LIST).L(), []Value{
	// 			s.Caller.Y("lambda"),
	// 			s.Caller.Make(tmpvar),
	// 			L(s.Caller.Y("define"), s.Caller.Make(tmpvar+"-len"), L(
	// 				s.Caller.Y("vector-len"), s.Caller.Make(tmpvar),
	// 			)),
	// 		}
	// 		/*
	// 			(lambda* (a0 a1 ... an) body) =>
	// 			(lambda axxx (begin
	// 				(define axxx-len (vector-len args))
	// 				(define a0 (if (< 0 axxx-len) (vector-nth args 0) a0-expr))
	// 				...
	// 				(define an (if (< n axxx-len) (vector-nth args n) an-expr))
	// 				body
	// 		*/
	// 		for i := range pl {
	// 			var name, val Value
	// 			if pl[i].Type() == SYM {
	// 				name, val = pl[i], ProEmpty
	// 				if a := pl[i].S(); strings.HasSuffix(a, "...") {
	// 					// Special case: "name..." to catch the rest arguments
	// 					body = Append(body, L(
	// 						s.Caller.Y("define"),
	// 						s.Caller.Make(ifstr(len(a) == 3, "...", a[:len(a)-3])),
	// 						L(s.Caller.Y("skip"), N(float64(i)), s.Caller.Make(tmpvar)),
	// 					))
	// 					continue
	// 				}
	// 			} else {
	// 				s.assert(pl[i].Type() == LIST && pl[i]._len() == 2 || s.panic("invalid binding list: %v", pl[i]))
	// 				name, val = pl[i]._at(0), pl[i]._at(1)
	// 			}
	// 			body = Append(body, L(
	// 				s.Caller.Y("define"),
	// 				name,
	// 				L(
	// 					s.Caller.Y("if"),
	// 					L(s.Caller.Y("<"), N(float64(i)), s.Caller.Make(tmpvar+"-len")),
	// 					L(s.Caller.Y("vector-nth"), s.Caller.Make(tmpvar), N(float64(i))),
	// 					val,
	// 				),
	// 			))
	// 		}
	// 		body = Append(body, s.Args[1:]...)
	// 		s.Out = L(body...)
	// 	})
	Default.Store("vector-bytes", NewFunc(1, func(s *State) { s.Out = V(make([]byte, s.PopArgAs('n').I())) }))
	Default.Store("vector-strings", NewFunc(1, func(s *State) { s.Out = V(make([]string, s.PopArgAs('n').I())) }))
	Default.Store("vector-ints", NewFunc(1, func(s *State) { s.Out = V(make([]int, s.PopArgAs('n').I())) }))
	Default.Store("vector-int64s", NewFunc(1, func(s *State) { s.Out = V(make([]int64, s.PopArgAs('n').I())) }))
	Default.Store("vector-len", NewFunc(1, func(s *State) { s.Out = I(int64((reflect.ValueOf(s.PopArg().V()).Len()))) }))
	Default.Store("vector-null?", NewFunc(1, func(s *State) { s.Out = B(reflect.ValueOf(s.PopArg().V()).Len() == 0) }))
	Default.Store("vector-nth", NewFunc(2, func(s *State) {
		rm := reflect.ValueOf(s.PopArg().V())
		s.Out = V(rm.Index(int(s.PopArgAs('n').I())).Interface())
	}))
	Default.Store("vector-set-nth!", NewFunc(3, func(s *State) {
		rm := reflect.ValueOf(s.PopArg().V())
		rm.Index(int(s.PopArgAs('n').I())).Set(s.PopArg().TypedVal(rm.Type().Elem()))
	}))
	Default.Store("vector-slice", NewFunc(3, func(s *State) {
		rl := reflect.ValueOf(s.PopArg().V())
		start, end := int(s.PopArgAs('n').I()), int(s.PopArgAs('n').I())
		s.Out = V(rl.Slice(start, end).Interface())
	}))
	Default.Store("vector-concat", NewFunc(2, func(s *State) {
		rv1, rv2 := reflect.ValueOf(s.PopArg().V()), reflect.ValueOf(s.PopArg().V())
		s.assert(rv1.Type() == rv2.Type() || s.panic("vector-concat: different type"))
		r := reflect.MakeSlice(rv1.Type(), rv1.Len(), rv1.Len()+rv2.Len())
		reflect.Copy(r, rv1)
		reflect.AppendSlice(r, rv2)
		s.Out = V(r.Interface())
	}))
	Default.Store("vector-foreach", NewFunc(2, func(s *State) {
		rl, fn := reflect.ValueOf(s.PopArg().V()), s.PopArgAs(FUNC)
		for i := 0; i < rl.Len(); i++ {
			flag, err := fn.F().Call(s.Stack, I(int64(i)), V(rl.Index(i).Interface()))
			s.assert(err == nil || s.panic("invalid callback "))
			if flag.IsFalse() {
				break
			}
		}
	}))
	Default.Store("map", NewFunc(2, func(s *State) {
		fn, r, l, i := s.PopArgAs(FUNC), []Value{}, s.PopArgAs(LIST).L(), 0
		l.ProRange(func(h Value) bool {
			v, err := fn.F().Call(s.Stack, h)
			s.assert(err == nil || s.panic("map: error at element #%d: %v", i, err))
			r = append(r, v)
			i++
			return true
		})
		s.Out = L(Empty, r...)
	}))
	Default.Store("reduce", NewFunc(3, func(s *State) {
		fn, left, l, i := s.PopArgAs(FUNC), s.PopArg(), s.PopArgAs(LIST).L(), 0
		var err error
		l.ProRange(func(h Value) bool {
			left, err = fn.F().Call(s.Stack, left, h)
			s.assert(err == nil || s.panic("reduce: error at element #%d: %v", i, err))
			i++
			return true
		})
		s.Out = left
	}))
	Default.Store("reduce-right", NewFunc(3, func(s *State) {
		fn, right, rl := s.PopArgAs(FUNC), s.PopArg(), s.PopArgAs(LIST).L().ProSlice()
		var err error
		for i := len(rl) - 1; i >= 0; i-- {
			right, err = fn.F().Call(s.Stack, right, rl[i])
			s.assert(err == nil || s.panic("reduce-right: error at element #%d: %v", i, err))
		}
		s.Out = right
	}))
	// 	// 	Default.Install("(eq any any...)", func(s *State) {
	// 	// 		s.Out = true
	// 	// 		for i, a := 1, s.In(0, 0); i < len(s.Args); i++ {
	// 	// 			s.Out = s.Out.(bool) && reflect.DeepEqual(a, s.Args[i])
	// 	// 		}
	// 	// 	})
	Default.Store("struct-get", NewFunc(1|Vararg, func(s *State) {
		rv := reflect.ValueOf(s.PopArg().V())
		s.Args.ProRange(func(v Value) bool {
			if rv.Kind() == reflect.Ptr {
				rv = rv.Elem()
			}
			s.assert(v.Type() == SYM || s.panic("expect field name to be symbol: %v", v))
			rv = rv.FieldByName(v.S())
			return true
		})
		s.Out = V(rv.Interface())
	}))
	Default.Store("struct-set!", NewFunc(2|Vararg, func(s *State) {
		rv := reflect.ValueOf(s.PopArg().V())
		v := s.PopArg()
		s.Args.ProRange(func(v Value) bool {
			if rv.Kind() == reflect.Ptr {
				rv = rv.Elem()
			}
			s.assert(v.Type() == SYM || s.panic("expect field name to be symbol: %v", v))
			rv = rv.FieldByName(v.S())
			return true
		})
		rv.Set(reflect.ValueOf(v.V()))
	}))
	Default.Store("^", NewFunc(Vararg, func(s *State) {
		p := bytes.Buffer{}
		s.Args.ProRange(func(v Value) bool { p.WriteString(v.S()); return true })
		s.Out = S(p.String())
	}))
	Default.Store("display", NewFunc(Vararg, func(s *State) { fmt.Fprintln(DefaultStdout, L(s.Args).V().([]interface{})...) }))
	Default.Store("newline", NewFunc(0, func(s *State) { fmt.Fprintln(DefaultStdout) }))
	// Default.Store("printf",NewFunc( 1|Vararg, func(s *State) { fmt.Fprintf(DefaultStdout, s.In(0, 's').S(), vlisttointerface(s.Args[1:])...) }))
	// 	Default.Install("regex/match", 2, func(s *State) {
	// 		s.Out = B(regexp.MustCompile(s.In(0, 's').S()).MatchString(s.In(1, 's').S()))
	// 	})
	// 	Default.Install("regex/find", 3, func(s *State) {
	// 		s.Out = ValRec(regexp.MustCompile(s.In(0, 's').S()).FindAllStringSubmatch(s.In(1, 's').S(), int(s.In(2, 'n').N())))
	// 	})
	Default.Store("json", NewFunc(1, func(s *State) {
		buf, err := json.MarshalIndent(s.PopArg().V(), "", "  ")
		s.Out = ev2(string(buf), err)
	}))
	Default.Store("json-c", NewFunc(1, func(s *State) {
		buf, err := json.Marshal(s.PopArg().V())
		s.Out = ev2(string(buf), err)
	}))
	Default.Store("json-parse", NewFunc(1, func(s *State) {
		text := strings.TrimSpace(s.PopArgAs(STR).S())
		if strings.HasPrefix(text, "{") {
			m := map[string]interface{}{}
			if err := json.Unmarshal([]byte(text), &m); err != nil {
				s.Out = V(err)
			} else {
				s.Out = V(m)
			}
		} else if strings.HasPrefix(text, "[") {
			m := []interface{}{}
			if err := json.Unmarshal([]byte(text), &m); err != nil {
				s.Out = V(err)
			} else {
				s.Out = V(m)
			}
		} else {
			var m interface{}
			if err := json.Unmarshal([]byte(text), &m); err != nil {
				s.Out = V(err)
			} else {
				s.Out = V(m)
			}
		}
	}))
	Default.Store("setf!", NewFunc(2|Macro, func(s *State) {
		a, v := s.PopArgAs(SYM).S(), s.PopArg()
		parts := strings.Split(a, ".")
		s.assert(len(parts) > 1 || s.panic("too few fields to set"))
		structname := parts[0]
		setter := InitListBuilder().Append(v.Y("struct-set!")).Append(v.Y(structname)).Append(v)
		for i := 1; i < len(parts); i++ {
			setter = setter.Append(v.Y(parts[i]).Quote())
		}
		s.Out = setter.Build()
	}))
	Default.Store("getf", NewFunc(1|Macro, func(s *State) {
		a := s.PopArgAs(SYM).S()
		parts := strings.Split(a, ".")
		s.assert(len(parts) > 1 || s.panic("too few fields to get"))
		structname := parts[0]
		setter := InitListBuilder().Append(s.Caller.Y("struct-get")).Append(s.Caller.Y(structname))
		for i := 1; i < len(parts); i++ {
			setter = setter.Append(s.Caller.Y(parts[i]).Quote())
		}
		s.Out = setter.Build()
	}))
	// 	Default.Install("write-file",
	// 		"write data to file, 'json or 'j if needed",
	// 		func(fn string, a interface{}, t OptAtom) error {
	// 			var buf []byte
	// 			switch t.Y.v {
	// 			case "j":
	// 				buf, _ = json.Marshal(a)
	// 			case "json":
	// 				buf, _ = json.MarshalIndent(a, "", "  ")
	// 			default:
	// 				buf = []byte(fmt.Sprint(a))
	// 			}
	// 			return ioutil.WriteFile(fn, buf, 0777)
	// 		})
	//
	// 	Default.Install("read-file", "read data from file", func(fn string) (string, error) {
	// 		buf, err := ioutil.ReadFile(fn)
	// 		return string(buf), err
	// 	})
	Default.Store("$", NewFunc(Macro|Vararg, func(s *State) {
		v := L(s.Args).stringify(true)
		expr, err := parser.ParseExpr(v)
		if err != nil {
			panic(fmt.Errorf("go syntax error %v", err))
		}
		var do func(ast.Expr) Value
		do = func(e ast.Expr) Value {
			switch e := e.(type) {
			case *ast.UnaryExpr:
				op := e.Op.String()
				switch e.Op {
				case token.NOT:
					op = "not"
				}
				return L(Empty, Y(op, 0), do(e.X))
			case *ast.BinaryExpr:
				op := e.Op.String()
				switch e.Op {
				case token.LAND:
					op = "and"
				case token.LOR:
					op = "or"
				}
				m := L(Empty, Y(op, 0), do(e.X), do(e.Y))
				return m
			case *ast.BasicLit:
				switch e.Kind {
				case token.INT:
					v, _ := strconv.ParseInt(e.Value, 10, 64)
					return I(int64(v))
				case token.FLOAT:
					v, _ := strconv.ParseFloat(e.Value, 64)
					return N(v)
				case token.STRING:
					v, _ := strconv.Unquote(e.Value)
					return S(v)
				}
			case *ast.Ident:
				return Y(e.Name, 0)
			case *ast.ParenExpr:
				return do(e.X)
			case *ast.CallExpr:
				r := []Value{do(e.Fun)}
				for i := range e.Args {
					r = append(r, do(e.Args[i]))
				}
				return L(Empty, r...)
			}
			panic(fmt.Errorf("$: %T not supported", e))
		}
		s.Out = do(expr)
	}))

	Default.Store("i64", NewFunc(1, func(s *State) { s.Out = s.PopArg() }))
	Default.Store("u64", NewFunc(1, func(s *State) { *(*interface{})(unsafe.Pointer(&s.Out)) = uint64(s.PopArgAs(NUM).I()) }))
	// 	// SRFI-9
	// 	type record struct {
	// 		name   string
	// 		num    int
	// 		parent *record
	// 	}
	// 	type _f struct {
	// 		name    string
	// 		index   int
	// 		mutable bool
	// 	}
	//
	// 	findRecordIndex := func(v []Value, expected *record) []Value {
	// 		for {
	// 			switch v[0].Type() {
	// 			case 'i':
	// 				if v[0].V() == expected {
	// 					return v
	// 				}
	// 				return nil
	// 			case LIST:
	// 				v = v[0].L()
	// 			}
	// 		}
	// 	}
	//
	// 	calcRecordTotalArgs := func(r *record) int {
	// 		Len := r.num
	// 		for r.parent != nil {
	// 			r = r.parent
	// 			Len += r.num
	// 		}
	// 		return Len
	// 	}
	//
	// 	Default.Install("define-record-type", 1|Macro|Vararg, func(s *State) {
	// 		// (define-record name (options...) ...)
	// 		recordName := s.In(0, SYM).S()
	// 		typeIndicator := &record{name: recordName}
	//
	// 		fields := map[string]*_f{}
	//
	// 		ret := []Value{
	// 			L(s.Caller.Y("define"), Y(recordName+"-type", 0, 0), V(typeIndicator)),
	// 		}
	//
	// 		for i := 1; i < len(s.Args); i++ {
	// 			l := s.In(i, LIST).L()
	// 			s.assert(len(l) >= 2 && l[0].Type() == SYM || s.panic("invalid record options: %v", s.Args[i]))
	// 			switch l[0].S() {
	// 			case "fields":
	// 				for i := 1; i < len(l); i++ {
	// 					field := l[i]
	// 					f := &_f{index: i}
	// 					switch _, va, _, vl, vtype := l[i]._value(); vtype {
	// 					case SYM:
	// 						f.name = recordName + "-" + va
	// 					case LIST:
	// 						s.assert(len(vl) == 2 && vl[0].Type() == SYM || s.panic("invalid field: %v", field))
	// 						f.name, f.mutable = recordName+"-"+vl[0].S(), vl[1].S() == "mutable"
	// 					default:
	// 						s.assert(false || s.panic("invalid field: %v", field))
	// 					}
	// 					fields[f.name] = f
	// 				}
	// 				typeIndicator.num = len(fields)
	// 			case "parent":
	// 				s.assert(typeIndicator.parent == nil || s.panic("multiple parents: %v", l[1]))
	// 				s.assert(l[1].Type() == SYM || s.panic("invalid parent: %v", l[1]))
	// 				pf, _ := s.Context.Load(l[1].S() + "-type")
	// 				typeIndicator.parent = pf.V().(*record)
	// 			}
	// 		}
	//
	// 		fieldNames := []string{}
	// 		for fn, f := range fields {
	// 			fieldNames = Append(fieldNames, fn)
	// 			ret = Append(ret, L(s.Caller.Y("define"), Y(recordName+"-"+f.name, 0, 0),
	// 				_Vquote(NewFunc(&Func{
	// 					fargs: 1,
	// 					f: func(ss *State) {
	// 						r := ss.In(0, LIST).L()
	// 						ss.assert(len(r) > 0 || ss.panic("invalid record: %v", ss.In(0, 0)))
	// 						r = findRecordIndex(r, typeIndicator)
	// 						ss.assert(r != nil || ss.panic("not '%s' record: %v", recordName, ss.In(0, 0)))
	// 						s.Out = r[f.index]
	// 					},
	// 				})),
	// 			))
	// 			if !f.mutable {
	// 				return
	// 			}
	// 			ret = Append(ret, L(s.Caller.Y("define"), Y(recordName+"-"+f.name+"-set!", 0, 0),
	// 				_Vquote(NewFunc(&Func{
	// 					fargs: 2,
	// 					f: func(ss *State) {
	// 						r := ss.In(0, LIST).L()
	// 						ss.assert(len(r) > 0 || ss.panic("invalid record: %v", ss.In(0, 0)))
	// 						r = findRecordIndex(r, typeIndicator)
	// 						ss.assert(r != nil || ss.panic("not '%s' record: %v", recordName, ss.In(0, 0)))
	// 						r[f.index] = ss.In(1, 0)
	// 					},
	// 				})),
	// 			))
	// 		}
	//
	// 		ret = Append(ret, L(s.Caller.Y("define"), Y(recordName+"-primary-fields", 0, 0), V(fieldNames)))
	//
	// 		// name, fields, typename := s.In(0, SYM).S(), make(map[string]int, len(s.Args)-1), new(int)
	// 		// for i := 1; i < len(s.Args); i++ {
	// 		// 	fields[s.In(i, SYM).S()] = i
	// 		// 	func(i int) {
	// 		// 		name := name + "-" + s.In(i, SYM).S()
	//
	// 		// 		s.Context.Install(name, 1, func(ss *State) { // getter
	// 		// 			ss.assert(len(ss.In(0, LIST).L()) == len(s.Args) && ss.In(0, LIST).L()[0].V() == typename || ss.panic("not a %s record", name))
	// 		// 			ss.Out = ss.In(0, LIST).L()[i]
	// 		// 		})
	//
	// 		// 		s.Context.Install(name+"-set!", 2, func(ss *State) { // setter
	// 		// 			ss.assert(len(ss.In(0, LIST).L()) == len(s.Args) && ss.In(0, LIST).L()[0].V() == typename || ss.panic("not a %s record", name))
	// 		// 			ss.In(0, LIST).L()[i] = ss.In(1, 0) // setter
	// 		// 		})
	// 		// 	}(i)
	// 		// }
	//
	// 		// s.Context.Install(name+"?", 1, func(ss *State) {
	// 		// 	ss.Out = B(len(ss.In(0, LIST).L()) == len(s.Args) && ss.In(0, LIST).L()[0].V() == typename)
	// 		// })
	//
	// 		ret = Append(ret, L(s.Caller.Y("define"), Y("make-"+recordName, 0, 0),
	// 			_Vquote(NewFunc(&Func{
	// 				fargs: calcRecordTotalArgs(typeIndicator),
	// 				f: func(ss *State) {
	// 					v := Append([]Value{V(typeIndicator)}, ss.Args...)
	// 					s.Out = L(v...)
	// 				},
	// 			})),
	// 		))
	// 		s.Out = L(ret...)
	// 	})
}

func (v Value) TypedVal(t reflect.Type) reflect.Value {
	if v.Type() == LIST {
		s := reflect.MakeSlice(t, 0, 0)
		v.L().ProRange(func(v Value) bool { s = reflect.Append(s, v.TypedVal(t.Elem())); return true })
		return s
	}
	vv := v.V()
	if vv == nil {
		return reflect.Zero(t)
	}
	if si, ok := vv.([]interface{}); ok {
		s := reflect.MakeSlice(t, 0, len(si))
		for _, v := range si {
			s = reflect.Append(s, reflect.ValueOf(v))
		}
		return s
	}
	rv := reflect.ValueOf(vv)
	if v.Type() == NUM {
		return rv.Convert(t)
	}
	return rv
}

func ev2(v interface{}, err error) Value {
	if err != nil {
		return V(err)
	}
	return V(v)
}

func (v Value) Add(v2 Value) Value {
	vf, vi, vIsInt := v.N()
	v2f, v2i, v2IsInt := v2.N()
	if vIsInt && v2IsInt {
		return I(vi + v2i)
	}
	return N(vf + v2f)
}
func (v Value) Sub(v2 Value) Value {
	vf, vi, vIsInt := v.N()
	v2f, v2i, v2IsInt := v2.N()
	if vIsInt && v2IsInt {
		return I(vi - v2i)
	}
	return N(vf - v2f)
}
func (v Value) Mul(v2 Value) Value {
	vf, vi, vIsInt := v.N()
	v2f, v2i, v2IsInt := v2.N()
	if vIsInt && v2IsInt {
		return I(vi * v2i)
	}
	return N(vf * v2f)
}
func (v Value) Div(v2 Value, idiv bool) Value {
	vf, vi, vIsInt := v.N()
	v2f, v2i, v2IsInt := v2.N()
	if vIsInt && v2IsInt {
		if r := vi / v2i; r*v2i == vi || idiv {
			return I(r)
		}
	}
	return N(vf / v2f)
}
func (v Value) Less(v2 Value, equal bool) bool {
	vf, vi, vIsInt := v.N()
	v2f, v2i, v2IsInt := v2.N()
	if vIsInt && v2IsInt {
		return vi < v2i || (equal && vi == v2i)
	}
	return vf < v2f || (equal && vf == v2f)
}
func (s *State) In(t1 ValueType) Value {
	return s.PopArgAs(t1)
}
func (s *State) In2(t1, t2 ValueType) (Value, Value) {
	return s.PopArgAs(t1), s.PopArgAs(t2)
}
func (s *State) In3(t1, t2, t3 ValueType) (Value, Value, Value) {
	return s.PopArgAs(t1), s.PopArgAs(t2), s.PopArgAs(t3)
}
func (s *State) In4(t1, t2, t3, t4 ValueType) (Value, Value, Value, Value) {
	return s.PopArgAs(t1), s.PopArgAs(t2), s.PopArgAs(t3), s.PopArgAs(t4)
}
