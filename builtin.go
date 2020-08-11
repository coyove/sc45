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
	"math/big"
	"os"
	"reflect"
	"strconv"
	"strings"
	"unsafe"
)

var DefaultStdout io.Writer = os.Stdout
var stateType = reflect.TypeOf(&State{})

func (s *State) InMap() map[string]Value {
	v, _ := s.InType('i').Val().(map[string]Value)
	return v
}

func (ctx *Context) String() string {
	p := bytes.NewBufferString("{")
	for k, v := range ctx.m {
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

func Fgo(fn interface{}) Value {
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
	return F(count, func(s *State) {
		ins := make([]reflect.Value, 0, rt.NumIn())
		if rt.IsVariadic() {
			for i := 0; i < rt.NumIn()-1; i++ {
				if t := rt.In(i); i == 0 && t == stateType {
					ins = append(ins, reflect.ValueOf(s))
				} else {
					ins = append(ins, s.In().TypedVal(t))
				}
			}
			for !s.Args.Empty() {
				ins = append(ins, s.In().TypedVal(rt.In(rt.NumIn()-1).Elem()))
			}
		} else {
			for i := 0; i < rt.NumIn(); i++ {
				if t := rt.In(i); i == 0 && t == stateType {
					ins = append(ins, reflect.ValueOf(s))
				} else {
					ins = append(ins, s.In().TypedVal(t))
				}
			}
		}
		outs := rf.Call(ins)
		switch rt.NumOut() {
		case 1:
			s.Out = Val(outs[0].Interface())
		case 2:
			if err, _ := outs[1].Interface().(error); err != nil {
				s.Out = Val(err)
			} else {
				s.Out = Val(outs[0].Interface())
			}
		}
	})
}

func _Ft(t byte) Value { return F(1, func(s *State) { s.Out = Bln(s.In().Type() == t) }) }

func init() {
	Default.Store("true", Bln(true)).Store("false", Bln(false)).Store("begin", F(Macro|Vararg, func(s *State) {
		s.Out = Lst(s.Args, s.Caller.Make("if"), Void, Void)
	})).Store("and", F(Macro|Vararg, func(s *State) {
		if s.Args.Empty() {
			s.Out = Bln(true)
		} else if !s.Args.HasNext() {
			s.Out = s.In()
		} else {
			s.Out = Lst(Empty, s.Caller.Make("if"), s.In(), Lst(s.Args, s.Caller.Make("and")), Bln(false))
		}
	})).Store("or", F(Macro|Vararg, func(s *State) {
		if s.Args.Empty() {
			s.Out = Bln(false)
		} else if !s.Args.HasNext() {
			s.Out = s.In()
		} else {
			s.Out = Lst(Empty, s.Caller.Make("if"), s.In(), Bln(true), Lst(s.Args, s.Caller.Make("or")))
		}
	})).Store("==", F(1|Vararg, func(s *State) {
		flag := true
		for s.In(); flag && !s.Args.Empty(); {
			flag = s.LastIn().Equals(s.In())
		}
		s.Out = Bln(flag)
	})).Store("=", Default.m["=="]).Store("!=", F(1|Vararg, func(s *State) {
		s.Out = Bln(!s.In().Equals(s.In()))
	})).Store("<>", Default.m["!="]).Store("<", F(1|Vararg, func(s *State) {
		flag := true
		for s.InType('n'); flag && !s.Args.Empty(); {
			flag = s.LastIn().Num() < s.InType('n').Num()
		}
		s.Out = Bln(flag)
	})).Store("<=", F(1|Vararg, func(s *State) {
		flag := true
		for s.InType('n'); flag && !s.Args.Empty(); {
			flag = s.LastIn().Num() <= s.InType('n').Num()
		}
		s.Out = Bln(flag)
	})).Store(">", F(1|Vararg|Macro, func(s *State) {
		s.Out = Lst(Empty, s.Caller.Make("not"), Lst(s.Args, s.Caller.Make("<=")))
	})).Store(">=", F(1|Vararg|Macro, func(s *State) {
		s.Out = Lst(Empty, s.Caller.Make("not"), Lst(s.Args, s.Caller.Make("<")))
	})).Store("not", F(1, func(s *State) {
		s.Out = Bln(s.In().IsFalse())
	})).Store("+", F(1|Vararg, func(s *State) {
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
	})).Store("-", F(1|Vararg, func(s *State) {
		a := s.InType('n').Num()
		if s.Args.Empty() {
			a = -a
		}
		for !s.Args.Empty() {
			a -= s.InType('n').Num()
		}
		s.Out = Num(a)
	})).Store("*", F(1|Vararg, func(s *State) {
		a := s.InType('n').Num()
		for !s.Args.Empty() {
			a *= s.InType('n').Num()
		}
		s.Out = Num(a)
	})).Store("/", F(1|Vararg, func(s *State) {
		a := s.InType('n').Num()
		for !s.Args.Empty() {
			a /= s.InType('n').Num()
		}
		s.Out = Num(a)
	})).Store("let", F(1|Vararg|Macro, func(s *State) {
		var names, values []Value
		s.InType('l').Lst().Range(func(pair Value) bool {
			s.assert(pair.Type() == 'l' || s.panic("invalid binding list format: %v", pair))
			p := pair.Lst()
			s.assert(p.HasNext() && p.Val().Type() == 'y' && p.Val().Str() != "" || s.panic("invalid binding list format: %v", pair))
			names, values = append(names, p.Val()), append(values, p.Next().Val())
			return true
		})
		fn := Lst(Empty, s.Caller.Make("lambda"), Lst(Empty, names...), Lst(s.Args, s.Caller.Make("if"), Void, Void))
		s.Out = Lst(Lst(Empty, values...).Lst(), fn)
	})).Store("eval", F(1, func(s *State) {
		s.Out = __exec(s.In(), execState{local: s.Context, curCaller: callerInfo{&Value{}, s.CallerLoc}})
	})).Store("parse", F(1, func(s *State) {
		x := s.InType('s').Str()
		if _, err := os.Stat(x); err == nil {
			buf, err := ioutil.ReadFile(x)
			if err != nil {
				s.Out = Val(err)
			} else {
				s.Out = ev2(s.Context.Parse(x, *(*string)(unsafe.Pointer(&buf))))
			}
		} else {
			s.Out = ev2(s.Context.Parse("(parse)", x))
		}
	})).Store("set-car!", F(2, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("set-car!: empty list"))
		l.SetVal(s.In())
	})).Store("set-cdr!", F(2, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("set-cdr!: empty list"))
		l.SetNext(s.InType('l').Lst())
	})).Store("list", F(Vararg, func(s *State) {
		s.Out = Lst(s.Args)
	})).Store("append", F(2, func(s *State) {
		s.Out = Lst(s.InType('l').Lst().Append(s.InType('l').Lst()))
	})).Store("cons", F(2, func(s *State) {
		s.Out = Lst(Cons(s.In(), s.In()))
	})).Store("car", F(1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("car: empty list"))
		s.Out = l.Val()
	})).Store("cdr", F(1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("cdr: empty list"))
		s.Out = Lst(l.Next())
	})).Store("last", F(1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("last: empty list"))
		s.Out = l.Last().Val()
	})).Store("init", F(1, func(s *State) {
		l := s.InType('l').Lst()
		s.assert(!l.Empty() || s.panic("init: empty list"))
		s.Out = Lst(l.Take(-1))
	})).Store("length", F(1, func(s *State) {
		s.Out = Num(float64(s.InType('l').Lst().Len()))
	})).Store("pcall", F(2, func(s *State) {
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
		s.Out = __exec(Lst(Empty, s.In().Quote()), execState{curCaller: callerInfo{&Value{}, new(string)}, local: s.Context})
	})).Store("apply", F(2, func(s *State) {
		expr := initlistbuilder().append(s.InType('f').Quote())
		s.InType('l').Lst().Range(func(v Value) bool { expr = expr.append(v.Quote()); return true })
		v, err := (*Context)(nil).Exec(expr.value())
		s.assert(err == nil || s.panic("apply panic: %v", err))
		s.Out = v
	})).
		Store("raise", F(1, func(s *State) { panic(s.In()) })).
		Store("string->number", F(1, func(s *State) { s.Out = ev2(strconv.ParseFloat(s.InType('s').Str(), 64)) })).
		Store("symbol->string", F(1, func(s *State) { s.Out = Str(s.InType('y').Str()) })).
		Store("number->string", F(1, func(s *State) { s.Out = Str(strconv.FormatFloat(s.InType('n').Num(), 'f', -1, 64)) })).
		Store("string->symbol", F(1, func(s *State) { s.Out = Sym(s.InType('s').Str(), 0, 0) })).
		Store("string->error", F(1, func(s *State) { s.Out = Val(fmt.Errorf(s.InType('s').Str())) })).
		Store("error?", F(1, func(s *State) { _, ok := s.In().Val().(error); s.Out = Bln(ok) })).
		Store("null?", F(1, func(s *State) { s.Out = Bln(s.In().Type() == 'l' && s.LastIn().Lst().Empty()) })).
		Store("list?", F(1, func(s *State) { s.Out = Bln(s.In().Type() == 'l' && s.LastIn().Lst().Proper()) })).
		Store("void?", F(1, func(s *State) { s.Out = Bln(s.In() == Void) })).Store("pair?", _Ft('l')).Store("symbol?", _Ft('y')).Store("boolean?", _Ft('b')).Store("number?", _Ft('n')).Store("string?", _Ft('s')).
		Store("stringify", F(1, func(s *State) { s.Out = Str(s.In().String()) }))
	Default.Store("letrec", F(1|Vararg|Macro, func(s *State) {
		/* Unwrap to:
		(let ((var1 ()) ... (varn ())                  // outer binds
			(let ((var1_tmp val1) ... (varn_tmp valn)) // inner binds
				(set! 'var1 var1_tmp)                  // inner sets
				...
				(set! 'varn varb_tmp)
				expr...                                // expressions
		*/
		let, setq := s.Caller.Make("let"), s.Caller.Make("set!")
		var innersets, innerbinds, outerbinds []Value
		s.InType('l').Lst().Range(func(v Value) bool {
			s.assert(v.Type() == 'l' || s.panic("invalid binding list format: %v", v))
			b := v.Lst()
			s.assert(b.HasNext() && b.Val().Type() == 'y' && b.Val().Str() != "" || s.panic("invalid binding list format: %v", v))
			tmpvar := Sym(b.Val().Str()+"tmp", 0, 0)
			innersets = append(innersets, Lst(Empty, setq, b.Val(), tmpvar))
			innerbinds = append(innerbinds, Lst(Empty, tmpvar, b.Next().Val()))
			outerbinds = append(outerbinds, Lst(Empty, b.Val(), Void))
			return true
		})
		inner := Lst(Lst(s.Args, innersets...).Lst(), let, Lst(Empty, innerbinds...))
		outer := []Value{let, Lst(Empty, outerbinds...), inner}
		s.Out = Lst(Empty, outer...)
	}))
	Default.Store("let*", F(1|Vararg|Macro, func(s *State) {
		/* Unwrap to:
		(let ((var1 val1)
			(let ((var2 val2))
				...
					expr...
		*/
		let, binds := s.Caller.Make("let"), s.InType('l').Lst().ToSlice()
		last := Lst(s.Args, s.Caller.Make("begin"))
		for i := len(binds) - 1; i >= 0; i-- {
			bd := binds[i]
			s.assert(bd.Type() == 'l' || s.panic("invalid binding list format: %v", bd))
			lst := bd.Lst()
			s.assert(lst.HasNext() && lst.Val().Type() == 'y' && lst.Val().Str() != "" || s.panic("invalid binding list format: %v", bd))
			last = Lst(Empty, let, Lst(Empty, bd), last)
		}
		s.Out = last
	}))
	Default.Store("define-modules", F(1|Vararg, func(s *State) {
	}))

	RegisterGoType(int64(0))
	Default.Store("i64", F(1|Macro, func(s *State) { v, _ := strconv.ParseInt(trystr(s), 0, 64); s.Out = Val(v) }))

	RegisterGoType(uint64(0))
	Default.Store("u64", F(1|Macro, func(s *State) { v, _ := strconv.ParseUint(trystr(s), 0, 64); s.Out = Val(v) }))

	RegisterGoType(&big.Int{})
	Default.Store("bigint", F(1|Macro, func(s *State) { i := &big.Int{}; i.UnmarshalText([]byte(trystr(s))); s.Out = Val(i) }))

	Default.Store("go->value", F(1, func(s *State) {
		rv := reflect.ValueOf(s.In().Val())
		switch rv.Kind() {
		case reflect.Slice, reflect.Array:
			l := initlistbuilder()
			for i := 0; i < rv.Len(); i++ {
				l = l.append(Val(rv.Index(i).Interface()))
			}
			s.Out = l.value()
		default:
			s.Out = s.LastIn()
		}
	}))
	Default.Store("hash-new", F(Vararg, func(s *State) {
		m := map[string]Value{}
		for !s.Args.Empty() {
			m[s.InType('s').Str()] = s.In()
		}
		s.Out = Val(m)
	}))
	Default.Store("hash-set!", F(3, func(s *State) { s.InMap()[s.InType('s').Str()] = s.In() }))
	Default.Store("hash-delete!", F(2, func(s *State) { delete(s.InMap(), s.InType('s').Str()) }))
	Default.Store("hash-get", F(2, func(s *State) { s.Out = s.InMap()[s.InType('s').Str()] }))
	Default.Store("hash-contains?", F(2, func(s *State) { _, ok := s.InMap()[s.InType('s').Str()]; s.Out = Bln(ok) }))
	Default.Store("hash-keys", F(1, func(s *State) {
		ret := initlistbuilder()
		for i := range s.InMap() {
			ret = ret.append(Str(i))
		}
		s.Out = ret.value()
	}))

	Default.Store("string-length", F(1, func(s *State) { s.Out = Num(float64(len(s.InType('s').Str()))) }))
	Default.Store("substring?", F(2, func(s *State) { s.Out = Bln(strings.Contains(s.InType('s').Str(), s.InType('s').Str())) }))
	// 	Default.Install("skip", 2, func(s *State) {
	// 		l := s.In(1, 'l').Lst()
	// 		for i := 0; i < int(s.In(0, 'n').Num()); i++ {
	// 			l, _ = Tail(l)
	// 		}
	// 		s.Out = Lst(l...)
	// 	})
	// 	Default.Install("lambda*", 2|Vararg|Macro, func(s *State) {
	// 		tmpvar := "a" + strconv.FormatInt(time.Now().Unix(), 10)
	// 		pl, body := s.In(0, 'l').Lst(), []Value{
	// 			s.Caller.Make("lambda"),
	// 			s.Caller.Make(tmpvar),
	// 			Lst(s.Caller.Make("define"), s.Caller.Make(tmpvar+"-len"), Lst(
	// 				s.Caller.Make("vector-len"), s.Caller.Make(tmpvar),
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
	// 			if pl[i].Type() == 'y' {
	// 				name, val = pl[i], Empty
	// 				if a := pl[i].Str(); strings.HasSuffix(a, "...") {
	// 					// Special case: "name..." to catch the rest arguments
	// 					body = append(body, Lst(
	// 						s.Caller.Make("define"),
	// 						s.Caller.Make(ifstr(len(a) == 3, "...", a[:len(a)-3])),
	// 						Lst(s.Caller.Make("skip"), Num(float64(i)), s.Caller.Make(tmpvar)),
	// 					))
	// 					continue
	// 				}
	// 			} else {
	// 				s.assert(pl[i].Type() == 'l' && pl[i]._len() == 2 || s.panic("invalid binding list: %v", pl[i]))
	// 				name, val = pl[i]._at(0), pl[i]._at(1)
	// 			}
	// 			body = append(body, Lst(
	// 				s.Caller.Make("define"),
	// 				name,
	// 				Lst(
	// 					s.Caller.Make("if"),
	// 					Lst(s.Caller.Make("<"), Num(float64(i)), s.Caller.Make(tmpvar+"-len")),
	// 					Lst(s.Caller.Make("vector-nth"), s.Caller.Make(tmpvar), Num(float64(i))),
	// 					val,
	// 				),
	// 			))
	// 		}
	// 		body = append(body, s.Args[1:]...)
	// 		s.Out = Lst(body...)
	// 	})
	Default.Store("vector-bytes", F(1, func(s *State) { s.Out = Val(make([]byte, int(s.InType('n').Num()))) }))
	Default.Store("vector-strings", F(1, func(s *State) { s.Out = Val(make([]string, int(s.InType('n').Num()))) }))
	Default.Store("vector-ints", F(1, func(s *State) { s.Out = Val(make([]int, int(s.InType('n').Num()))) }))
	Default.Store("vector-int64s", F(1, func(s *State) { s.Out = Val(make([]int64, int(s.InType('n').Num()))) }))
	Default.Store("vector-len", F(1, func(s *State) { s.Out = Num(float64((reflect.ValueOf(s.In().Val()).Len()))) }))
	Default.Store("vector-null?", F(1, func(s *State) { s.Out = Bln(reflect.ValueOf(s.In().Val()).Len() == 0) }))
	Default.Store("vector-nth", F(2, func(s *State) {
		rm := reflect.ValueOf(s.In().Val())
		s.Out = Val(rm.Index(int(s.InType('n').Num())).Interface())
	}))
	Default.Store("vector-set-nth!", F(3, func(s *State) {
		rm := reflect.ValueOf(s.In().Val())
		rm.Index(int(s.InType('n').Num())).Set(s.In().TypedVal(rm.Type().Elem()))
	}))
	Default.Store("vector-slice", F(3, func(s *State) {
		rl := reflect.ValueOf(s.In().Val())
		start, end := int(s.InType('n').Num()), int(s.InType('n').Num())
		s.Out = Val(rl.Slice(start, end).Interface())
	}))
	Default.Store("vector-concat", F(2, func(s *State) {
		rv1, rv2 := reflect.ValueOf(s.In().Val()), reflect.ValueOf(s.In().Val())
		s.assert(rv1.Type() == rv2.Type() || s.panic("vector-concat: different type"))
		r := reflect.MakeSlice(rv1.Type(), rv1.Len(), rv1.Len()+rv2.Len())
		reflect.Copy(r, rv1)
		reflect.AppendSlice(r, rv2)
		s.Out = Val(r.Interface())
	}))
	Default.Store("vector-foreach", F(2, func(s *State) {
		rl, fn := reflect.ValueOf(s.In().Val()), s.InType('f')
		for i := 0; i < rl.Len(); i++ {
			flag, err := fn.Fun().Call(Num(float64(i)), Val(rl.Index(i).Interface()))
			s.assert(err == nil || s.panic("invalid callback "))
			if flag.IsFalse() {
				break
			}
		}
	}))
	Default.Store("map", F(2, func(s *State) {
		fn, r, l, i := s.InType('f'), []Value{}, s.InType('l').Lst(), 0
		l.Range(func(h Value) bool {
			v, err := fn.Fun().Call(h)
			s.assert(err == nil || s.panic("map: error at element #%d: %v", i, err))
			r = append(r, v)
			i++
			return true
		})
		s.Out = Lst(Empty, r...)
	}))
	Default.Store("reduce", F(3, func(s *State) {
		fn, left, l, i := s.InType('f'), s.In(), s.InType('l').Lst(), 0
		var err error
		l.Range(func(h Value) bool {
			left, err = fn.Fun().Call(left, h)
			s.assert(err == nil || s.panic("reduce: error at element #%d: %v", i, err))
			i++
			return true
		})
		s.Out = left
	}))
	Default.Store("reduce-right", F(3, func(s *State) {
		fn, right, rl := s.InType('f'), s.In(), s.InType('l').Lst().ToSlice()
		var err error
		for i := len(rl) - 1; i >= 0; i-- {
			right, err = fn.Fun().Call(right, rl[i])
			s.assert(err == nil || s.panic("reduce-right: error at element #%d: %v", i, err))
		}
		s.Out = right
	}))
	// 	Default.Install("cond", Macro|Vararg, func(s *State) {
	// 		if len(s.Args) == 0 {
	// 			s.Out = s.Caller.Make("true")
	// 			return
	// 		}
	// 		build := func(expr Value) []Value {
	// 			s.assert(expr.Type() == 'l' && expr._len() == 2 || s.panic("invalid cond statement: %v", expr))
	// 			cond, stat := expr.Lst()[0], expr.Lst()[1]
	// 			if cond.Type() == 'y' && cond.Str() == "else" {
	// 				cond = s.Caller.Make("true")
	// 			}
	// 			return []Value{s.Caller.Make("if"), cond, stat, Void}
	// 		}
	// 		exprs := build(s.In(0, 0))
	// 		for i, head := 1, exprs; i < len(s.Args); i++ {
	// 			tail := build(s.In(i, 0))
	// 			head[3] = Lst(tail...)
	// 			head = tail
	// 		}
	// 		s.Out = Lst(exprs...)
	// 	})
	// 	// 	Default.Install("(eq any any...)", func(s *State) {
	// 	// 		s.Out = true
	// 	// 		for i, a := 1, s.In(0, 0); i < len(s.Args); i++ {
	// 	// 			s.Out = s.Out.(bool) && reflect.DeepEqual(a, s.Args[i])
	// 	// 		}
	// 	// 	})
	Default.Store("struct-get", F(1|Vararg, func(s *State) {
		rv := reflect.ValueOf(s.In().Val())
		s.Args.Range(func(v Value) bool {
			if rv.Kind() == reflect.Ptr {
				rv = rv.Elem()
			}
			s.assert(v.Type() == 'y' || s.panic("expect field name to be symbol: %v", v))
			rv = rv.FieldByName(v.Str())
			return true
		})
		s.Out = Val(rv.Interface())
	}))
	Default.Store("struct-set!", F(2|Vararg, func(s *State) {
		rv := reflect.ValueOf(s.In().Val())
		v := s.In()
		s.Args.Range(func(v Value) bool {
			if rv.Kind() == reflect.Ptr {
				rv = rv.Elem()
			}
			s.assert(v.Type() == 'y' || s.panic("expect field name to be symbol: %v", v))
			rv = rv.FieldByName(v.Str())
			return true
		})
		rv.Set(reflect.ValueOf(v.Val()))
	}))
	Default.Store("^", F(Vararg, func(s *State) {
		p := bytes.Buffer{}
		s.Args.Range(func(v Value) bool { p.WriteString(v.Str()); return true })
		s.Out = Str(p.String())
	}))
	Default.Store("display", F(Vararg, func(s *State) { fmt.Fprintln(DefaultStdout, vlisttointerface(s.Args.ToSlice())...) }))
	Default.Store("newline", F(0, func(s *State) { fmt.Fprintln(DefaultStdout) }))
	// Default.Store("printf",F( 1|Vararg, func(s *State) { fmt.Fprintf(DefaultStdout, s.In(0, 's').Str(), vlisttointerface(s.Args[1:])...) }))
	// 	Default.Install("regex/match", 2, func(s *State) {
	// 		s.Out = Bln(regexp.MustCompile(s.In(0, 's').Str()).MatchString(s.In(1, 's').Str()))
	// 	})
	// 	Default.Install("regex/find", 3, func(s *State) {
	// 		s.Out = ValRec(regexp.MustCompile(s.In(0, 's').Str()).FindAllStringSubmatch(s.In(1, 's').Str(), int(s.In(2, 'n').Num())))
	// 	})
	Default.Store("json", F(1, func(s *State) {
		buf, err := json.MarshalIndent(s.In().Val(), "", "  ")
		s.Out = ev2(string(buf), err)
	}))
	Default.Store("json-c", F(1, func(s *State) {
		buf, err := json.Marshal(s.In().Val())
		s.Out = ev2(string(buf), err)
	}))
	Default.Store("json-parse", F(1, func(s *State) {
		text := strings.TrimSpace(s.InType('s').Str())
		if strings.HasPrefix(text, "{") {
			m := map[string]interface{}{}
			if err := json.Unmarshal([]byte(text), &m); err != nil {
				s.Out = Val(err)
			} else {
				s.Out = Val(m)
			}
		} else if strings.HasPrefix(text, "[") {
			m := []interface{}{}
			if err := json.Unmarshal([]byte(text), &m); err != nil {
				s.Out = Val(err)
			} else {
				s.Out = Val(m)
			}
		} else {
			var m interface{}
			if err := json.Unmarshal([]byte(text), &m); err != nil {
				s.Out = Val(err)
			} else {
				s.Out = Val(m)
			}
		}
	}))
	Default.Store("setf!", F(2|Macro, func(s *State) {
		a, v := s.InType('y').Str(), s.In()
		parts := strings.Split(a, ".")
		s.assert(len(parts) > 1 || s.panic("too few fields to set"))
		structname := parts[0]
		setter := initlistbuilder().append(v.Make("struct-set!")).append(v.Make(structname)).append(v)
		for i := 1; i < len(parts); i++ {
			setter = setter.append(v.Make(parts[i]).Quote())
		}
		s.Out = setter.value()
	}))
	Default.Store("getf", F(1|Macro, func(s *State) {
		a := s.InType('y').Str()
		parts := strings.Split(a, ".")
		s.assert(len(parts) > 1 || s.panic("too few fields to get"))
		structname := parts[0]
		setter := initlistbuilder().append(s.Caller.Make("struct-get")).append(s.Caller.Make(structname))
		for i := 1; i < len(parts); i++ {
			setter = setter.append(s.Caller.Make(parts[i]).Quote())
		}
		s.Out = setter.value()
	}))
	// 	Default.Install("write-file",
	// 		"write data to file, 'json or 'j if needed",
	// 		func(fn string, a interface{}, t OptAtom) error {
	// 			var buf []byte
	// 			switch t.A.v {
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
	Default.Store("$", F(Macro|Vararg, func(s *State) {
		v := Lst(s.Args).stringify(true)
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
				return Lst(Empty, Sym(op, 0, 0), do(e.X))
			case *ast.BinaryExpr:
				op := e.Op.String()
				switch e.Op {
				case token.LAND:
					op = "and"
				case token.LOR:
					op = "or"
				}
				m := Lst(Empty, Sym(op, 0, 0), do(e.X), do(e.Y))
				return m
			case *ast.BasicLit:
				switch e.Kind {
				case token.INT:
					v, _ := strconv.ParseInt(e.Value, 10, 64)
					return Num(float64(v))
				case token.FLOAT:
					v, _ := strconv.ParseFloat(e.Value, 64)
					return Num(v)
				case token.STRING:
					v, _ := strconv.Unquote(e.Value)
					return Str(v)
				}
			case *ast.Ident:
				return Sym(e.Name, 0, 0)
			case *ast.ParenExpr:
				return do(e.X)
			case *ast.CallExpr:
				r := []Value{do(e.Fun)}
				for i := range e.Args {
					r = append(r, do(e.Args[i]))
				}
				return Lst(Empty, r...)
			}
			panic(fmt.Errorf("$: %T not supported", e))
		}
		s.Out = do(expr)
	}))
	//
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
	// 				if v[0].Val() == expected {
	// 					return v
	// 				}
	// 				return nil
	// 			case 'l':
	// 				v = v[0].Lst()
	// 			}
	// 		}
	// 	}
	//
	// 	calcRecordTotalArgs := func(r *record) int {
	// 		count := r.num
	// 		for r.parent != nil {
	// 			r = r.parent
	// 			count += r.num
	// 		}
	// 		return count
	// 	}
	//
	// 	Default.Install("define-record-type", 1|Macro|Vararg, func(s *State) {
	// 		// (define-record name (options...) ...)
	// 		recordName := s.In(0, 'y').Str()
	// 		typeIndicator := &record{name: recordName}
	//
	// 		fields := map[string]*_f{}
	//
	// 		ret := []Value{
	// 			Lst(s.Caller.Make("define"), Sym(recordName+"-type", 0, 0), Val(typeIndicator)),
	// 		}
	//
	// 		for i := 1; i < len(s.Args); i++ {
	// 			l := s.In(i, 'l').Lst()
	// 			s.assert(len(l) >= 2 && l[0].Type() == 'y' || s.panic("invalid record options: %v", s.Args[i]))
	// 			switch l[0].Str() {
	// 			case "fields":
	// 				for i := 1; i < len(l); i++ {
	// 					field := l[i]
	// 					f := &_f{index: i}
	// 					switch _, va, _, vl, vtype := l[i]._value(); vtype {
	// 					case 'y':
	// 						f.name = recordName + "-" + va
	// 					case 'l':
	// 						s.assert(len(vl) == 2 && vl[0].Type() == 'y' || s.panic("invalid field: %v", field))
	// 						f.name, f.mutable = recordName+"-"+vl[0].Str(), vl[1].Str() == "mutable"
	// 					default:
	// 						s.assert(false || s.panic("invalid field: %v", field))
	// 					}
	// 					fields[f.name] = f
	// 				}
	// 				typeIndicator.num = len(fields)
	// 			case "parent":
	// 				s.assert(typeIndicator.parent == nil || s.panic("multiple parents: %v", l[1]))
	// 				s.assert(l[1].Type() == 'y' || s.panic("invalid parent: %v", l[1]))
	// 				pf, _ := s.Context.Load(l[1].Str() + "-type")
	// 				typeIndicator.parent = pf.Val().(*record)
	// 			}
	// 		}
	//
	// 		fieldNames := []string{}
	// 		for fn, f := range fields {
	// 			fieldNames = append(fieldNames, fn)
	// 			ret = append(ret, Lst(s.Caller.Make("define"), Sym(recordName+"-"+f.name, 0, 0),
	// 				_Vquote(Fun(&Func{
	// 					fargs: 1,
	// 					f: func(ss *State) {
	// 						r := ss.In(0, 'l').Lst()
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
	// 			ret = append(ret, Lst(s.Caller.Make("define"), Sym(recordName+"-"+f.name+"-set!", 0, 0),
	// 				_Vquote(Fun(&Func{
	// 					fargs: 2,
	// 					f: func(ss *State) {
	// 						r := ss.In(0, 'l').Lst()
	// 						ss.assert(len(r) > 0 || ss.panic("invalid record: %v", ss.In(0, 0)))
	// 						r = findRecordIndex(r, typeIndicator)
	// 						ss.assert(r != nil || ss.panic("not '%s' record: %v", recordName, ss.In(0, 0)))
	// 						r[f.index] = ss.In(1, 0)
	// 					},
	// 				})),
	// 			))
	// 		}
	//
	// 		ret = append(ret, Lst(s.Caller.Make("define"), Sym(recordName+"-primary-fields", 0, 0), Val(fieldNames)))
	//
	// 		// name, fields, typename := s.In(0, 'y').Str(), make(map[string]int, len(s.Args)-1), new(int)
	// 		// for i := 1; i < len(s.Args); i++ {
	// 		// 	fields[s.In(i, 'y').Str()] = i
	// 		// 	func(i int) {
	// 		// 		name := name + "-" + s.In(i, 'y').Str()
	//
	// 		// 		s.Context.Install(name, 1, func(ss *State) { // getter
	// 		// 			ss.assert(len(ss.In(0, 'l').Lst()) == len(s.Args) && ss.In(0, 'l').Lst()[0].Val() == typename || ss.panic("not a %s record", name))
	// 		// 			ss.Out = ss.In(0, 'l').Lst()[i]
	// 		// 		})
	//
	// 		// 		s.Context.Install(name+"-set!", 2, func(ss *State) { // setter
	// 		// 			ss.assert(len(ss.In(0, 'l').Lst()) == len(s.Args) && ss.In(0, 'l').Lst()[0].Val() == typename || ss.panic("not a %s record", name))
	// 		// 			ss.In(0, 'l').Lst()[i] = ss.In(1, 0) // setter
	// 		// 		})
	// 		// 	}(i)
	// 		// }
	//
	// 		// s.Context.Install(name+"?", 1, func(ss *State) {
	// 		// 	ss.Out = Bln(len(ss.In(0, 'l').Lst()) == len(s.Args) && ss.In(0, 'l').Lst()[0].Val() == typename)
	// 		// })
	//
	// 		ret = append(ret, Lst(s.Caller.Make("define"), Sym("make-"+recordName, 0, 0),
	// 			_Vquote(Fun(&Func{
	// 				fargs: calcRecordTotalArgs(typeIndicator),
	// 				f: func(ss *State) {
	// 					v := append([]Value{Val(typeIndicator)}, ss.Args...)
	// 					s.Out = Lst(v...)
	// 				},
	// 			})),
	// 		))
	// 		s.Out = Lst(ret...)
	// 	})
}

func (v Value) TypedVal(t reflect.Type) reflect.Value {
	if v.Type() == 'l' {
		s := reflect.MakeSlice(t, 0, 0)
		v.Lst().Range(func(v Value) bool { s = reflect.Append(s, v.TypedVal(t.Elem())); return true })
		return s
	}
	vv := v.Val()
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
	if v.Type() == 'n' {
		return rv.Convert(t)
	}
	return rv
}

func vlisttointerface(l []Value) []interface{} {
	a := make([]interface{}, len(l))
	for i := range l {
		a[i] = l[i]
	}
	return a
}

func trystr(s *State) string {
	switch s.In().Type() {
	case 's', 'y':
		return s.LastIn().Str()
	case 'n':
		if s.LastIn().ptr != nil {
			return s.LastIn().Str()
		}
	}
	return ""
}
