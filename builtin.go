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
	"regexp"
	"strconv"
	"strings"
	"time"
	"unsafe"
)

var (
	DefaultStdout io.Writer = os.Stdout
	valueType               = reflect.TypeOf(Value{})
	fastNow       int64     = time.Now().Unix()
	Vararg, Macro           = 1 << 30, 1 << 29
)

func NewFunc(a int, f func(*State)) Value {
	return F(&Func{F: f, MinArgNum: a & 0xffff, Vararg: a&Vararg != 0, Macro: a&Macro != 0, Source: "(sys)"})
}

func (s *State) InMap() map[string]Value {
	v, _ := s.In().V().(map[string]Value)
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

func init() {
	Now = func() int64 { return fastNow }
	go func() {
		for range time.Tick(time.Second) {
			fastNow = time.Now().Unix()
		}
	}()

	Default.Store("true", B(true))
	Default.Store("false", B(false))
	Default.Store("begin", NewFunc(Macro|Vararg, func(s *State) { s.Out = L(s.Args, s.Caller.Y("if"), Void, Void) }))
	Default.Store("and", NewFunc(Macro|Vararg, func(s *State) {
		if s.Args.MustProper().Empty() {
			s.Out = B(true)
		} else if !s.Args.HasProperCdr() {
			s.Out = s.In()
		} else {
			s.Out = L(Empty, s.Caller.Y("if"), s.In(), L(s.Args, s.Caller.Y("and")), B(false))
		}
	}))
	Default.Store("or", NewFunc(Macro|Vararg, func(s *State) {
		if s.Args.MustProper().Empty() {
			s.Out = B(false)
		} else if !s.Args.HasProperCdr() {
			s.Out = s.In()
		} else {
			s.Out = L(Empty, s.Caller.Y("if"), s.In(), B(true), L(s.Args, s.Caller.Y("or")))
		}
	}))
	Default.Store("==", NewFunc(1|Vararg, func(s *State) {
		flag := true
		for last := s.In(); flag && !s.Args.MustProper().Empty(); last = s.LastIn {
			flag = last.Equals(s.In())
		}
		s.Out = B(flag)
	}))
	Default.Store("=", Default.M["=="])
	Default.Store("!=", NewFunc(1|Vararg, func(s *State) { s.Out = B(!s.In().Equals(s.In())) }))
	Default.Store("<>", Default.M["!="])
	Default.Store("<", NewFunc(1|Vararg, func(s *State) {
		flag := true
		for last := s.Nv(); flag && !s.Args.MustProper().Empty(); last = s.LastIn {
			flag = last.Less(s.Nv(), false)
		}
		s.Out = B(flag)
	}))
	Default.Store("<=", NewFunc(1|Vararg, func(s *State) {
		flag := true
		for last := s.Nv(); flag && !s.Args.MustProper().Empty(); last = s.LastIn {
			flag = last.Less(s.Nv(), true)
		}
		s.Out = B(flag)
	}))
	Default.Store(">", NewFunc(1|Vararg, func(s *State) {
		flag := true
		for last := s.Nv(); flag && !s.Args.MustProper().Empty(); last = s.LastIn {
			flag = !last.Less(s.Nv(), true)
		}
		s.Out = B(flag)
	}))
	Default.Store(">=", NewFunc(1|Vararg|Macro, func(s *State) {
		s.Out = L(Empty, s.Caller.Y("not"), L(s.Args, s.Caller.Y("<")))
	}))
	Default.Store("not", NewFunc(1, func(s *State) { s.Out = B(s.In().IsFalse()) }))
	Default.Store("+", NewFunc(1|Vararg, func(s *State) {
		switch s.Out = s.In(); s.Out.Type() {
		case NUM:
			for !s.Args.MustProper().Empty() {
				s.Out = s.Out.Add(s.Nv())
			}
		case STR:
			vs := bytes.NewBufferString(s.Out.S())
			for !s.Args.MustProper().Empty() {
				vs.WriteString(s.S())
			}
			s.Out = S(vs.String())
		default:
			panic(fmt.Errorf("can't apply '+' on %v", s.Out))
		}
	}))
	Default.Store("-", NewFunc(1|Vararg, func(s *State) {
		a := s.Nv()
		if s.Args.MustProper().Empty() {
			af, ai, aIsInt := a.N()
			_ = aIsInt && s.Out.of(I(-ai)) || s.Out.of(N(-af))
			return
		}
		for !s.Args.MustProper().Empty() {
			a = a.Sub(s.Nv())
		}
		s.Out = a
	}))
	Default.Store("*", NewFunc(1|Vararg, func(s *State) {
		s.Out = s.Nv()
		for !s.Args.MustProper().Empty() {
			s.Out = s.Out.Mul(s.Nv())
		}
	}))
	Default.Store("/", NewFunc(1|Vararg, func(s *State) {
		s.Out = s.Nv()
		for !s.Args.MustProper().Empty() {
			s.Out = s.Out.Div(s.Nv(), false)
		}
	}))
	Default.Store("idiv", NewFunc(1|Vararg, func(s *State) {
		s.Out = s.Nv()
		for !s.Args.MustProper().Empty() {
			s.Out = s.Out.Div(s.Nv(), true)
		}
	}))
	Default.Store("let", NewFunc(1|Vararg|Macro, func(s *State) {
		var names, values []Value
		s.L().Foreach(func(pair Value) bool {
			s.assert(pair.Type() == LIST || s.panic("invalid binding list format: %v", pair))
			p := pair.L()
			s.assert(p.HasProperCdr() && p.val.Type() == SYM && p.val.S() != "" || s.panic("invalid binding list format: %v", pair))
			names, values = append(names, p.val), append(values, p.next.val)
			return true
		})
		fn := L(Empty, s.Caller.Y("lambda"), L(Empty, names...), L(s.Args, s.Caller.Y("if"), Void, Void))
		s.Out = L(L(Empty, values...).L(), fn)
	}))
	Default.Store("eval", NewFunc(1, func(s *State) {
		s.Out = __exec(s.In(), execState{local: s.Context, debug: s.Stack, deadline: s.deadline})
	}))
	Default.Store("parse", NewFunc(1, func(s *State) {
		x := s.S()
		if _, err := os.Stat(x); err == nil {
			buf, err := ioutil.ReadFile(x)
			_ = err != nil && s.Out.of(V(err)) || s.Out.of(ev2(s.Context.Parse(x, *(*string)(unsafe.Pointer(&buf)))))
		} else {
			s.Out = ev2(s.Context.Parse("(parse)", x))
		}
	}))
	Default.Store("set-car!", NewFunc(2, func(s *State) {
		l := s.L()
		s.assert(!l.MustProper().Empty() || s.panic("set-car!: empty list"))
		l.val = s.In()
	}))
	Default.Store("set-cdr!", NewFunc(2, func(s *State) { s.Out = L(s.L().SetCdr(s.In())) }))
	Default.Store("list", NewFunc(Vararg, func(s *State) { s.Out = L(s.Args) }))
	Default.Store("append", NewFunc(2, func(s *State) {
		b := InitListBuilder()
		s.L().Foreach(func(v Value) bool { b = b.Append(v); return true })
		if b.last == nil {
			s.Out = s.In()
		} else {
			b.last.SetCdr(s.In())
			s.Out = b.Build()
		}
	}))
	Default.Store("cons", NewFunc(2, func(s *State) { s.Out = L(Cons(s.In(), s.In())) }))
	Default.Store("car", NewFunc(1, func(s *State) { s.Out = s.L().Car() }))
	Default.Store("cdr", NewFunc(1, func(s *State) { s.Out = s.L().Cdr() }))
	Default.Store("last", NewFunc(1, func(s *State) {
		l := s.L()
		s.assert(!l.MustProper().Empty() || s.panic("last: empty list"))
		s.Out = l.Last().val
	}))
	Default.Store("init", NewFunc(1, func(s *State) { s.Out = L(s.L().Take(-2)) }))
	Default.Store("skip", NewFunc(2, func(s *State) {
		l, n := s.L(), s.Nv().I()
		for ; n > 0 && l != nil; l, n = l.next, n-1 {
		}
		panicif(n > 0, "skip: not enough values")
		panicif(l == nil, "skip: improper list")
		s.Out = L(l)
	}))
	Default.Store("length", NewFunc(1, func(s *State) { s.Out = I(int64(s.L().Length())) }))
	Default.Store("pcall", NewFunc(2, func(s *State) {
		rc, old := s.In(), s.Stack.Frames
		defer func() {
			if r := recover(); r != nil {
				_ = rc.Type() != FUNC && s.Out.of(V(r)) || s.Out.of(ev2(rc.F().CallOnStack(s.Stack, s.Deadline(), L(Empty, V(r)))))
				s.Stack.Frames = old
			}
		}()
		s.Out = __exec(L(Empty, s.In().Quote()), execState{debug: s.Stack, local: s.Context, deadline: s.deadline})
	}))
	Default.Store("apply", NewFunc(2, func(s *State) {
		expr := InitListBuilder().Append(F(s.F()))
		s.L().Foreach(func(v Value) bool { expr = expr.Append(v.Quote()); return true })
		v, err := (*Context)(nil).Exec(s.Deadline(), expr.Build())
		s.assert(err == nil || s.panic("apply panic: %v", err))
		s.Out = v
	}))
	Default.Store("raise", NewFunc(1, func(s *State) { panic(s.In()) }))
	Default.Store("symbol->string", NewFunc(1, func(s *State) { s.Out = S(s.Y()) }))
	Default.Store("number->string", NewFunc(1, func(s *State) { s.Out = S(fmt.Sprint(s.Nv().V())) }))
	Default.Store("string->symbol", NewFunc(1, func(s *State) { s.Out = Y(s.S(), 0) }))
	Default.Store("string->error", NewFunc(1, func(s *State) { s.Out = V(fmt.Errorf(s.S())) }))
	Default.Store("string->number", NewFunc(1, func(s *State) { s.Out = ParseNumber(s.S()) }))
	Default.Store("error?", NewFunc(1, func(s *State) { _, ok := s.In().V().(error); s.Out = B(ok) }))
	Default.Store("null?", NewFunc(1, func(s *State) { s.Out = B(s.In().Type() == LIST && s.LastIn.L().MustProper().Empty()) }))
	Default.Store("list?", NewFunc(1, func(s *State) { s.Out = B(s.In().Type() == LIST && s.LastIn.L().IsProperList()) }))
	Default.Store("void?", NewFunc(1, func(s *State) { s.Out = B(s.In() == Void) }))
	Default.Store("pair?", NewFunc(1, func(s *State) { s.Out = B(s.In().Type() == LIST) }))
	Default.Store("symbol?", NewFunc(1, func(s *State) { s.Out = B(s.In().Type() == SYM) }))
	Default.Store("boolean?", NewFunc(1, func(s *State) { s.Out = B(s.In().Type() == BOOL) }))
	Default.Store("number?", NewFunc(1, func(s *State) { s.Out = B(s.In().Type() == NUM) }))
	Default.Store("string?", NewFunc(1, func(s *State) { s.Out = B(s.In().Type() == STR) }))
	Default.Store("stringify", NewFunc(1, func(s *State) { s.Out = S(s.In().String()) }))
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
		s.L().Foreach(func(v Value) bool {
			s.assert(v.Type() == LIST || s.panic("invalid binding list format: %v", v))
			b := v.L()
			s.assert(b.HasProperCdr() && b.val.Type() == SYM && b.val.S() != "" || s.panic("invalid binding list format: %v", v))
			tmpvar := Y(b.val.S()+"tmp", 0)
			innersets = append(innersets, L(Empty, setq, b.val, tmpvar))
			innerbinds = append(innerbinds, L(Empty, tmpvar, b.next.val))
			outerbinds = append(outerbinds, L(Empty, b.val, Void))
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
		let, binds := s.Caller.Y("let"), s.L().ToSlice()
		last := L(s.Args, s.Caller.Y("begin"))
		for i := len(binds) - 1; i >= 0; i-- {
			bd := binds[i]
			s.assert(bd.Type() == LIST || s.panic("invalid binding list format: %v", bd))
			lst := bd.L()
			s.assert(lst.HasProperCdr() && lst.val.Type() == SYM && lst.val.S() != "" || s.panic("invalid binding list format: %v", bd))
			last = L(Empty, let, L(Empty, bd), last)
		}
		s.Out = last
	}))
	Default.Store("define-modules", NewFunc(1|Vararg, func(s *State) {
	}))
	Default.Store("go->value", NewFunc(1, func(s *State) { s.Out = Vrec(s.In().V()) }))
	Default.Store("hash-new", NewFunc(Vararg, func(s *State) {
		m := map[string]Value{}
		for !s.Args.MustProper().Empty() {
			m[s.S()] = s.In()
		}
		s.Out = V(m)
	}))
	Default.Store("hash-set!", NewFunc(3, func(s *State) { s.InMap()[s.S()] = s.In() }))
	Default.Store("hash-delete!", NewFunc(2, func(s *State) { delete(s.InMap(), s.S()) }))
	Default.Store("hash-get", NewFunc(2, func(s *State) { s.Out = s.InMap()[s.S()] }))
	Default.Store("hash-contains?", NewFunc(2, func(s *State) { _, ok := s.InMap()[s.S()]; s.Out = B(ok) }))
	Default.Store("hash-keys", NewFunc(1, func(s *State) {
		ret := InitListBuilder()
		for i := range s.InMap() {
			ret = ret.Append(S(i))
		}
		s.Out = ret.Build()
	}))

	Default.Store("string-length", NewFunc(1, func(s *State) { s.Out = I(int64(len(s.S()))) }))
	Default.Store("substring?", NewFunc(2, func(s *State) { s.Out = B(strings.Contains(s.S(), s.S())) }))
	Default.Store("vector-bytes", NewFunc(1, func(s *State) { s.Out = V(make([]byte, s.Nv().I())) }))
	Default.Store("vector-strings", NewFunc(1, func(s *State) { s.Out = V(make([]string, s.Nv().I())) }))
	Default.Store("vector-ints", NewFunc(1, func(s *State) { s.Out = V(make([]int, s.Nv().I())) }))
	Default.Store("vector-int64s", NewFunc(1, func(s *State) { s.Out = V(make([]int64, s.Nv().I())) }))
	Default.Store("vector-len", NewFunc(1, func(s *State) { s.Out = I(int64((reflect.ValueOf(s.In().V()).Len()))) }))
	Default.Store("vector-null?", NewFunc(1, func(s *State) { s.Out = B(reflect.ValueOf(s.In().V()).Len() == 0) }))
	Default.Store("vector-nth", NewFunc(2, func(s *State) {
		rm := reflect.ValueOf(s.In().V())
		s.Out = V(rm.Index(int(s.Nv().I())).Interface())
	}))
	Default.Store("vector-set-nth!", NewFunc(3, func(s *State) {
		rm := reflect.ValueOf(s.In().V())
		rm.Index(int(s.Nv().I())).Set(s.In().TypedVal(rm.Type().Elem()))
	}))
	Default.Store("vector-slice", NewFunc(3, func(s *State) {
		rl := reflect.ValueOf(s.In().V())
		start, end := int(s.Nv().I()), int(s.Nv().I())
		s.Out = V(rl.Slice(start, end).Interface())
	}))
	Default.Store("vector-concat", NewFunc(2, func(s *State) {
		rv1, rv2 := reflect.ValueOf(s.In().V()), reflect.ValueOf(s.In().V())
		s.assert(rv1.Type() == rv2.Type() || s.panic("vector-concat: different type"))
		r := reflect.MakeSlice(rv1.Type(), rv1.Len(), rv1.Len()+rv2.Len())
		reflect.Copy(r, rv1)
		reflect.AppendSlice(r, rv2)
		s.Out = V(r.Interface())
	}))
	Default.Store("vector-foreach", NewFunc(2, func(s *State) {
		rl, fn := reflect.ValueOf(s.In().V()), s.F()
		for i := 0; i < rl.Len(); i++ {
			flag, err := fn.CallOnStack(s.Stack, s.Deadline(), L(Empty, I(int64(i)), V(rl.Index(i).Interface())))
			s.assert(err == nil || s.panic("invalid callback "))
			if flag.IsFalse() {
				break
			}
		}
	}))
	Default.Store("map", NewFunc(2, func(s *State) {
		fn, r, l, i := s.F(), []Value{}, s.L(), 0
		l.Foreach(func(h Value) bool {
			v, err := fn.CallOnStack(s.Stack, s.Deadline(), L(Empty, h))
			s.assert(err == nil || s.panic("map: error at element #%d: %v", i, err))
			r = append(r, v)
			i++
			return true
		})
		s.Out = L(Empty, r...)
	}))
	Default.Store("reduce", NewFunc(3, func(s *State) {
		fn, left, l, i := s.F(), s.In(), s.L(), 0
		var err error
		l.Foreach(func(h Value) bool {
			left, err = fn.CallOnStack(s.Stack, s.Deadline(), L(Empty, left, h))
			s.assert(err == nil || s.panic("reduce: error at element #%d: %v", i, err))
			i++
			return true
		})
		s.Out = left
	}))
	Default.Store("reduce-right", NewFunc(3, func(s *State) {
		fn, right, rl := s.F(), s.In(), s.L().ToSlice()
		var err error
		for i := len(rl) - 1; i >= 0; i-- {
			right, err = fn.CallOnStack(s.Stack, s.Deadline(), L(Empty, right, rl[i]))
			s.assert(err == nil || s.panic("reduce-right: error at element #%d: %v", i, err))
		}
		s.Out = right
	}))
	Default.Store("struct-get", NewFunc(1|Vararg, func(s *State) {
		rv := reflect.ValueOf(s.In().V())
		s.Args.Foreach(func(v Value) bool {
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
		rv := reflect.ValueOf(s.In().V())
		v := s.In()
		s.Args.Foreach(func(v Value) bool {
			if rv.Kind() == reflect.Ptr {
				rv = rv.Elem()
			}
			s.assert(v.Type() == SYM || s.panic("expect field name to be symbol: %v", v))
			rv = rv.FieldByName(v.S())
			return true
		})
		rv.Set(reflect.ValueOf(v.V()))
	}))
	Default.Store("display", NewFunc(Vararg, func(s *State) { fmt.Fprintln(DefaultStdout, L(s.Args).V().([]interface{})...) }))
	Default.Store("newline", NewFunc(0, func(s *State) { fmt.Fprintln(DefaultStdout) }))
	Default.Store("regex-match", NewFunc(2, func(s *State) {
		s.Out = B(regexp.MustCompile(s.S()).MatchString(s.S()))
	}))
	Default.Store("regex-find", NewFunc(3, func(s *State) {
		// s.Out = V(regexp.MustCompile(s.In(0, 's').S()).FindAllStringSubmatch(s.In(1, 's').S(), int(s.In(2, 'n').N())))
	}))
	Default.Store("json", NewFunc(1, func(s *State) {
		buf, err := json.MarshalIndent(s.In().V(), "", "  ")
		s.Out = ev2(string(buf), err)
	}))
	Default.Store("json-c", NewFunc(1, func(s *State) {
		buf, err := json.Marshal(s.In().V())
		s.Out = ev2(string(buf), err)
	}))
	Default.Store("json-parse", NewFunc(1, func(s *State) {
		text := strings.TrimSpace(s.S())
		if strings.HasPrefix(text, "{") {
			m := map[string]interface{}{}
			err := json.Unmarshal([]byte(text), &m)
			_ = err != nil && s.Out.of(V(err)) || s.Out.of(V(m))
		} else if strings.HasPrefix(text, "[") {
			m := []interface{}{}
			err := json.Unmarshal([]byte(text), &m)
			_ = err != nil && s.Out.of(V(err)) || s.Out.of(V(m))
		} else {
			var m interface{}
			err := json.Unmarshal([]byte(text), &m)
			_ = err != nil && s.Out.of(V(err)) || s.Out.of(V(m))
		}
	}))
	Default.Store("setf!", NewFunc(2|Macro, func(s *State) {
		a, v := s.Y(), s.In()
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
		a := s.Y()
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
					return I(v)
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
	Default.Store("sleep-milli", NewFunc(1, func(s *State) {
		d, t := s.Deadline(), time.Duration(s.I())*time.Millisecond
		if time.Now().Add(t).Before(d) {
			time.Sleep(t)
		}
	}))
	Default.Store("env", NewFunc(0, func(s *State) {
		l := InitListBuilder()
		for _, kv := range os.Environ() {
			p := strings.SplitN(kv, "=", 2)
			l = l.Append(L(Empty, S(p[0]), S(p[1])))
		}
		s.Out = l.Build()
	}))

	Default.Store("i64", NewFunc(1, func(s *State) { s.Out = s.In() }))
	Default.Store("u64", NewFunc(1, func(s *State) { *s.Out.A() = uint64(s.I()) }))

	// 	// SRFI-9
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
	if t == valueType {
		return reflect.ValueOf(v)
	}
	if v.Type() == LIST {
		s := reflect.MakeSlice(t, 0, 0)
		v.L().Foreach(func(v Value) bool { s = reflect.Append(s, v.TypedVal(t.Elem())); return true })
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

func ev2(v interface{}, err error) (e Value) {
	_ = err != nil && e.of(V(err)) || e.of(V(v))
	return
}

func (v Value) Add(v2 Value) (n Value) {
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
func Vrec(v interface{}) Value {
	rv := reflect.ValueOf(v)
	switch rv.Kind() {
	case reflect.Slice, reflect.Array:
		l := InitListBuilder()
		for i := 0; i < rv.Len(); i++ {
			l = l.Append(Vrec(rv.Index(i).Interface()))
		}
		return l.Build()
	}
	return V(v)
}
