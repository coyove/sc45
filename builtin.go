package scmbed

import (
	"bytes"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io"
	"os"
	"reflect"
	"regexp"
	"strconv"
	"strings"
	"time"
)

var DefaultStdout io.Writer = os.Stdout

func (s *State) InMap(i int) map[string]Value {
	v, ok := s.In(i, 'i').Val().(map[string]Value)
	s.assert(ok || s.panic("invalid argument #%d, expect map, got %v", i, s.Args[i]))
	return v
}

func (m *Context) String() string {
	p := bytes.NewBufferString("{")
	for k, v := range m.m {
		p.WriteString(strconv.Quote(k))
		p.WriteString(":")
		p.WriteString(v.String())
		p.WriteString(" ")
	}
	if p.Bytes()[p.Len()-1] == ' ' {
		p.Truncate(p.Len() - 1)
	}
	p.WriteString("}")
	if m.parent != nil {
		p.WriteString(" -> ")
		p.WriteString(m.parent.String())
	}
	return p.String()
}

func (ctx *Context) InstallGo(name string, fn interface{}) {
	rf, rt := reflect.ValueOf(fn), reflect.TypeOf(fn)
	ctx.assert(rf.Kind() == reflect.Func || ctx.panic("not func"))
	ctx.assert(rt.NumOut() <= 2 || ctx.panic("too many return values, expect 0, 1 or 2"))
	ctx.assert(rt.NumOut() < 2 || (rt.Out(1).Implements(reflect.TypeOf((*error)(nil)).Elem())) || ctx.panic("require func (...) (*, error)"))
	ctx.Install(name, func(s *State) {
		ins := make([]reflect.Value, 0, rt.NumIn())
		if rt.IsVariadic() {
			for i := 0; i < rt.NumIn()-1; i++ {
				ins = append(ins, s.In(i, 0).GoTypedValue(rt.In(i)))
			}
			for i := rt.NumIn() - 1; i < len(s.Args); i++ {
				ins = append(ins, s.In(i, 0).GoTypedValue(rt.In(rt.NumIn()-1).Elem()))
			}
		} else {
			for i := 0; i < rt.NumIn(); i++ {
				ins = append(ins, s.In(i, 0).GoTypedValue(rt.In(i)))
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

func (ctx *Context) Funcs() map[string]*Func {
	p := map[string]*Func{}
	for k, v := range ctx.m {
		if v.Type() == 'f' {
			p[k] = v.Fun()
		}
	}
	return p
}

func init() {
	Default.Install("#(letrec ((var1 val1) ... (varn valn)) expr...)", func(s *State) {
		/* Unwrap to:
		(let ((var1 ()) ... (varn ())                  // outer binds
			(let ((var1_tmp val1) ... (varn_tmp valn)) // inner binds
				(set! 'var1 var1_tmp)                  // inner sets
				...
				(set! 'varn varb_tmp)
				expr...                                // expressions
		*/
		let, binds := s.Caller.Make("let"), s.In(0, 'l').Lst()
		innersets := make([]Value, len(binds))
		innerbinds := make([]Value, len(binds))
		outerbinds := make([]Value, len(binds))
		for i := range binds {
			s.assert(binds[i].Type() == 'l' || s.panic("invalid binding list format: %v", binds[i]))
			b := binds[i].Lst()
			s.assert(len(b) == 2 && b[0].Type() == 'y' && b[0].Str() != "" || s.panic("invalid binding list format: %v", binds[i]))
			tmpvar := Sym(b[0].Str()+"tmp", 0, 0)
			innersets[i] = Lst(Sym("set!", 0, 0), b[0], tmpvar)
			innerbinds[i] = Lst(tmpvar, b[1])
			outerbinds[i] = Lst(b[0], Void)
		}
		inner := Lst(let, Lst(innerbinds...), _Vddd(innersets), _Vddd(s.Args[1:]))._flatten(true)
		outer := []Value{let, Lst(outerbinds...), Lst(inner...)}
		s.Out = Lst(outer...)
	})
	Default.Install("#(let* ((var1 val1) ... (varn valn)) expr...)", func(s *State) {
		/* Unwrap to:
		(let ((var1 val1)
			(let ((var2 val2))
				...
					expr...
		*/
		let, binds := s.Caller.Make("let"), s.In(0, 'l').Lst()
		last := begin(s.Caller, s.Args[1:]...)
		for i := len(binds) - 1; i >= 0; i-- {
			bd := binds[i]
			s.assert(bd.Type() == 'l' || s.panic("invalid binding list format: %v", bd))
			s.assert(bd._len() == 2 && bd._at(0).Type() == 'y' && bd._at(0).Str() != "" || s.panic("invalid binding list format: %v", bd))
			last = Lst(let, Lst(bd), begin(s.Caller, last))
		}
		s.Out = last
	})
	Default.Install("#(i64 @value)", func(s *State) {
		t, unsigned := strings.TrimPrefix(s.In(0, 'y').Str(), "@"), false
		if strings.HasPrefix(t, "u") {
			t, unsigned = t[1:], true
		}
		if unsigned {
			v, _ := strconv.ParseUint(t, 0, 64)
			s.Out = Val(v)
		} else {
			v, _ := strconv.ParseInt(t, 0, 64)
			s.Out = Val(v)
		}
	})
	Default.Install("(list-depth list)", func(s *State) { s.Out = Val(maxdepth(s.In(0, 'l').Lst())) })
	Default.Install("(go-value-wrap a)", func(s *State) { s.Out = ValRec(s.In(0, 0).Val()) })
	Default.Install("(map-new key0 value0 key1 value1 ...)", func(s *State) {
		m := map[string]Value{}
		for i := 0; i < len(s.Args); i += 2 {
			m[s.In(i, 's').Str()] = s.In(i+1, 0)
		}
		s.Out = Val(m)
	})
	Default.Install("(map-set! map key value)", func(s *State) { s.InMap(0)[s.In(1, 's').Str()] = s.In(2, 0) })
	Default.Install("(map-delete! map key)", func(s *State) { delete(s.InMap(0), s.In(1, 's').Str()) })
	Default.Install("(map-get map key)", func(s *State) { s.Out = s.InMap(0)[s.In(1, 's').Str()] })
	Default.Install("(map-contains map key)", func(s *State) { _, ok := s.InMap(0)[s.In(1, 's').Str()]; s.Out = Bln(ok) })
	Default.Install("(map-keys map)", func(s *State) {
		ret := make([]Value, 0, len(s.InMap(0)))
		for i := range s.InMap(0) {
			ret = append(ret, Str(i))
		}
		s.Out = Lst(ret...)
	})
	Default.Install("(skip n list)", func(s *State) {
		l := s.In(1, 'l').Lst()
		for i := 0; i < int(s.In(0, 'n').Num()); i++ {
			l, _ = Tail(l)
		}
		s.Out = Lst(l...)
	})
	Default.Install("#(lambda* (paramlist) body)", func(s *State) {
		tmpvar := "a" + strconv.FormatInt(time.Now().Unix(), 10)
		pl, body := s.In(0, 'l').Lst(), []Value{
			s.Caller.Make("lambda"),
			s.Caller.Make(tmpvar),
			Lst(s.Caller.Make("define"), s.Caller.Make(tmpvar+"-len"), Lst(
				s.Caller.Make("vector-len"), s.Caller.Make(tmpvar),
			)),
		}
		/*
			(lambda* (a0 a1 ... an) body) =>
			(lambda axxx (begin
				(define axxx-len (vector-len args))
				(define a0 (if (< 0 axxx-len) (vector-nth args 0) a0-expr))
				...
				(define an (if (< n axxx-len) (vector-nth args n) an-expr))
				body
		*/
		for i := range pl {
			var name, val Value
			if pl[i].Type() == 'y' {
				name, val = pl[i], Empty
				if a := pl[i].Str(); strings.HasSuffix(a, "...") {
					// Special case: "name..." to catch the rest arguments
					body = append(body, Lst(
						s.Caller.Make("define"),
						s.Caller.Make(ifstr(len(a) == 3, "...", a[:len(a)-3])),
						Lst(s.Caller.Make("skip"), Num(float64(i)), s.Caller.Make(tmpvar)),
					))
					continue
				}
			} else {
				s.assert(pl[i].Type() == 'l' && pl[i]._len() == 2 || s.panic("invalid binding list: %v", pl[i]))
				name, val = pl[i]._at(0), pl[i]._at(1)
			}
			body = append(body, Lst(
				s.Caller.Make("define"),
				name,
				Lst(
					s.Caller.Make("if"),
					Lst(s.Caller.Make("<"), Num(float64(i)), s.Caller.Make(tmpvar+"-len")),
					Lst(s.Caller.Make("vector-nth"), s.Caller.Make(tmpvar), Num(float64(i))),
					val,
				),
			))
		}
		body = append(body, s.Args[1:]...)
		s.Out = Lst(body...)
	})
	Default.Install("(vector-bytes n)", func(s *State) { s.Out = Val(make([]byte, int(s.In(0, 'n').Num()))) })
	Default.Install("(vector-strings n)", func(s *State) { s.Out = Val(make([]string, int(s.In(0, 'n').Num()))) })
	Default.Install("(vector-ints n)", func(s *State) { s.Out = Val(make([]int, int(s.In(0, 'n').Num()))) })
	Default.Install("(vector-int64s n)", func(s *State) { s.Out = Val(make([]int64, int(s.In(0, 'n').Num()))) })
	Default.Install("(vector-len a)", func(s *State) { s.Out = Num(float64((reflect.ValueOf(s.In(0, 0).Val()).Len()))) })
	Default.Install("(vector-null? a)", func(s *State) { s.Out = Bln(reflect.ValueOf(s.In(0, 0).Val()).Len() == 0) })
	Default.Install("(vector-nth vector n)", func(s *State) {
		rm := reflect.ValueOf(s.In(0, 0).Val())
		s.Out = Val(rm.Index(int(s.In(1, 'n').Num())).Interface())
	})
	Default.Install("(vector-set-nth! vector n value)", func(s *State) {
		rm := reflect.ValueOf(s.In(0, 0).Val())
		rm.Index(int(s.In(1, 'n').Num())).Set(s.In(2, 0).GoTypedValue(rm.Type().Elem()))
	})
	Default.Install("(vector-slice vector start end?)", func(s *State) {
		rl := reflect.ValueOf(s.In(0, 0).Val())
		start, end := int(s.In(1, 'n').Num()), rl.Len()
		if len(s.Args) == 3 {
			end = int(s.In(2, 'n').Num())
		}
		s.Out = Val(rl.Slice(start, end).Interface())
	})
	Default.Install("(vector-concat v1 v2)", func(s *State) {
		rv1, rv2 := reflect.ValueOf(s.In(0, 0).Val()), reflect.ValueOf(s.In(1, 0).Val())
		s.assert(rv1.Type() == rv2.Type() || s.panic("vector-concat: different type"))
		r := reflect.MakeSlice(rv1.Type(), rv1.Len(), rv1.Len()+rv2.Len())
		reflect.Copy(r, rv1)
		reflect.AppendSlice(r, rv2)
		s.Out = Val(r.Interface())
	})
	Default.Install("(vector-foreach vector callback)", func(s *State) {
		rl, fn := reflect.ValueOf(s.In(0, 0).Val()), s.In(1, 'f')
		for i := 0; i < rl.Len(); i++ {
			flag, err := fn.Fun().Call(Num(float64(i)), Val(rl.Index(i).Interface()))
			s.assert(err == nil || s.panic("invalid callback "))
			if !flag.IsTrue() {
				break
			}
		}
	})
	Default.Install("(define-record 'name 'field1 ... 'fieldn)", func(s *State) {
		name, fields, typename := s.In(0, 'y').Str(), make(map[string]int, len(s.Args)-1), new(int)
		for i := 1; i < len(s.Args); i++ {
			fields[s.In(i, 'y').Str()] = i
			func(i int) {
				name := name + "-" + s.In(i, 'y').Str()

				s.Context.Store(name, Fun(&Func{f: func(ss *State) { // getter
					ss.assert(len(ss.In(0, 'l').Lst()) == len(s.Args) && ss.In(0, 'l').Lst()[0].Val() == typename || ss.panic("not a %s record", name))
					ss.Out = ss.In(0, 'l').Lst()[i]
				}, sig: "(" + name + " r)"}))

				s.Context.Store(name+"-set!", Fun(&Func{f: func(ss *State) { // setter
					ss.assert(len(ss.In(0, 'l').Lst()) == len(s.Args) && ss.In(0, 'l').Lst()[0].Val() == typename || ss.panic("not a %s record", name))
					ss.In(0, 'l').Lst()[i] = ss.In(1, 0) // setter
				}, sig: "(" + name + "-set! r value)"}))
			}(i)
		}

		s.Context.Store(name+"?", Fun(&Func{f: func(ss *State) {
			ss.Out = Bln(len(ss.In(0, 'l').Lst()) == len(s.Args) && ss.In(0, 'l').Lst()[0].Val() == typename)
		}, sig: "(" + name + "? a)"}))

		s.Context.Store(name+"-new", Fun(&Func{f: func(ss *State) {
			out := make([]Value, len(s.Args))
			out[0] = Val(typename)
			for i := 1; i < len(out); i++ {
				out[i] = Void
			}
			for i := 0; i < len(ss.Args); i += 2 {
				fieldname := ss.In(i, 'y').Str()
				ss.assert(fields[fieldname] != 0 || ss.panic("field %s not found", fieldname))
				out[fields[fieldname]] = ss.In(i+1, 0)
			}
			ss.Out = Lst(out...)
		}, sig: "(" + name + "-new ...)"}))
	})
	Default.Install("(map fn list)", func(s *State) {
		l, r, fn, i := s.In(1, 'l').Lst(), []Value{}, s.In(0, 'f'), 0
		for h, ok := Head(l, false, nil); ok; h, ok = Head(l, false, nil) {
			v, err := fn.Fun().Call(h)
			s.assert(err == nil || s.panic("map: error at element #%d: %v", i, err))
			r = append(r, v)
			l, _ = Tail(l)
			i++
		}
		s.Out = Lst(r...)
	})
	Default.Install("(reduce fn v list)", func(s *State) {
		l, left, fn, i := s.In(2, 'l').Lst(), s.In(1, 0), s.In(0, 'f'), 0
		var err error
		for h, ok := Head(l, false, nil); ok; h, ok = Head(l, false, nil) {
			left, err = fn.Fun().Call(left, h)
			s.assert(err == nil || s.panic("reduce: error at element #%d: %v", i, err))
			l, _ = Tail(l)
			i++
		}
		s.Out = left
	})
	Default.Install("(reduce-right fn v list)", func(s *State) {
		i, rl, right, fn := 0, s.In(2, 'l').Lst(), s.In(1, 0), s.In(0, 'f')
		var err error
		for l, ok := Head(rl, true, nil); ok; l, ok = Head(rl, true, nil) {
			right, err = fn.Fun().Call(right, l)
			s.assert(err == nil || s.panic("reduce-right: error at element #%d: %v", i, err))
			rl, _ = Init(rl)
			i++
		}
		s.Out = right
	})
	Default.Install("#(cond (cond1 stat1) (cond2 stat2) ... (else catch-all)?)", func(s *State) {
		if len(s.Args) == 0 {
			s.Out = s.Caller.Make("true")
			return
		}
		build := func(expr Value) []Value {
			s.assert(expr.Type() == 'l' && expr._len() == 2 || s.panic("invalid cond statement: %v", expr))
			cond, stat := expr.Lst()[0], expr.Lst()[1]
			if cond.Type() == 'y' && cond.Str() == "else" {
				cond = s.Caller.Make("true")
			}
			return []Value{s.Caller.Make("if"), cond, stat, Void}
		}
		exprs := build(s.In(0, 0))
		for i, head := 1, exprs; i < len(s.Args); i++ {
			tail := build(s.In(i, 0))
			head[3] = Lst(tail...)
			head = tail
		}
		s.Out = Lst(exprs...)
	})
	// 	Default.Install("(eq any any...)", func(s *State) {
	// 		s.Out = true
	// 		for i, a := 1, s.In(0, 0); i < len(s.Args); i++ {
	// 			s.Out = s.Out.(bool) && reflect.DeepEqual(a, s.Args[i])
	// 		}
	// 	})
	Default.Install("(struct-get 'field1 ... 'fieldn struct)", func(s *State) {
		rv := reflect.ValueOf(s.In(len(s.Args)-1, 0).Val())
		for i := 0; i < len(s.Args)-1; i++ {
			m := s.In(i, 'y').Str()
			if rv.Kind() == reflect.Ptr {
				rv = rv.Elem()
			}
			tmp := rv.FieldByName(m)
			if i < len(s.Args)-1-1 { // not last atom
				s.assert(tmp.IsValid() || s.panic("field %q not found", m))
				rv = tmp
				continue
			}
			if tmp.IsValid() {
				s.Out = Val(tmp.Interface())
				return
			}
			tmp = rv.MethodByName(m)
			if !tmp.IsValid() {
				tmp = rv.Addr().MethodByName(m)
			}
			s.assert(tmp.IsValid() || s.panic("method %q not found", m))
			rv = tmp
		}
		s.Out = Val(rv.Interface())
	})
	Default.Install("(struct-set! 'field1 ... 'fieldn value struct)", func(s *State) {
		v := s.In(len(s.Args)-2, 0)
		f := reflect.ValueOf(s.In(len(s.Args)-1, 0).Val())
		if f.Kind() == reflect.Ptr {
			f = f.Elem()
		}
		for i := 0; i < len(s.Args)-2; i++ {
			m := s.In(i, 'y').Str()
			f = f.FieldByName(m)
			if i != len(s.Args)-3 { // not last atom
				s.assert(f.IsValid() || s.panic("field %q not found", m))
				continue
			}
			f.Set(v.GoTypedValue(f.Type()))
		}
	})
	Default.Install("(^ string...)", func(s *State) {
		p := bytes.Buffer{}
		for i := range s.Args {
			p.WriteString(s.In(i, 's').Str())
		}
		s.Out = Str(p.String())
	})
	Default.Install("(println any...)", func(s *State) { fmt.Fprintln(DefaultStdout, vlisttointerface(s.Args)...) })
	Default.Install("(print any...)", func(s *State) { fmt.Fprint(DefaultStdout, vlisttointerface(s.Args)...) })
	Default.Install("(printf format any...)", func(s *State) { fmt.Fprintf(DefaultStdout, s.In(0, 's').Str(), vlisttointerface(s.Args[1:])...) })
	Default.Install("(regex/match regexp text)", func(s *State) {
		s.Out = Bln(regexp.MustCompile(s.In(0, 's').Str()).MatchString(s.In(1, 's').Str()))
	})
	Default.Install("(regex/find regexp text count)", func(s *State) {
		s.Out = ValRec(regexp.MustCompile(s.In(0, 's').Str()).FindAllStringSubmatch(s.In(1, 's').Str(), int(s.In(2, 'n').Num())))
	})
	Default.Install("(json a)", func(s *State) {
		buf, err := json.MarshalIndent(s.In(0, 0), "", "  ")
		s.Out = errorOrValue(string(buf), err)
	})
	Default.Install("(json-c a)", func(s *State) {
		buf, err := json.Marshal(s.In(0, 0))
		s.Out = errorOrValue(string(buf), err)
	})
	Default.Install("(json-parse string)",
		func(s *State) {
			text := strings.TrimSpace(s.In(0, 's').Str())
			if strings.HasPrefix(text, "{") {
				m := map[string]interface{}{}
				if err := json.Unmarshal([]byte(text), &m); err != nil {
					s.Out = Val(err)
				} else {
					s.Out = ValRec(m)
				}
			} else if strings.HasPrefix(text, "[") {
				m := []interface{}{}
				if err := json.Unmarshal([]byte(text), &m); err != nil {
					s.Out = Val(err)
				} else {
					s.Out = ValRec(m)
				}
			} else {
				var m interface{}
				if err := json.Unmarshal([]byte(text), &m); err != nil {
					s.Out = Val(err)
				} else {
					s.Out = Val(m)
				}
			}
		})
	Default.Install("#(setf! structname.Field1.Field2...Fieldn value)",
		func(s *State) {
			a := s.In(0, 'y').Str()
			parts := strings.Split(a, ".")
			s.assert(len(parts) > 1 || s.panic("too few fields to set"))
			structname := parts[0]
			setter := []Value{s.In(0, 0).Make("struct-set!")}
			for i := 1; i < len(parts); i++ {
				setter = append(setter, _Vquote(s.In(0, 0).Make(parts[i])))
			}
			setter = append(setter, s.In(1, 0), s.In(0, 0).Make(structname))
			s.Out = Lst(setter...)
		})
	Default.Install("#(getf structname.Field1.Field2...Fieldn)",
		func(s *State) {
			a := s.In(0, 'y').Str()
			parts := strings.Split(a, ".")
			s.assert(len(parts) > 1 || s.panic("too few fields to get"))
			structname := parts[0]
			setter := []Value{s.In(0, 0).Make("struct-get")}
			for i := 1; i < len(parts); i++ {
				setter = append(setter, _Vquote(s.In(0, 0).Make(parts[i])))
			}
			setter = append(setter, s.In(0, 0).Make(structname))
			s.Out = Lst(setter...)
		})

	// 	// 	Default.Install("write-file",
	// 	// 		"write data to file, 'json or 'j if needed",
	// 	// 		func(fn string, a interface{}, t OptAtom) error {
	// 	// 			var buf []byte
	// 	// 			switch t.A.v {
	// 	// 			case "j":
	// 	// 				buf, _ = json.Marshal(a)
	// 	// 			case "json":
	// 	// 				buf, _ = json.MarshalIndent(a, "", "  ")
	// 	// 			default:
	// 	// 				buf = []byte(fmt.Sprint(a))
	// 	// 			}
	// 	// 			return ioutil.WriteFile(fn, buf, 0777)
	// 	// 		})
	// 	//
	// 	// 	Default.Install("read-file", "read data from file", func(fn string) (string, error) {
	// 	// 		buf, err := ioutil.ReadFile(fn)
	// 	// 		return string(buf), err
	// 	// 	})
	Default.Install("#($ any...)",
		func(s *State) {
			v := Lst(s.Args...).String()
			expr, err := parser.ParseExpr(v)
			if err != nil {
				panic(err)
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
					return Lst(Sym(op, 0, 0), do(e.X))
				case *ast.BinaryExpr:
					op := e.Op.String()
					switch e.Op {
					case token.LAND:
						op = "and"
					case token.LOR:
						op = "or"
					}
					m := Lst(Sym(op, 0, 0), do(e.X), do(e.Y))
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
					return Lst(r...)
				}
				panic(fmt.Errorf("$: %T not supported", e))
			}
			s.Out = do(expr)
		})
}

func (v Value) GoTypedValue(t reflect.Type) reflect.Value {
	vv := v.Val()
	if vv == nil {
		return reflect.Zero(t)
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

func maxdepth(v []Value) int {
	d := 1
	for _, e := range v {
		if e.Type() != 'd' {
			continue
		}
		if x := 1 + maxdepth(e.Lst()); x > d {
			d = x
		}
	}
	return d
}

func Range(v []Value, fn func(int, Value) (Value, bool)) { _range(0, v, fn) }

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
