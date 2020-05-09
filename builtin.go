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
	v, ok := s.Int(i, 'i').Val().(map[string]Value)
	s.assert(ok || s.panic("invalid argument #%d, expect map, got %v", i, s.Args[i]))
	return v
}

func (m *Map) String() string {
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

func (it *Interpreter) InstallGo(name string, fn interface{}) {
	rf, rt := reflect.ValueOf(fn), reflect.TypeOf(fn)
	it.assert(rf.Kind() == reflect.Func || it.panic("not func"))
	it.assert(rt.NumOut() <= 2 || it.panic("too many return values, expect 0, 1 or 2"))
	it.assert(rt.NumOut() < 2 || (rt.Out(1).Implements(reflect.TypeOf((*error)(nil)).Elem())) || it.panic("require func (...) (*, error)"))
	it.Install(name, func(s *State) {
		ins := make([]reflect.Value, 0, rt.NumIn())
		if rt.IsVariadic() {
			for i := 0; i < rt.NumIn()-1; i++ {
				ins = append(ins, s.In(i).GoTypedValue(rt.In(i)))
			}
			for i := rt.NumIn() - 1; i < len(s.Args); i++ {
				ins = append(ins, s.In(i).GoTypedValue(rt.In(rt.NumIn()-1).Elem()))
			}
		} else {
			for i := 0; i < rt.NumIn(); i++ {
				ins = append(ins, s.In(i).GoTypedValue(rt.In(i)))
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

func (it *Interpreter) Funcs() map[string]*Func {
	p := map[string]*Func{}
	for k, v := range it.Globals.Unsafe() {
		if v.Type() == 'f' {
			p[k] = v.Fun()
		}
	}
	return p
}

func init() {
	predefined.Install("#(i64 @value)", func(s *State) {
		t, unsigned, base := strings.ToLower(s.Int(0, 'a').Str()), false, 10
		if strings.HasPrefix(t, "u") {
			t, unsigned = t[1:], true
		}
		switch t[0] {
		case 'x':
			base = 16
		case 'o':
			base = 8
		case 'b':
			base = 2
		}
		if unsigned {
			v, _ := strconv.ParseUint(strings.TrimLeft(t, "udxob"), base, 64)
			s.Out = Val(v)
		} else {
			v, _ := strconv.ParseInt(strings.TrimLeft(t, "udxob"), base, 64)
			s.Out = Val(v)
		}
	})
	predefined.Install("(list-depth list)", func(s *State) { s.Out = Val(maxdepth(s.Int(0, 'l').Lst())) })
	predefined.Install("(go-value-wrap a)", func(s *State) { s.Out = ValRec(s.In(0).Val()) })
	predefined.Install("(map-new key0 value0 key1 value1 ...)", func(s *State) {
		m := map[string]Value{}
		for i := 0; i < len(s.Args); i += 2 {
			m[s.Int(i, 's').Str()] = s.In(i + 1)
		}
		s.Out = Val(m)
	})
	predefined.Install("(map-set! map key value)", func(s *State) { s.InMap(0)[s.Int(1, 's').Str()] = s.In(2) })
	predefined.Install("(map-delete! map key)", func(s *State) { delete(s.InMap(0), s.Int(1, 's').Str()) })
	predefined.Install("(map-get map key)", func(s *State) { s.Out = s.InMap(0)[s.Int(1, 's').Str()] })
	predefined.Install("(map-contains map key)", func(s *State) { _, ok := s.InMap(0)[s.Int(1, 's').Str()]; s.Out = Bln(ok) })
	predefined.Install("(map-keys map)", func(s *State) {
		ret := make([]Value, 0, len(s.InMap(0)))
		for i := range s.InMap(0) {
			ret = append(ret, Str(i))
		}
		s.Out = Lst(ret...)
	})
	predefined.Install("(skip n list)", func(s *State) {
		l := s.Int(1, 'l').Lst()
		for i := 0; i < int(s.Int(0, 'n').Num()); i++ {
			l, _ = Tail(l)
		}
		s.Out = Lst(l...)
	})
	predefined.Install("#(lambda* (paramlist) body)", func(s *State) {
		tmpvar := "a" + strconv.FormatInt(time.Now().Unix(), 10)
		pl, body := s.Int(0, 'l').Lst(), []Value{
			s.Caller.Rename("lambda"),
			s.Caller.Rename(tmpvar),
			Lst(s.Caller.Rename("define"), s.Caller.Rename(tmpvar+"-len"), Lst(
				s.Caller.Rename("vector-len"), s.Caller.Rename(tmpvar),
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
			if a, ok := pl[i]._atm(); ok {
				name, val = pl[i], Empty
				if strings.HasSuffix(a, "...") {
					// Special case: "name..." to catch the rest arguments
					body = append(body, Lst(
						s.Caller.Rename("define"),
						s.Caller.Rename(ifstr(len(a) == 3, "...", a[:len(a)-3])),
						Lst(s.Caller.Rename("skip"), Num(float64(i)), s.Caller.Rename(tmpvar)),
					))
					continue
				}
			} else {
				s.assert(pl[i].Type() == 'l' && pl[i]._len() == 2 || s.panic("invalid binding list: %v", pl[i]))
				name, val = pl[i]._at(0), pl[i]._at(1)
			}
			body = append(body, Lst(
				s.Caller.Rename("define"),
				name,
				Lst(
					s.Caller.Rename("if"),
					Lst(s.Caller.Rename("<"), Num(float64(i)), s.Caller.Rename(tmpvar+"-len")),
					Lst(s.Caller.Rename("vector-nth"), s.Caller.Rename(tmpvar), Num(float64(i))),
					val,
				),
			))
		}
		body = append(body, s.Args[1:]...)
		s.Out = Lst(body...)
	})
	predefined.Install("(vector-bytes n)", func(s *State) { s.Out = Val(make([]byte, int(s.Int(0, 'n').Num()))) })
	predefined.Install("(vector-strings n)", func(s *State) { s.Out = Val(make([]string, int(s.Int(0, 'n').Num()))) })
	predefined.Install("(vector-ints n)", func(s *State) { s.Out = Val(make([]int, int(s.Int(0, 'n').Num()))) })
	predefined.Install("(vector-int64s n)", func(s *State) { s.Out = Val(make([]int64, int(s.Int(0, 'n').Num()))) })
	predefined.Install("(vector-len a)", func(s *State) { s.Out = Num(float64((reflect.ValueOf(s.In(0).Val()).Len()))) })
	predefined.Install("(vector-null? a)", func(s *State) { s.Out = Bln(reflect.ValueOf(s.In(0).Val()).Len() == 0) })
	predefined.Install("(vector-nth vector n)", func(s *State) {
		rm := reflect.ValueOf(s.In(0).Val())
		s.Out = Val(rm.Index(int(s.Int(1, 'n').Num())).Interface())
	})
	predefined.Install("(vector-set-nth! vector n value)", func(s *State) {
		rm := reflect.ValueOf(s.In(0).Val())
		rm.Index(int(s.Int(1, 'n').Num())).Set(s.In(2).GoTypedValue(rm.Type().Elem()))
	})
	predefined.Install("(vector-slice vector start end?)", func(s *State) {
		rl := reflect.ValueOf(s.In(0).Val())
		start, end := int(s.Int(1, 'n').Num()), rl.Len()
		if len(s.Args) == 3 {
			end = int(s.Int(2, 'n').Num())
		}
		s.Out = Val(rl.Slice(start, end).Interface())
	})
	predefined.Install("(vector-concat v1 v2)", func(s *State) {
		rv1, rv2 := reflect.ValueOf(s.In(0).Val()), reflect.ValueOf(s.In(1).Val())
		s.assert(rv1.Type() == rv2.Type() || s.panic("vector-concat: different type"))
		r := reflect.MakeSlice(rv1.Type(), rv1.Len(), rv1.Len()+rv2.Len())
		reflect.Copy(r, rv1)
		reflect.AppendSlice(r, rv2)
		s.Out = Val(r.Interface())
	})
	predefined.Install("(vector-foreach vector callback)", func(s *State) {
		rl, fn := reflect.ValueOf(s.In(0).Val()), s.InFunc(1)
		for i := 0; i < rl.Len(); i++ {
			fn(Num(float64(i)), Val(rl.Index(i).Interface()))
		}
	})
	predefined.Install("(define-record 'name 'field1 ... 'fieldn)", func(s *State) {
		name, fields, typename := s.Int(0, 'a').Str(), make(map[string]int, len(s.Args)-1), new(int)
		for i := 1; i < len(s.Args); i++ {
			fields[s.Int(i, 'a').Str()] = i
			func(i int) {
				name := name + "-" + s.Int(i, 'a').Str()

				s.Map.Store(name, Fun(&Func{f: func(ss *State) { // getter
					ss.assert(len(ss.Int(0, 'l').Lst()) == len(s.Args) && ss.Int(0, 'l').Lst()[0].Val() == typename || ss.panic("not a %s record", name))
					ss.Out = ss.Int(0, 'l').Lst()[i]
				}, sig: "(" + name + " r)"}))

				s.Map.Store(name+"-set!", Fun(&Func{f: func(ss *State) { // setter
					ss.assert(len(ss.Int(0, 'l').Lst()) == len(s.Args) && ss.Int(0, 'l').Lst()[0].Val() == typename || ss.panic("not a %s record", name))
					ss.Int(0, 'l').Lst()[i] = ss.In(1) // setter
				}, sig: "(" + name + "-set! r value)"}))
			}(i)
		}

		s.Map.Store(name+"?", Fun(&Func{f: func(ss *State) {
			ss.Out = Bln(len(ss.Int(0, 'l').Lst()) == len(s.Args) && ss.Int(0, 'l').Lst()[0].Val() == typename)
		}, sig: "(" + name + "? a)"}))

		s.Map.Store(name+"-new", Fun(&Func{f: func(ss *State) {
			out := make([]Value, len(s.Args))
			out[0] = Val(typename)
			for i := 1; i < len(out); i++ {
				out[i] = Void
			}
			for i := 0; i < len(ss.Args); i += 2 {
				fieldname := ss.Int(i, 'a').Str()
				ss.assert(fields[fieldname] != 0 || ss.panic("field %s not found", fieldname))
				out[fields[fieldname]] = ss.In(i + 1)
			}
			ss.Out = Lst(out...)
		}, sig: "(" + name + "-new ...)"}))
	})
	predefined.Install("(map fn list)", func(s *State) {
		l, r, fn, i := s.Int(1, 'l').Lst(), []Value{}, s.InFunc(0), 0
		for h, ok := Head(l, nil); ok; h, ok = Head(l, nil) {
			v, err := fn(h)
			s.assert(err == nil || s.panic("map: error at element #%d: %v", i, err))
			r = append(r, v)
			l, _ = Tail(l)
			i++
		}
		s.Out = Lst(r...)
	})
	predefined.Install("(reduce fn v list)", func(s *State) {
		l, left, fn, i := s.Int(2, 'l').Lst(), s.In(1), s.InFunc(0), 0
		var err error
		for h, ok := Head(l, nil); ok; h, ok = Head(l, nil) {
			left, err = fn(left, h)
			s.assert(err == nil || s.panic("reduce: error at element #%d: %v", i, err))
			l, _ = Tail(l)
			i++
		}
		s.Out = left
	})
	predefined.Install("(reduce-right fn v list)", func(s *State) {
		i, rl, right, fn := 0, s.Int(2, 'l').Lst(), s.In(1), s.InFunc(0)
		var err error
		for l, ok := Last(rl, nil); ok; l, ok = Last(rl, nil) {
			right, err = fn(right, l)
			s.assert(err == nil || s.panic("reduce-right: error at element #%d: %v", i, err))
			rl, _ = Init(rl)
			i++
		}
		s.Out = right
	})
	predefined.Install("#(cond (cond1 stat1) (cond2 stat2) ... (else catch-all)?)", func(s *State) {
		if len(s.Args) == 0 {
			s.Out = s.Caller.Rename("true")
			return
		}
		build := func(expr Value) []Value {
			s.assert(expr.Type() == 'l' && expr._len() == 2 || s.panic("invalid cond statement: %v", expr))
			cond, stat := expr.Lst()[0], expr.Lst()[1]
			if a, ok := cond._atm(); ok && a == "else" {
				cond = s.Caller.Rename("true")
			}
			return []Value{s.Caller.Rename("if"), cond, stat, Void}
		}
		exprs := build(s.In(0))
		for i, head := 1, exprs; i < len(s.Args); i++ {
			tail := build(s.In(i))
			head[3] = Lst(tail...)
			head = tail
		}
		s.Out = Lst(exprs...)
	})
	// 	predefined.Install("(eq any any...)", func(s *State) {
	// 		s.Out = true
	// 		for i, a := 1, s.In(0); i < len(s.Args); i++ {
	// 			s.Out = s.Out.(bool) && reflect.DeepEqual(a, s.Args[i])
	// 		}
	// 	})
	predefined.Install("(struct-get 'field1 ... 'fieldn struct)", func(s *State) {
		rv := reflect.ValueOf(s.In(len(s.Args) - 1).Val())
		for i := 0; i < len(s.Args)-1; i++ {
			m := s.Int(i, 'a').Str()
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
	predefined.Install("(struct-set! 'field1 ... 'fieldn value struct)", func(s *State) {
		v := s.In(len(s.Args) - 2)
		f := reflect.ValueOf(s.In(len(s.Args) - 1).Val())
		if f.Kind() == reflect.Ptr {
			f = f.Elem()
		}
		for i := 0; i < len(s.Args)-2; i++ {
			m := s.Int(i, 'a').Str()
			f = f.FieldByName(m)
			if i != len(s.Args)-3 { // not last atom
				s.assert(f.IsValid() || s.panic("field %q not found", m))
				continue
			}
			f.Set(v.GoTypedValue(f.Type()))
		}
	})
	predefined.Install("(^ string...)", func(s *State) {
		p := bytes.Buffer{}
		for i := range s.Args {
			p.WriteString(s.Int(i, 's').Str())
		}
		s.Out = Str(p.String())
	})
	predefined.Install("(println any...)", func(s *State) { fmt.Fprintln(DefaultStdout, vlisttointerface(s.Args)...) })
	predefined.Install("(print any...)", func(s *State) { fmt.Fprint(DefaultStdout, vlisttointerface(s.Args)...) })
	predefined.Install("(printf format any...)", func(s *State) { fmt.Fprintf(DefaultStdout, s.Int(0, 's').Str(), vlisttointerface(s.Args[1:])...) })
	predefined.Install("(regex/match regexp text)", func(s *State) {
		s.Out = Bln(regexp.MustCompile(s.Int(0, 's').Str()).MatchString(s.Int(1, 's').Str()))
	})
	predefined.Install("(regex/find regexp text count)", func(s *State) {
		s.Out = ValRec(regexp.MustCompile(s.Int(0, 's').Str()).FindAllStringSubmatch(s.Int(1, 's').Str(), int(s.Int(2, 'n').Num())))
	})
	predefined.Install("(json a)", func(s *State) {
		buf, err := json.MarshalIndent(s.In(0), "", "  ")
		s.Out = errorOrValue(string(buf), err)
	})
	predefined.Install("(json-c a)", func(s *State) {
		buf, err := json.Marshal(s.In(0))
		s.Out = errorOrValue(string(buf), err)
	})
	predefined.Install("(json-parse string)",
		func(s *State) {
			text := strings.TrimSpace(s.Int(0, 's').Str())
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
	predefined.Install("#(setf! structname.Field1.Field2...Fieldn value)",
		func(s *State) {
			a := s.Int(0, 'a').Str()
			parts := strings.Split(a, ".")
			s.assert(len(parts) > 1 || s.panic("too few fields to set"))
			structname := parts[0]
			setter := []Value{s.In(0).Rename("struct-set!")}
			for i := 1; i < len(parts); i++ {
				setter = append(setter, _Vquote(s.In(0).Rename(parts[i])))
			}
			setter = append(setter, s.In(1), s.In(0).Rename(structname))
			s.Out = Lst(setter...)
		})
	predefined.Install("#(getf structname.Field1.Field2...Fieldn)",
		func(s *State) {
			a := s.Int(0, 'a').Str()
			parts := strings.Split(a, ".")
			s.assert(len(parts) > 1 || s.panic("too few fields to get"))
			structname := parts[0]
			setter := []Value{s.In(0).Rename("struct-get")}
			for i := 1; i < len(parts); i++ {
				setter = append(setter, _Vquote(s.In(0).Rename(parts[i])))
			}
			setter = append(setter, s.In(0).Rename(structname))
			s.Out = Lst(setter...)
		})

	// 	// 	predefined.Install("write-file",
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
	// 	// 	predefined.Install("read-file", "read data from file", func(fn string) (string, error) {
	// 	// 		buf, err := ioutil.ReadFile(fn)
	// 	// 		return string(buf), err
	// 	// 	})
	predefined.Install("#($ any...)",
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
					return Lst(Atm(op, 0, 0), do(e.X))
				case *ast.BinaryExpr:
					op := e.Op.String()
					switch e.Op {
					case token.LAND:
						op = "and"
					case token.LOR:
						op = "or"
					}
					m, _ := s.It.UnwrapMacro([]Value{Atm(op, 0, 0), do(e.X), do(e.Y)})
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
					return Atm(e.Name, 0, 0)
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
