package scmbed

import (
	"bytes"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io"
	"io/ioutil"
	"net/http"
	"os"
	"reflect"
	"regexp"
	"strconv"
	"strings"
	"syscall"
	"time"
	"unicode"
)

var DefaultStdout io.Writer = os.Stdout

func (s *State) InMap(i int) *Map {
	vv, _ := s.In(i).Itf()
	v, ok := vv.(*Map)
	s.assert(ok || s.panic("invalid argument at %d, expect map, got %v", i, s.Args[i]))
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
				s.Out = VInterface(err)
			} else {
				s.Out = Val(outs[0].Interface())
			}
		}
	})
}

func init() {
	predefined.Install("#(i64 @value)", func(s *State) {
		t, unsigned, base := strings.ToLower(s.InAtom(0)), false, 10
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
			s.Out = VInterface(v)
		} else {
			v, _ := strconv.ParseInt(strings.TrimLeft(t, "udxob"), base, 64)
			s.Out = VInterface(v)
		}
	})
	predefined.Install("(list-depth list)", func(s *State) { s.Out = Val(maxdepth(s.InList(0))) })
	predefined.Install("(go-value-wrap a)", func(s *State) { s.Out = ValRec(s.In(0).GoValue()) })
	predefined.Install("(map-new key0 value0 key1 value1 ...)", func(s *State) {
		m := &Map{}
		for i := 0; i < len(s.Args); i += 2 {
			m.set(s.InString(i), s.In(i+1))
		}
		s.Out = VInterface(m)
	})
	predefined.Install("(map-set! map key value)", func(s *State) { s.InMap(0).set(s.InString(1), s.In(2)) })
	predefined.Install("(map-delete! map key)", func(s *State) { s.Out, _ = s.InMap(0).Delete(s.InString(1)) })
	predefined.Install("(map-get map key)", func(s *State) { s.Out, _ = s.InMap(0).Load(s.InString(1)) })
	predefined.Install("(map-contains map key)", func(s *State) { _, ok := s.InMap(0).Load(s.InString(1)); s.Out = VBool(ok) })
	predefined.Install("(map-keys map)", func(s *State) {
		ret := make([]Value, 0, s.InMap(0).Len())
		for i := range s.InMap(0).Unsafe() {
			ret = append(ret, VString(i))
		}
		s.Out = VList(ret...)
	})
	predefined.Install("(skip n list)", func(s *State) {
		l := s.InList(1)
		for i := 0; i < int(s.InNumber(0)); i++ {
			l, _ = Tail(l)
		}
		s.Out = VList(l...)
	})
	predefined.Install("#(lambda* (paramlist) body)", func(s *State) {
		tmpvar := "a" + strconv.FormatInt(time.Now().Unix(), 10)
		pl, body := s.InList(0), []Value{
			s.Caller.DupAtom("lambda"),
			s.Caller.DupAtom(tmpvar),
			VList(s.Caller.DupAtom("define"), s.Caller.DupAtom(tmpvar+"-len"), VList(
				s.Caller.DupAtom("vector-len"), s.Caller.DupAtom(tmpvar),
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
			if a, ok := pl[i].Atm(); ok {
				name, val = pl[i], Empty
				if strings.HasSuffix(a, "...") && len(a) > 3 {
					// Special case: "name..." to catch the rest arguments
					body = append(body, VList(
						s.Caller.DupAtom("define"),
						s.Caller.DupAtom(a[:len(a)-3]),
						VList(s.Caller.DupAtom("skip"), VNumber(float64(i)), s.Caller.DupAtom(tmpvar)),
					))
					continue
				}
			} else {
				l, _ := pl[i].Lst()
				s.assert(len(l) == 2 || s.panic("invalid binding list: %v", pl[i]))
				name, val = l[0], l[1]
			}
			body = append(body, VList(
				s.Caller.DupAtom("define"),
				name,
				VList(
					s.Caller.DupAtom("if"),
					VList(s.Caller.DupAtom("<"), VNumber(float64(i)), s.Caller.DupAtom(tmpvar+"-len")),
					VList(s.Caller.DupAtom("vector-nth"), s.Caller.DupAtom(tmpvar), VNumber(float64(i))),
					val,
				),
			))
		}
		body = append(body, s.Args[1:]...)
		s.Out = VList(body...)
	})
	predefined.Install("(vector-len a)", func(s *State) {
		s.Out = VNumber(float64((reflect.ValueOf(s.In(0).GoValue()).Len())))
	})
	predefined.Install("(vector-null? a)", func(s *State) {
		s.Out = VBool(reflect.ValueOf(s.In(0).GoValue()).Len() == 0)
	})
	predefined.Install("(vector-nth vector n)", func(s *State) {
		rm := reflect.ValueOf(s.In(0).GoValue())
		s.Out = Val(rm.Index(int(s.InNumber(1))).Interface())
	})
	predefined.Install("(vector-set-nth! vector n value)", func(s *State) {
		rm := reflect.ValueOf(s.In(0).GoValue())
		rm.Index(int(s.InNumber(1))).Set(s.In(2).GoTypedValue(rm.Type().Elem()))
	})
	predefined.Install("(vector-slice vector start end?)", func(s *State) {
		rl := reflect.ValueOf(s.In(0).GoValue())
		start, end := int(s.InNumber(1)), rl.Len()
		if len(s.Args) == 3 {
			end = int(s.InNumber(2))
		}
		s.Out = VInterface(rl.Slice(start, end).Interface())
	})
	predefined.Install("(vector-concat v1 v2)", func(s *State) {
		rv1, rv2 := reflect.ValueOf(s.In(0).GoValue()), reflect.ValueOf(s.In(1).GoValue())
		s.assert(rv1.Type() == rv2.Type() || s.panic("vector-concat: different type"))
		r := reflect.MakeSlice(rv1.Type(), rv1.Len(), rv1.Len()+rv2.Len())
		reflect.Copy(r, rv1)
		reflect.AppendSlice(r, rv2)
		s.Out = VInterface(r.Interface())
	})
	predefined.Install("(vector-foreach vector callback)", func(s *State) {
		rl, fn := reflect.ValueOf(s.In(0).GoValue()), s.InGoFunc(1)
		for i := 0; i < rl.Len(); i++ {
			fn(VNumber(float64(i)), Val(rl.Index(i).Interface()))
		}
	})
	predefined.Install("(define-record 'name 'field1 ... 'fieldn)", func(s *State) {
		name, fields, typename := s.InAtom(0), make(map[string]int, len(s.Args)-1), new(int)
		for i := 1; i < len(s.Args); i++ {
			fields[s.InAtom(i)] = i
			func(i int) {
				name := name + "-" + s.InAtom(i)

				s.Map.Store(name, VFunc(&Func{f: func(ss *State) { // getter
					ss.assert(len(ss.InList(0)) == len(s.Args) && ss.InList(0)[0].GoValue() == typename || ss.panic("not a %s record", name))
					ss.Out = ss.InList(0)[i]
				}, sig: "(" + name + " r)"}))

				s.Map.Store(name+"-set!", VFunc(&Func{f: func(ss *State) { // setter
					ss.assert(len(ss.InList(0)) == len(s.Args) && ss.InList(0)[0].GoValue() == typename || ss.panic("not a %s record", name))
					ss.InList(0)[i] = ss.In(1) // setter
				}, sig: "(" + name + "-set! r value)"}))
			}(i)
		}

		s.Map.Store(name+"?", VFunc(&Func{f: func(ss *State) {
			ss.Out = VBool(len(ss.InList(0)) == len(s.Args) && ss.InList(0)[0].GoValue() == typename)
		}, sig: "(" + name + "? a)"}))

		s.Map.Store(name+"-new", VFunc(&Func{f: func(ss *State) {
			out := make([]Value, len(s.Args))
			out[0] = VInterface(typename)
			for i := 1; i < len(out); i++ {
				out[i] = Void
			}
			for i := 0; i < len(ss.Args); i += 2 {
				fieldname := ss.InAtom(i)
				ss.assert(fields[fieldname] != 0 || ss.panic("field %s not found", fieldname))
				out[fields[fieldname]] = ss.In(i + 1)
			}
			ss.Out = VList(out...)
		}, sig: "(" + name + "-new ...)"}))
	})
	predefined.Install("(map fn list)", func(s *State) {
		l, r, fn, i := s.InList(1), []Value{}, s.InGoFunc(0), 0
		for h, ok := Head(l, nil); ok; h, ok = Head(l, nil) {
			v, err := fn(h)
			s.assert(err == nil || s.panic("map: error at element %d: %v", i, err))
			r = append(r, v)
			l, _ = Tail(l)
			i++
		}
		s.Out = VList(r...)
	})
	predefined.Install("(reduce fn v list)", func(s *State) {
		l, left, fn, i := s.InList(2), s.In(1), s.InGoFunc(0), 0
		var err error
		for h, ok := Head(l, nil); ok; h, ok = Head(l, nil) {
			left, err = fn(left, h)
			s.assert(err == nil || s.panic("reduce: error at element %d: %v", i, err))
			l, _ = Tail(l)
			i++
		}
		s.Out = left
	})
	predefined.Install("(reduce-right fn v list)", func(s *State) {
		i, rl, right, fn := 0, s.InList(2), s.In(1), s.InGoFunc(0)
		var err error
		for l, ok := Last(rl, nil); ok; l, ok = Last(rl, nil) {
			right, err = fn(right, l)
			s.assert(err == nil || s.panic("reduce-right: error at element %d: %v", i, err))
			rl, _ = Init(rl)
			i++
		}
		s.Out = right
	})
	predefined.Install("#(cond (cond1 stat1) (cond2 stat2) ... (else catch-all)?)", func(s *State) {
		if len(s.Args) == 0 {
			s.Out = s.Caller.DupAtom("true")
			return
		}
		build := func(expr Value) []Value {
			e, _ := expr.Lst()
			s.assert(len(e) == 2 || s.panic("invalid cond statement: %v", expr))
			cond, stat := e[0], e[1]
			if a, ok := cond.Atm(); ok && a == "else" {
				cond = s.Caller.DupAtom("true")
			}
			return []Value{s.Caller.DupAtom("if"), cond, stat, Void}
		}
		exprs := build(s.In(0))
		for i, head := 1, exprs; i < len(s.Args); i++ {
			tail := build(s.In(i))
			head[3] = VList(tail...)
			head = tail
		}
		s.Out = VList(exprs...)
	})
	// 	predefined.Install("(eq any any...)", func(s *State) {
	// 		s.Out = true
	// 		for i, a := 1, s.In(0); i < len(s.Args); i++ {
	// 			s.Out = s.Out.(bool) && reflect.DeepEqual(a, s.Args[i])
	// 		}
	// 	})
	predefined.Install("(struct-get 'field1 ... 'fieldn struct)", func(s *State) {
		rv := reflect.ValueOf(s.In(len(s.Args) - 1).GoValue())
		for i := 0; i < len(s.Args)-1; i++ {
			m := s.InAtom(i)
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
		f := reflect.ValueOf(s.In(len(s.Args) - 1).GoValue())
		if f.Kind() == reflect.Ptr {
			f = f.Elem()
		}
		for i := 0; i < len(s.Args)-2; i++ {
			m := s.InAtom(i)
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
			p.WriteString(s.InString(i))
		}
		s.Out = VString(p.String())
	})
	predefined.Install("(println any...)", func(s *State) { fmt.Fprintln(DefaultStdout, vlisttointerface(s.Args)...) })
	predefined.Install("(print any...)", func(s *State) { fmt.Fprint(DefaultStdout, vlisttointerface(s.Args)...) })
	predefined.Install("(printf format any...)", func(s *State) { fmt.Fprintf(DefaultStdout, s.InString(0), vlisttointerface(s.Args[1:])...) })
	predefined.Install("(regex/match regexp text)", func(s *State) {
		s.Out = VBool(regexp.MustCompile(s.InString(0)).MatchString(s.InString(1)))
	})
	predefined.Install("(regex/find regexp text count)", func(s *State) {
		s.Out = ValRec(regexp.MustCompile(s.InString(0)).FindAllStringSubmatch(s.InString(1), int(s.InNumber(2))))
	})
	predefined.Install("(json any 'c?)",
		func(s *State) {
			var buf []byte
			var err error
			if len(s.Args) == 2 && s.InAtom(1, "c") == "c" {
				buf, err = json.Marshal(s.In(0))
			} else {
				buf, err = json.MarshalIndent(s.In(0), "", "  ")
			}
			s.Out = errorOrValue(string(buf), err)
		})
	predefined.Install("(json-parse string)",
		func(s *State) {
			text := strings.TrimSpace(s.InString(0))
			if strings.HasPrefix(text, "{") {
				m := map[string]interface{}{}
				if err := json.Unmarshal([]byte(text), &m); err != nil {
					s.Out = VInterface(err)
				} else {
					s.Out = ValRec(m)
				}
			}
			if strings.HasPrefix(text, "[") {
				m := []interface{}{}
				if err := json.Unmarshal([]byte(text), &m); err != nil {
					s.Out = VInterface(err)
				} else {
					s.Out = ValRec(m)
				}
			}
		})
	predefined.Install("#(setf! struct.Field1.Field2...Fieldn value)",
		func(s *State) {
			a := s.InAtom(0)
			parts := strings.Split(a, ".")
			s.assert(len(parts) > 1 || s.panic("too few fields to set"))
			structname := parts[0]
			setter := []Value{s.In(0).DupAtom("struct-set!")}
			for i := 1; i < len(parts); i++ {
				setter = append(setter, _Vquote(s.In(0).DupAtom(parts[i])))
			}
			setter = append(setter, s.In(1), s.In(0).DupAtom(structname))
			s.Out = VList(setter...)
		})
	predefined.Install("#(getf struct.Field1.Field2...Fieldn)",
		func(s *State) {
			a := s.InAtom(0)
			parts := strings.Split(a, ".")
			s.assert(len(parts) > 1 || s.panic("too few fields to get"))
			structname := parts[0]
			setter := []Value{s.In(0).DupAtom("struct-get")}
			for i := 1; i < len(parts); i++ {
				setter = append(setter, _Vquote(s.In(0).DupAtom(parts[i])))
			}
			setter = append(setter, s.In(0).DupAtom(structname))
			s.Out = VList(setter...)
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
			v := VList(s.Args...).String()
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
					return VList(VAtom(op, 0, 0), do(e.X))
				case *ast.BinaryExpr:
					op := e.Op.String()
					switch e.Op {
					case token.LAND:
						op = "and"
					case token.LOR:
						op = "or"
					}
					m, _ := s.It.UnwrapMacro([]Value{VAtom(op, 0, 0), do(e.X), do(e.Y)})
					return m
				case *ast.BasicLit:
					switch e.Kind {
					case token.INT:
						v, _ := strconv.ParseInt(e.Value, 10, 64)
						return VNumber(float64(v))
					case token.FLOAT:
						v, _ := strconv.ParseFloat(e.Value, 64)
						return VNumber(v)
					case token.STRING:
						v, _ := strconv.Unquote(e.Value)
						return VString(v)
					}
				case *ast.Ident:
					return VAtom(e.Name, 0, 0)
				case *ast.ParenExpr:
					return do(e.X)
				case *ast.CallExpr:
					r := []Value{do(e.Fun)}
					for i := range e.Args {
						r = append(r, do(e.Args[i]))
					}
					return VList(r...)
				}
				panic(fmt.Errorf("$: %T not supported", e))
			}
			s.Out = do(expr)
		})
}

func (it *Interpreter) Funcs() map[string]*Func {
	p := map[string]*Func{}
	for k, v := range it.Globals.Unsafe() {
		if v.Type() == 'f' {
			p[k], _ = v.Fun()
		}
	}
	return p
}

func (it *Interpreter) RunSimplePipeREPL(path string) error {
	os.Remove(path)
	if err := syscall.Mkfifo(path, 0777); err != nil {
		return err
	}

	text := bytes.Buffer{}
	text.WriteString(`
	rm -rf repl-ac || true
	touch2() { mkdir -p "$(dirname "$1")" && touch "$1" ; }
	`)

	for _, k := range it.Funcs() {
		name := strings.Split(k.String(), " ")[0]
		if len(name) == 0 || !unicode.IsLetter(rune(name[0])) {
			continue
		}
		text.WriteString(fmt.Sprintf("touch2 repl-ac/%s || true\n", name))
	}
	text.WriteString(fmt.Sprintf(`
cd repl-ac
while true; do
    read -p 'in > ' -e cmd
	history -s "$cmd"
    echo $cmd > %s && cat %s
done
`, path, path))

	if err := ioutil.WriteFile("repl", text.Bytes(), 0777); err != nil {
		return err
	}

	ww := &bytes.Buffer{}
	DefaultStdout = ww

	for {
		f, err := os.Open(path)
		if err != nil {
			return err
		}
		tmp := [1024]byte{}
		n, _ := f.Read(tmp[:])
		f.Close()

		cmd := string(bytes.TrimSpace(tmp[:n]))

		ww.Reset()
		v, err := it.Run(cmd)

		resp := bytes.Buffer{}
		resp.WriteString("out > ")

		if ww.Len() > 0 {
			resp.Write(ww.Bytes())
		}

		if err != nil {
			resp.WriteString(err.Error())
		} else {
			resp.WriteString(fmt.Sprint(v))
		}
		resp.WriteRune('\n')

		if err := ioutil.WriteFile(path, resp.Bytes(), 0777); err != nil {
			return err
		}
	}
}

func (it *Interpreter) InjectDebugREPLIntopprof(title string) *Interpreter {
	type respStruct struct {
		Result string
		Stdout string
	}

	ww := &bytes.Buffer{}
	DefaultStdout = ww

	http.HandleFunc("/debug/pprof/repl/tribute.min.js", func(w http.ResponseWriter, r *http.Request) {
		http.ServeFile(w, r, "tribute.min.js")
	})

	http.HandleFunc("/debug/pprof/repl", func(w http.ResponseWriter, r *http.Request) {
		if r.Method == "GET" {
			p := bytes.Buffer{}
			p.WriteString(`<!doctype html><html><meta charset="UTF-8"><title>REPL: ` + title + `</title>
<style>
	body { font-size: 16px }
	* {box-sizing: border-box; font-family: monospace;}
	a {text-decoration: none}
	.results div:nth-child(even) {background: #eee}
	.results > div { display: block !important; }
	.results .result {margin-left:1em;white-space:pre-wrap}
</style>
<script src="/debug/pprof/repl/tribute.min.js" ></script>
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/tributejs/5.1.2/tribute.min.css" integrity="sha256-jCuf8eDAzmPpRqt5n0v1utTOCeWZc4OrGbv24Pw+ltk=" crossorigin="anonymous" />

<form onsubmit="var _=this;post('',{cmd:this.querySelector('#cmd').value},function(obj, data){
	var el = _.nextElementSibling.nextElementSibling.cloneNode(true);
	el.querySelector('.date').innerText = new Date().toLocaleString() 
	el.querySelector('.options').innerText = data.cmd;
	el.querySelector('.options').onclick = function() { document.getElementById('cmd').value = data.cmd }
	el.querySelector('.result').innerText = obj.Result;
	if (obj.Stdout) el.querySelector('.result').innerHTML += '\n<b>Stdout:</b>\n' + obj.Stdout;
	_.nextElementSibling.insertBefore(el,_.nextElementSibling.firstChild)
});return false;">
<input id=cmd style="width:100%;padding:0.5em;margin:0.5em 0;font-size:16px">
<input type=submit style="display:none">
</form>
<div class=results></div>
<div style='display:none'><b class=date></b> <a href='#' class=options></a><span class=result>z</span></div>

<script>
(new Tribute({
	collection: [{
		trigger: '(',
		lookup: 'key',
		values: function (text, cb) {
			post("?all=1", {}, function(results) {
				cb(results.filter(function(r) { return r.key.indexOf(text) > -1 }));
			})
		},
		selectTemplate: function (item) { return '(' + item.original.key },
		menuItemTemplate: function (item) { return item.original.doc; },
		replaceTextSuffix: '\n',
		positionMenu: true,
	}]
})).attach(document.getElementById('cmd'))

function post(url, data, cb) {
    var xml = new XMLHttpRequest(), q = "";
	xml.onreadystatechange = function() {
		if (xml.readyState == 4 && xml.status == 200) cb(JSON.parse(xml.responseText), data) 
	}
	xml.open("POST", url, true);
	xml.setRequestHeader('Content-Type', 'application/x-www-form-urlencoded');
	for (var k in data) if (data.hasOwnProperty(k)) q += '&' + k + '=' + encodeURIComponent(data[k]);
	xml.send(q);
}
</script>

<pre>`)
			for _, cmd := range it.Funcs() {
				p.WriteByte('\n')
				p.WriteString(cmd.String())
			}
			w.Header().Add("Content-Type", "text/html")
			w.Write(p.Bytes())
			return
		}

		if r.FormValue("all") != "" {
			keys := []map[string]string{}
			for k, cmd := range it.Funcs() {
				keys = append(keys, map[string]string{"key": k, "doc": cmd.sig})
			}
			buf, _ := json.Marshal(keys)
			w.Write(buf)
			return
		}

		cmd := r.FormValue("cmd")

		ww.Reset()
		v, err := it.Run(cmd)

		var resp = respStruct{
			Stdout: ww.String(),
			Result: fmt.Sprint(v),
		}
		if err != nil {
			resp.Result = err.Error()
		}

		p, _ := json.Marshal(resp)
		w.Header().Add("Content-Type", "application/json")
		w.Write([]byte(p))
	})

	return it
}

func (v Value) GoTypedValue(t reflect.Type) reflect.Value {
	vv := v.GoValue()
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
		if x := 1 + maxdepth(e._lst()); x > d {
			d = x
		}
	}
	return d
}
