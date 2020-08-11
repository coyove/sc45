package sc45

import (
	"bytes"
	"fmt"
	"io/ioutil"
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
	Void, Quote   = Value{}, Sym("quote", 0, 0)
	Empty         = &Pair{_empty: true}
	Types         = map[byte]string{'s': "string", 'y': "symbol", 'n': "number", 'l': "list", 'i': "any", 'f': "function", 'v': "void"}
	TypesRev      = map[string]byte{"string": 's', "symbol": 'y', "number": 'n', "list": 'l', "any": 'i', "function": 'f', "void": 'v'}
)

type (
	Value struct {
		val uint64
		ptr unsafe.Pointer
	}
	Pair struct {
		next   *Pair
		val    Value
		_empty bool
	}
	Func struct {
		macro         bool         // is macro
		wrapper       bool         // is native wrapper
		fvar          bool         // builtin is variadic
		f             func(*State) // builtin function
		fvars         int          // builtin: (minimal) arguments required
		n             Value        // native function
		nargs         []string     // native: arguments binding list
		nvar_or_fname string       // native: vararg name, builtin: last assigned name
		cls           *Context     // native: closure
		location      string
	}
	State struct {
		*Context
		assertable
		argsidx     int
		arglast     Value
		Args        *Pair
		Out, Caller Value
		CallerLoc   *string
	}
	Context struct {
		assertable
		parent *Context
		m      map[string]Value
	}
	callerInfo struct {
		v   *Value
		loc *string
	}
	execState struct {
		assertable
		curCaller callerInfo
		local     *Context
		quasi     bool
		macroMode bool
	}
	assertable struct{ err error }
)

func New() *Context { return Default.Copy() }

func F(minArgsFlag int, f func(*State)) Value {
	return Fun(&Func{f: f, fvars: minArgsFlag & 0xffff, fvar: minArgsFlag&Vararg != 0, macro: minArgsFlag&Macro != 0})
}

func (f *Func) Call(a ...Value) (Value, error) {
	expr := initlistbuilder().append(Fun(f).Quote())
	for i := range a {
		expr = expr.append(a[i].Quote())
	}
	return ((*Context)(nil)).Exec(expr.value())
}

func (f *Func) String() string {
	if f.n == Void {
		return ifstr(f.nvar_or_fname == "#v", "/*missing native code*/", f.nvar_or_fname+" /*native code*/")
	}
	return ifstr(f.macro, "(lambda-syntax (", "(lambda (") + strings.Join(f.nargs, " ") + ifstr(f.nvar_or_fname != "", " . "+f.nvar_or_fname, "") + ") " + f.n.String() + ")"
}

// In pops an argument
func (s *State) In() Value {
	s.assert(!s.Args.Empty() || s.panic("too few arguments, expect at least %d", s.argsidx+1))
	v := s.Args.Val()
	s.argsidx, s.arglast = s.argsidx+1, v
	s.Args = s.Args.Next()
	return v
}

func (s *State) InType(t byte) Value {
	v := s.In()
	s.assert(t == 0 || v.Type() == t || s.panic("invalid argument #%d, expect %s, got %v", s.argsidx, Types[t], v))
	return v
}

func (s *State) LastIn() Value { return s.arglast }

func (ctx *Context) find(k string) (Value, *Context) {
	for ; ctx != nil; ctx = ctx.parent {
		if v, ok := ctx.m[k]; ok {
			return v, ctx
		}
	}
	return Void, nil
}

func (ctx *Context) set(k string, v Value) {
	if ctx.m == nil {
		ctx.m = make(map[string]Value, 4)
	}
	ctx.m[k] = v
}

func (ctx *Context) Store(k string, v Value) *Context {
	if v.Type() == 'f' && v.Fun().n == Void {
		v.Fun().nvar_or_fname = k
	}
	if _, mv := ctx.find(k); mv == nil {
		ctx.set(k, v)
	} else {
		mv.set(k, v)
	}
	return ctx
}

func (ctx *Context) Load(k string) (Value, bool) {
	v, mv := ctx.find(k)
	return v, mv != nil
}

func (ctx *Context) Delete(k string) (Value, bool) {
	v, mv := ctx.find(k)
	if mv != nil {
		delete(mv.m, k)
	}
	return v, mv != nil
}

func (ctx *Context) Len() int { return len(ctx.m) }

func (ctx *Context) Unsafe() map[string]Value { return ctx.m }

func (ctx *Context) Copy() *Context {
	m2 := &Context{m: make(map[string]Value, len(ctx.m)), parent: ctx.parent}
	for k, v := range ctx.m {
		m2.m[k] = v
	}
	return m2
}

func __exec(expr Value, state execState) Value {
	if state.quasi {
		if expr.Type() == 'l' && !expr.Lst().Empty() {
			lst := expr.Lst()
			if x := lst.Val(); x.Type() == 'y' && x.Str() == "unquote" {
				state.assert(lst.HasNext() || state.panic("invalid unquote syntax"))
				state.quasi = false
				v := __exec(lst.Next().Val(), state)
				return v
			}
			results := initlistbuilder()
			for ; !lst.Empty(); lst = lst.Next() {
				results = results.append(__exec(lst.Val(), state))
			}
			return results.value()
		}
		return expr
	}

TAIL_CALL:
	switch expr.Type() {
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

	head := c.Val()
	if *state.curCaller.v = c.Val(); state.curCaller.v.Type() == 'y' {
		switch va := state.curCaller.v.Str(); va {
		case "if":
			state.assert(c.MoveNext(&c) || state.panic("invalid if syntax, missing condition"))
			if !__exec(c.Val(), state).IsFalse() {
				state.assert(c.MoveNext(&c) || state.panic("invalid if syntax, missing true branch"))
				expr = c.Val() // execute true-branch
				goto TAIL_CALL
			}
			c.MoveNext(&c)                     // skip condition
			c.MoveNext(&c)                     // skip true branch
			for ; !c.Empty(); c.MoveNext(&c) { // execute rest statements: (if cond true-branch false-1 ... false-n)
				if !c.HasNext() {
					expr = c.Val()
					goto TAIL_CALL
				}
				__exec(c.Val(), state)
			}
			return Void
		case "lambda", "lambda-syntax":
			state.assert(c.MoveNext(&c) || state.panic("invalid lambda* syntax, missing parameters"))
			f := &Func{cls: state.local, macro: va != "lambda", location: *state.curCaller.loc}
			switch c.Val().Type() {
			case 'y': // (lambda* args body)
				f.nvar_or_fname = c.Val().Str()
			case 'l': // (lambda* (a1 a2 ... an) body)
				for bindings := c.Val().Lst(); bindings != nil; bindings = bindings.Next() {
					switch bindings.testEmpty() {
					case 'i':
						state.assert(bindings.Val().Type() == 'y' || state.panic("invalid parameter, expect valid symbol"))
						f.nvar_or_fname = bindings.Val().Str()
					case 'f':
						state.assert(bindings.Val().Type() == 'y' || state.panic("invalid parameter, expect valid symbol"))
						f.nargs = append(f.nargs, bindings.Val().Str())
					}
				}
			default:
				panic(fmt.Errorf("invalid binding list: %v", c.Val()))
			}
			state.assert(c.MoveNext(&c) || state.panic("invalid lambda syntax, missing lambda body"))
			if f.n = c.Val(); c.HasNext() {
				f.n = Lst(c, state.curCaller.v.Make("if"), Void, Void)
			}
			return Fun(f)
		case "match":
			state.assert(c.MoveNext(&c) || state.panic("invalid match syntax, missing source"))
			source := __exec(c.Val(), state)
			state.assert(source.Type() == 'l' || state.panic("invalid match syntax, expect source to be list"))
			state.assert(c.MoveNext(&c) && c.Val().Type() == 'l' || state.panic("invalid match syntax, missing symbol list"))
			symbols := c.Val().Lst().ToSlice()
		MATCH_NEXT:
			state.assert(c.MoveNext(&c) && c.Val().Type() == 'l' || state.panic("invalid match syntax, missing pattern"))
			pattern := c.Val().Lst()
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
				return __exec(c.Val(), execState{curCaller: state.curCaller, local: m})
			}
			if c.HasNext() {
				goto MATCH_NEXT
			}
			return Void
		case "quote":
			state.assert(c.MoveNext(&c) || state.panic("invalid quote syntax"))
			return c.Val()
		case "quasiquote":
			state.assert(c.MoveNext(&c) || state.panic("invalid quasiquote syntax"))
			state.quasi = true
			v := __exec(c.Val(), state)
			return v
		case "unquote":
			panic(fmt.Errorf("unquote outside quasiquote"))
		case "set!":
			state.assert(c.MoveNext(&c) && c.Val().Type() == 'y' || state.panic("invalid set! syntax, missing symbol"))
			x := c.Val().Str()
			_, m := state.local.find(x)
			state.assert(m != nil || state.panic("set!: unbound %s", x))
			state.assert(c.MoveNext(&c) || state.panic("invalid set! syntax, missing bound value"))
			m.set(x, __exec(c.Val(), state))
			return Void
		case "define":
			switch c.MoveNext(&c); c.Val().Type() {
			case 'y':
				x := c.Val().Str()
				state.assert(state.local.m[x] == Void || state.panic("re-define %s", x)).
					assert(c.MoveNext(&c) || state.panic("invalid define syntax, missing bound value"))
				state.local.set(x, __exec(c.Val(), state))
			case 'l':
				lst := c.Val().Lst()
				state.assert(!lst.Empty() || state.panic("invalid define syntax, missing function name")).
					assert(c.MoveNext(&c) || state.panic("invalid define syntax, missing bound value"))
				s := Lst(Empty, head.Make("define"), lst.Val(), Lst(c, head.Make("lambda"), Lst(lst.Next())))
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

	oldLoc := *state.curCaller.loc
	if cc.f == nil {
		if cc.macro && !state.macroMode {
			return __exec(state.local.unwrapMacro(expr, false), state)
		}
		m := &Context{parent: cc.cls}
		for i, name := range cc.nargs {
			state.assert(c.MoveNext(&c) || state.panic("too few arguments, expect at least %d", i+1))
			m.set(name, __exec(c.Val(), state))
		}
		if cc.nvar_or_fname != "" {
			values := initlistbuilder()
			c.Next().Range(func(v Value) bool { values = values.append(__exec(v, state)); return true })
			m.set(cc.nvar_or_fname, values.value())
		}
		if *state.curCaller.loc == cc.location {
			*state.curCaller.v, state.local, expr = head, m, cc.n
			goto TAIL_CALL
		}
		*state.curCaller.loc, state.local = cc.location, m
		v := __exec(cc.n, state)
		*state.curCaller.loc = oldLoc
		return v
	}

	s := State{Context: state.local, Out: Void, Caller: head, CallerLoc: state.curCaller.loc}
	args := initlistbuilder()
	c.Next().Range(func(v Value) bool { args = args.append(__exec(v, state)); return true })

	*state.curCaller.v = head
	state.assert(args.count == cc.fvars || (cc.fvar && args.count >= cc.fvars) ||
		state.panic("call: expect "+ifstr(cc.fvar, "at least ", "")+strconv.Itoa(cc.fvars)+" arguments"))

	s.Args = args.L
	cc.f(&s)
	*state.curCaller.loc = oldLoc
	return s.Out
}

func (ctx *Context) Parse(filename, text string) (expr Value, err error) {
	s := (&scanner.Scanner{}).Init(strings.NewReader(text))
	s.Mode &^= scanner.ScanChars | scanner.ScanRawStrings
	s.Error = func(s *scanner.Scanner, msg string) {
		pos := s.Position
		if !pos.IsValid() {
			pos = s.Pos()
		}
		err = fmt.Errorf("parse: %s at %s:%d:%d", msg, filename, pos.Line, pos.Column)
	}
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("parse: %v at %s:%d:%d", r, filename, s.Pos().Line, s.Pos().Column)
		}
	}()
	v := ctx.scan(s, false)
	if err != nil {
		return Void, err
	}

	v = ctx.unwrapMacro(v, false)
	if v.Type() == 'l' {
		v = Lst(v.Lst(), Sym("if", 0, 0), Void, Void)
	} else {
		v = Lst(Empty, Sym("if", 0, 0), Void, Void, v)
	}
	v = Fun(&Func{n: v, cls: ctx, wrapper: true, location: filename})
	return Lst(Empty, v), nil
}

func (ctx *Context) Exec(c Value) (output Value, err error) {
	var curCaller Value
	var curLoc string
	defer func() {
		if r := recover(); r != nil {
			if os.Getenv("SBD_STACK") != "" {
				fmt.Println(string(debug.Stack()))
			}
			err = fmt.Errorf("%v at %v (%s)", r, curCaller, curLoc)
		}
	}()
	return __exec(c, execState{local: ctx, curCaller: callerInfo{&curCaller, &curLoc}}), nil
}

func (ctx *Context) RunFile(path string) (result Value, err error) {
	buf, err := ioutil.ReadFile(path)
	if err != nil {
		return Void, err
	}
	c, err := ctx.Parse(path, *(*string)(unsafe.Pointer(&buf)))
	if err != nil {
		return Void, err
	}
	buf, err = c.Lst().Val().Fun().n.Marshal()
	panicerr(err)
	{
		c := Void
		fmt.Println(c.Unmarshal(buf))
	}
	return ctx.Exec(c)
}

func (ctx *Context) Run(tmpl string) (result Value, err error) {
	c, err := ctx.Parse("(memory)", tmpl)
	if err != nil {
		return Void, err
	}
	return ctx.Exec(c)
}

func (ctx *Context) scan(s *scanner.Scanner, scanOne bool) Value {
	comp := initlistbuilder()
LOOP:
	for tok := s.Scan(); tok != scanner.EOF; tok = s.Scan() {
		// fmt.Println(s.TokenText())
		switch tok {
		case scanner.String, scanner.RawString:
			t, err := strconv.Unquote(s.TokenText())
			ctx.assert(err == nil || ctx.panic("invalid string: %q", s.TokenText()))
			comp = comp.append(Str(t))
		case '#':
			switch pr := s.Peek(); pr {
			case '|': // #| comment |#
				for s.Scan(); ; {
					current, next := s.Scan(), s.Peek()
					ctx.assert(current != scanner.EOF || ctx.panic("incomplete comment block"))
					if current == '|' && next == '#' {
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
					ctx.assert(l != 0 || ctx.panic("invalid char: %q", n))
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
			comp = comp.append(ctx.scan(s, false))
		case ')', ']':
			break LOOP
		case '.':
			c := ctx.scan(s, true)
			if c.Type() == 'l' {
				*comp.p = *c.Lst()
			} else {
				comp.p.SetVal(c)._empty = false
			}
			s := s.Scan()
			ctx.assert(s == scanner.EOF || s == ']' || s == ')' || ctx.panic("invalid dot syntax"))
			return comp.value()
		case '\'', '`', ',':
			c := ctx.scan(s, true)
			ctx.assert(c != Void || ctx.panic("invalid *quote syntax"))
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
			return comp.L.Val()
		}
	}
	return comp.value()
}

func (ctx *Context) unwrapMacro(v Value, quasi bool) Value {
	if v.Type() != 'l' || v.Lst().testEmpty() == 't' {
		return v
	}

	comp := v.Lst()
	if head := comp.Val(); head.Type() == 'y' {
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
					args = args.append(ctx.unwrapMacro(comp.Val(), false).Quote())
				}
				v := __exec(args.value(), execState{local: ctx, curCaller: callerInfo{&Value{}, new(string)}, macroMode: true})
				return ctx.unwrapMacro(v, false)
			}
		}
	}
	old := comp
	for ; comp != nil; comp = comp.Next() {
		if comp.testEmpty() == 't' {
			break
		}
		comp.SetVal(ctx.unwrapMacro(comp.Val(), quasi))
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
	*va.itfptr() = v
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
		n := (&Pair{}).SetNext(lst).SetVal(l[i])
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

func (v *Value) itfptr() *interface{} { return (*interface{})(unsafe.Pointer(v)) }
func (v Value) IsFalse() bool         { return v.val < 2 } // 0: void, 1: false

func (v Value) Quote() Value {
	if t := v.Type(); t == 'l' || t == 'y' {
		return Lst((&Pair{}).SetVal(Quote).SetNext((&Pair{}).SetVal(v).SetNext(Empty)))
	}
	return v
}

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
		return ifbyte(v == Void, 'v', 'i')
	}
}

func (v Value) String() string { return v.stringify(false) }

func (v Value) stringify(goStyle bool) string {
	switch v.Type() {
	case 'n':
		return strconv.FormatFloat(v.Num(), 'f', -1, 64)
	case 's':
		return strconv.Quote(v.Str())
	case 'y':
		line, col := v.Pos()
		return v.Str() + ifstr(line > 0, fmt.Sprintf(ifstr(goStyle, " /*%d:%d*/", " #|%d:%d|#"), line, col), "")
	case 'l':
		vl, p := v.Lst(), bytes.NewBufferString("(")
		for vl != nil && !vl._empty {
			if vl.Next() == nil {
				p.WriteString(". ")
				p.WriteString(vl.Val().stringify(goStyle))
			} else {
				p.WriteString(vl.Val().stringify(goStyle))
				p.WriteString(" ")
			}
			vl = vl.Next()
		}
		for p.Len() > 0 && p.Bytes()[p.Len()-1] == ' ' {
			p.Truncate(p.Len() - 1)
		}
		p.WriteString(")")
		return p.String()
	case 'b':
		return ifstr(v.Bln(), ifstr(goStyle, "true", "#t"), ifstr(goStyle, "false", "#f"))
	case 'i':
		return "#" + fmt.Sprint(*v.itfptr())
	case 'f':
		return v.Fun().String()
	default:
		return ifstr(goStyle, "nil", "#v")
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
		var a []interface{}
		v.Lst().Range(func(v Value) bool { a = append(a, v.Val()); return true })
		return a
	case 'b':
		return v.Bln()
	case 'i':
		return *v.itfptr()
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
			return *v.itfptr() == *v2.itfptr()
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

func (p *Pair) Val() Value             { return p.val }
func (p *Pair) SetVal(v Value) *Pair   { p.val = v; return p }
func (p *Pair) Next() *Pair            { return p.next }
func (p *Pair) SetNext(p2 *Pair) *Pair { p.next = p2; return p }
func (p *Pair) Empty() bool {
	if r := p.testEmpty(); r == 'i' {
		panic("improper list")
	} else {
		return r == 't'
	}
}
func (p *Pair) testEmpty() byte {
	if p.Next() == nil {
		return ifbyte(p._empty, 't', 'i')
	}
	return 'f'
}
func (p *Pair) HasNext() bool { return p.Next() != nil && !p.Next().Empty() }
func (p *Pair) MoveNext(ll **Pair) bool {
	if p.HasNext() {
		*ll = p.Next()
		return true
	}
	*ll = Empty
	return false
}
func (p *Pair) Len() (length int) {
	for ; !p.Empty(); p = p.Next() {
		length++
	}
	return
}
func (p *Pair) Range(cb func(Value) bool) {
	for flag := true; flag && !p.Empty(); p = p.Next() {
		flag = cb(p.Val())
	}
}
func (p *Pair) ToSlice() (s []Value) {
	p.Range(func(v Value) bool { s = append(s, v); return true })
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
	b.p.SetVal(v).SetNext(&Pair{_empty: true})._empty = false
	b.p = b.p.Next()
	b.count++
	return b
}
func (b listbuilder) value() Value { return Lst(b.L) }

func (p *Pair) match(state execState, pattern *Pair, metWildcard bool, symbols map[string]struct{}, m map[string]Value) bool {
	if pattern.Empty() && p.Empty() {
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
	if p.Empty() {
		if pattern.Val().Type() == 'y' && !pattern.HasNext() {
			if w := isWildcard(pattern.Val().Str()); w != "" {
				m[w] = Lst(Empty)
				return true
			}
		}
		return false
	}
	switch pattern.Val().Type() {
	case 'y':
		sym := pattern.Val().Str()
		if sym == "_" {
			break
		}
		if _, ok := symbols[sym]; ok {
			if !pattern.Val().Equals(p.Val()) {
				return false
			}
			break
		}
		if w := isWildcard(sym); w != "" {
			if pattern.HasNext() {
				n := p.Len() - pattern.Next().Len()
				if n < 0 { // the remaining symbols in 'p' is less than 'pattern'
					return false
				}
				// The first n symbols will go into 'ww'
				ww := initlistbuilder()
				for ; n > 0; n-- {
					ww = ww.append(p.Val())
					p = p.Next()
				}
				m[w] = ww.value()
				return p.match(state, pattern.Next(), true, symbols, m)
			}
			m[w] = Lst(p)
			return true
		}
		if strings.HasPrefix(sym, "#:") {
			if x := TypesRev[sym[2:]]; x > 0 {
				if p.Val().Type() != x {
					return false
				}
			} else if !p.Val().Equals(pattern.Val()) {
				return false
			}
			break
		}
		m[sym] = p.Val()
	case 'l':
		if lst := pattern.Val().Lst(); lst.Val().Type() == 'y' && lst.Val().Str() == "quote" {
			if __exec(lst.Next().Val(), execState{
				curCaller: state.curCaller,
				local:     &Context{parent: state.local, m: map[string]Value{"_": p.Val()}},
			}).IsFalse() {
				return false
			}
			m["_"] = p.Val()
			break
		}
		if p.Val().Type() != 'l' {
			return false
		}
		if !p.Val().Lst().match(state, pattern.Val().Lst(), false, symbols, m) {
			return false
		}
	default:
		if !p.Val().Equals(pattern.Val()) {
			return false
		}
	}
	return p.Next().match(state, pattern.Next(), false, symbols, m)
}
func (p *Pair) Take(n int) *Pair {
	if n == 0 {
		return Empty
	}
	b := initlistbuilder()
	for ; !p.Empty(); p = p.Next() {
		b = b.append(p.Val())
		if n == -1 {
			if !p.HasNext() { // we are at the last position, this means p.Len() == 1
				return Empty
			} else if /* p.HasNext() &&*/ !p.Next().HasNext() { // we are at second to last position
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
func (p *Pair) Append(l2 *Pair) *Pair {
	b := initlistbuilder()
	p.Range(func(v Value) bool { b = b.append(v); return true })
	*b.p = *l2
	return b.L
}
func (p *Pair) Last() (last *Pair) {
	for ; !p.Empty(); p = p.Next() {
		last = p
	}
	return
}
func (p *Pair) Proper() bool {
	for ; ; p = p.Next() {
		if f := p.testEmpty(); f == 'i' {
			return false
		} else if f == 't' {
			return true
		}
	}
}

func Cons(v, v2 Value) *Pair {
	p := (&Pair{}).SetVal(v)
	if v2.Type() == 'l' {
		p.SetNext(v2.Lst())
	} else {
		p.SetNext((&Pair{}).SetVal(v2))
	}
	return p
}
