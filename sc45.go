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
	"time"
	"unicode"
	"unicode/utf8"
	"unsafe"
)

var (
	Default, Now, Forever                  = &Context{}, func() int64 { return time.Now().Unix() }, time.Unix(1<<32, 0)
	Void, Quote, Empty                     = Value{}, Y("quote", 0), &Pair{empty: true}
	Types                                  = map[ValueType]string{TEXT: "string", SYM: "symbol", NUM: "number", LIST: "list", INTF: "interface", FUNC: "function", VOID: "void", BOOL: "boolean"}
	int64Marker, boolMarker, float64Marker = unsafe.Pointer(new(int64)), unsafe.Pointer(new(bool)), unsafe.Pointer(new(float64))
	stateType, errorType                   = reflect.TypeOf(&State{}), reflect.TypeOf((*error)(nil)).Elem()
)

const TEXT, SYM, NUM, BOOL, LIST, INTF, FUNC, VOID ValueType = 's', 'y', 'n', 'b', 'l', 'i', 'f', 'v'

type (
	ValueType byte
	Value     struct {
		val uint64
		ptr unsafe.Pointer
	}
	Pair struct {
		next  *Pair
		val   Value
		empty bool
	}
	Func struct {
		Source, name  string       // filename inherited from the toplevel lambda, name => native: variadic argument name, builtin: last assigned name
		Vararg, Macro bool         // is macro/variadic function
		natToplevel   bool         // native: toplevel
		natArgNames   []string     // native: arguments binding list
		natCls        *Context     // native: closure
		nat           Value        // native
		MinArgNum     int          // builtin: minimal arguments required
		F             func(*State) // builtin
	}
	State struct {
		*Context
		assertable
		argIdx              int
		deadline            int64
		Args                *Pair
		LastIn, Caller, Out Value
		Stack               *Stack
	}
	Context struct {
		assertable
		parent *Context
		M      map[string]Value
	}
	frame struct {
		K   Value
		Loc string
	}
	Stack struct {
		nextLoc string
		Frames  []frame
	}
	ListBuilder struct {
		Len             int
		head, last, Cur *Pair
	}
	execState struct {
		assertable
		deadline  int64
		debug     *Stack
		local     *Context
		macroMode bool
	}
	assertable struct{ err error }
)

func New() *Context { return Default.Copy() }

func (s *Stack) popAndReturn(v Value) Value {
	s.nextLoc = s.Frames[len(s.Frames)-1].Loc
	s.Frames = s.Frames[:len(s.Frames)-1]
	return v
}
func (s *Stack) push(k Value, tail bool) {
	if !tail {
		s.Frames = append(s.Frames, frame{K: k, Loc: s.nextLoc})
		return
	}
	s.Frames[len(s.Frames)-1].K = k
	s.Frames[len(s.Frames)-1].Loc = s.nextLoc
}
func (s *Stack) StackLocations(includeBuiltin bool) (locs []string) {
	for _, k := range s.Frames {
		if k.Loc != "(sys)" || includeBuiltin {
			locs = append(locs, k.Loc)
		}
	}
	return locs
}
func (s *Stack) LastLocation() string { return s.Frames[len(s.Frames)-1].Loc }
func (s *Stack) String() (p string) {
	for _, k := range s.Frames {
		if sym, li := k.K.findSym(0); sym != "" && li > 0 {
			p = sym + " in " + k.Loc + ":" + strconv.FormatInt(int64(li), 10) + "\n" + p
		}
	}
	return strings.TrimSpace(p)
}

func (f *Func) Call(a ...interface{}) (result Value, err error) {
	v := InitListBuilder()
	for _, a := range a {
		v = v.Append(V(a))
	}
	return f.CallOnStack(nil, Forever, v.Build())
}
func (f *Func) CallOnStack(dbg *Stack, deadline time.Time, args Value) (result Value, err error) {
	expr := L(args.List(), F(f).Quote())
	if dbg == nil {
		dbg = &Stack{nextLoc: "(call)"}
	}
	defer debugCatch(dbg, &err)
	return __exec(expr, execState{local: (*Context)(nil), debug: dbg, deadline: deadline.Unix()}), nil
}
func (f *Func) String() string {
	if f.nat == Void {
		return ifstr(f.name == "", "#|missing native code|#", f.name+" #|native code|#")
	} else if f.Vararg && len(f.natArgNames) == 0 {
		return ifstr(f.Macro, "(lambda-syntax ", "(lambda ") + f.name + " " + f.nat.String() + ")"
	}
	return ifstr(f.Macro, "(lambda-syntax (", "(lambda (") + strings.Join(f.natArgNames, " ") + ifstr(f.Vararg, " . "+f.name, "") + ") " + f.nat.String() + ")"
}

// In pops an argument
func (s *State) In() Value {
	s.assert(!s.Args.MustProper().Empty() || s.panic("too few arguments, expect at least %d", s.argIdx+1))
	v := s.Args.val
	s.argIdx, s.LastIn = s.argIdx+1, v
	s.Args = s.Args.next
	return v
}
func (s *State) Nv() Value                 { return s.In().expect(s, NUM) }
func (s *State) N() (float64, int64, bool) { return s.In().expect(s, NUM).Number() }
func (s *State) I() int64                  { return s.In().expect(s, NUM).Int() }
func (s *State) S() string                 { return s.In().expect(s, TEXT).Text() }
func (s *State) Y() string                 { return s.In().expect(s, SYM).Text() }
func (s *State) L() *Pair                  { return s.In().expect(s, LIST).List() }
func (s *State) B() bool                   { return s.In().expect(s, BOOL).Bool() }
func (s *State) F() *Func                  { return s.In().expect(s, FUNC).Func() }
func (s *State) V() interface{}            { return s.In().Interface() }
func (s *State) Deadline() time.Time       { return time.Unix(s.deadline, 0) }

func (ctx *Context) find(k string) (Value, *Context) {
	for ; ctx != nil; ctx = ctx.parent {
		if v, ok := ctx.M[k]; ok {
			return v, ctx
		}
	}
	return Void, nil
}
func (ctx *Context) set(k string, v Value) {
	if ctx.M == nil {
		ctx.M = make(map[string]Value, 4)
	}
	ctx.M[k] = v
}
func (ctx *Context) Store(k string, v Value) *Context {
	if v.Type() == FUNC && v.Func().F != nil {
		v.Func().name = k
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
		delete(mv.M, k)
	}
	return v, mv != nil
}
func (ctx *Context) Copy() *Context {
	m2 := &Context{M: make(map[string]Value, len(ctx.M)), parent: ctx.parent}
	for k, v := range ctx.M {
		m2.M[k] = v
	}
	return m2
}

func __execQuasi(expr Value, state execState) (Value, *Pair) {
	if expr.Type() == LIST && !expr.List().MustProper().Empty() {
		lst := expr.List()
		if x := lst.val; x.Type() == SYM {
			switch x.Text() {
			case "unquote":
				state.assert(lst.HasProperCdr() || state.panic("invalid unquote syntax"))
				return __exec(lst.next.val, state), nil
			case "unquote-splicing":
				state.assert(lst.HasProperCdr() || state.panic("invalid unquote-splicing syntax"))
				v := __exec(lst.next.val, state)
				if v.Type() == LIST {
					return Void, v.List()
				}
				return Void, &Pair{val: v}
			}
		}
		results := InitListBuilder()
		for ; !lst.MustProper().Empty(); lst = lst.next {
			if v, p := __execQuasi(lst.val, state); p != nil {
				for ; p != nil; p = p.next {
					*results.Cur = *p
					if !p.Empty() && !p.Improper() {
						results.Cur.next = &Pair{empty: true}
						results.Cur = results.Cur.next
					}
				}
			} else {
				results = results.Append(v)
			}
		}
		return results.Build(), nil
	}
	return expr, nil
}

func __exec(expr Value, state execState) Value {
	tailCall := false
TAIL_CALL:
	switch expr.Type() {
	case LIST: // evaluating the list
	case SYM:
		v, ok := state.local.Load(expr.Text())
		state.assert(ok || state.panic("unbound %v", expr))
		expr = v
		fallthrough
	default:
		if tailCall {
			return state.debug.popAndReturn(expr)
		}
		return expr
	}

	state.assert(Now() < state.deadline || state.panic("timeout"))
	c := expr.List()
	if c.MustProper().Empty() {
		return L(Empty)
	}

	head := c.val
	state.debug.push(head, tailCall)

	if head.Type() == SYM {
		switch va := head.Text(); va {
		case "if", "lambda-body":
			state.assert(moveCdr(&c) || state.panic("invalid if syntax, missing condition"))
			if !__exec(c.val, state).IsFalse() {
				state.assert(moveCdr(&c) || state.panic("invalid if syntax, missing true branch"))
				expr, tailCall = c.val, true // execute true-branch
				goto TAIL_CALL
			}
			moveCdr(&c)                                  // skip condition
			moveCdr(&c)                                  // skip true branch
			for ; !c.MustProper().Empty(); moveCdr(&c) { // execute rest statements: (if cond true-branch false-1 ... false-n)
				if !c.HasProperCdr() {
					expr, tailCall = c.val, true
					goto TAIL_CALL
				}
				__exec(c.val, state)
			}
			return state.debug.popAndReturn(Void)
		case "lambda", "lambda-syntax":
			state.assert(moveCdr(&c) || state.panic("lambda: missing binding list"))
			f := &Func{natCls: state.local, Macro: va != "lambda", Source: state.debug.LastLocation()}
			switch c.val.Type() {
			case SYM: // (lambda* args body)
				f.name, f.Vararg = fmt.Sprint(c.val.Interface()), true
			case LIST: // (lambda* (a1 a2 ... an) body)
				for bindings := c.val.List(); bindings != nil; bindings = bindings.next {
					if p := fmt.Sprint(bindings.val.Interface()); bindings.Improper() {
						f.name, f.Vararg = p, true
					} else if !bindings.Empty() {
						f.natArgNames = append(f.natArgNames, p)
					}
				}
			default:
				f.Vararg = true
			}
			state.assert(moveCdr(&c) || state.panic("lambda: missing body"))
			_ = c.HasProperCdr() && f.nat.of(L(c, head.SetText("lambda-body"), Void, Void)) || f.nat.of(c.val)
			return state.debug.popAndReturn(F(f))
		case "match":
			state.assert(moveCdr(&c) || state.panic("match: missing source"))
			source := __exec(c.val, state)
			state.assert(moveCdr(&c) && c.val.Type() == LIST || state.panic("match: missing symbol list"))
			symbols := c.val.List().ToSlice()
		MATCH_NEXT:
			// ( (pattern subject) ... )
			state.assert(moveCdr(&c) && c.val.Type() == LIST && c.val.List().HasProperCdr() || state.panic("match: invalid pattern"))
			pattern, subject, matched := c.val.List().val, c.val.List().next.val, false
			m := &Context{parent: state.local, M: map[string]Value{}}
			if pattern.Type() == LIST && source.Type() == LIST {
				var symbolmap map[string]struct{}
				if len(symbols) > 0 {
					symbolmap = map[string]struct{}{}
					for _, s := range symbols {
						symbolmap[s.Text()] = struct{}{}
					}
				}
				matched = source.List().match(state, pattern.List(), false, symbolmap, m.M)
			} else {
				matched = source.Equals(pattern)
			}
			if matched {
				return state.debug.popAndReturn(__exec(subject, execState{debug: state.debug, local: m, deadline: state.deadline}))
			}
			if c.HasProperCdr() {
				goto MATCH_NEXT
			}
			return state.debug.popAndReturn(Void)
		case "quote":
			state.assert(moveCdr(&c) || state.panic("invalid quote syntax"))
			return state.debug.popAndReturn(c.val)
		case "quasiquote":
			state.assert(moveCdr(&c) || state.panic("invalid quasiquote syntax"))
			v, p := __execQuasi(c.val, state)
			return state.debug.popAndReturn(v.nop(p != nil && v.of(L(p)) || v.of(v)))
		case "unquote", "unquote-splicing":
			panic(fmt.Errorf("unquote outside quasiquote"))
		case "set!":
			state.assert(moveCdr(&c) && c.val.Type() == SYM || state.panic("set!: missing symbol"))
			x := c.val.Text()
			oldValue, m := state.local.find(x)
			state.assert(m != nil || state.panic("set!: unbound %s", x))
			state.assert(moveCdr(&c) || state.panic("set!: missing bound value"))
			state.assert(oldValue.Type() != FUNC || !oldValue.Func().Macro || state.panic("set!: alter bounded macro"))
			m.set(x, __exec(c.val, state))
			return state.debug.popAndReturn(Void)
		case "define":
			switch moveCdr(&c); c.val.Type() {
			case SYM:
				x := c.val.Text()
				_, def := state.local.M[x]
				state.assert(!def || state.panic("re-define %s", x)).assert(moveCdr(&c) || state.panic("define: missing bound value"))
				state.local.set(x, __exec(c.val, state))
			case LIST:
				lst := c.val.List()
				state.assert(!lst.MustProper().Empty() || state.panic("define: missing function name"))
				state.assert(moveCdr(&c) || state.panic("define: missing bound value"))
				s := L(Empty, head.SetText("define"), lst.val, L(c, head.SetText("lambda"), L(lst.next)))
				__exec(s, state)
			default:
				panic("define: missing binding symbol")
			}
			return state.debug.popAndReturn(Void)
		}
	}

	fn := __exec(head, state)
	state.assert(fn.Type() == FUNC || state.panic("invalid function: %v", head))
	cc := fn.Func()

	if cc.Macro && !state.macroMode {
		args := InitListBuilder().Append(F(cc))
		c.next.Foreach(func(v Value) bool { args = args.Append(v.Quote()); return true })
		state.macroMode = true
		u := __exec(args.Build(), state)
		if head.Type() == SYM {
			// The macro is bounded with a symbol and will not be altered ever, so we can replace the expression with the unwrapped one
			// The opposite case is like: ((if cond macro1 macro2) a b c ...), we have to unwrap every time
			*c = *u.nop(u.Type() == LIST && u.of(u) || u.of(L(Empty, head.SetText("if"), Void, Void, u))).List()
		}
		state.macroMode = false
		return state.debug.popAndReturn(__exec(u, state))
	}

	state.macroMode = false // clear the macro flag because a macro may call other macros as well, so more unwrappings may take place
	if cc.F == nil {
		m := &Context{parent: cc.natCls}
		for i, name := range cc.natArgNames {
			state.assert(moveCdr(&c) || state.panic("too few arguments, expect at least %d", i+1))
			m.set(name, __exec(c.val, state))
		}
		if cc.Vararg {
			values := InitListBuilder()
			c.next.Foreach(func(v Value) bool { values = values.Append(__exec(v, state)); return true })
			m.set(cc.name, values.Build())
		} else {
			state.assert(!c.HasProperCdr() || state.panic("too many arguments, expect exact %d", len(cc.natArgNames)))
		}
		state.local, expr, tailCall = m, cc.nat, true
		state.debug.nextLoc = (cc.Source)
		goto TAIL_CALL
	}

	args := InitListBuilder()
	c.next.Foreach(func(v Value) bool { args = args.Append(__exec(v, state)); return true })
	state.assert(args.Len == cc.MinArgNum || (cc.Vararg && args.Len >= cc.MinArgNum) || state.panic("call: expect %d arguments", cc.MinArgNum))

	state.debug.nextLoc = (cc.Source)
	s := State{Context: state.local, Caller: head, Stack: state.debug, Args: args.head, deadline: state.deadline}
	cc.F(&s)
	return state.debug.popAndReturn(s.Out)
}

func (ctx *Context) Parse(filename, text string) (v Value, err error) {
	s := (&scanner.Scanner{}).Init(strings.NewReader(text))
	s.Mode &^= scanner.ScanChars | scanner.ScanRawStrings
	s.Error = func(s *scanner.Scanner, msg string) { panic(msg) }
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("parse: %v at %s:%d:%d", r, filename, s.Pos().Line, s.Pos().Column)
		}
	}()

	v = ctx.scan(s, false)
	_ = v.Type() == LIST && v.of(L(v.List(), Y("if", 0), Void, Void)) || v.of(L(Empty, Y("if", 0), Void, Void, v))
	v = F(&Func{nat: v, natCls: ctx, natToplevel: true, Source: filename})
	return L(Empty, v), nil
}

func debugCatch(dbg *Stack, err *error) {
	if r := recover(); r != nil {
		if os.Getenv("SC_STACK") != "" {
			fmt.Println(string(debug.Stack()))
		}
		*err = fmt.Errorf("%v at %v", r, dbg)
	}
}

func (ctx *Context) Exec(deadline time.Time, c Value) (output Value, err error) {
	dbg := &Stack{nextLoc: "(toplevel)"}
	defer debugCatch(dbg, &err)
	return __exec(c, execState{local: ctx, debug: dbg, deadline: deadline.Unix() + 1}), nil
}

func (ctx *Context) RunFile(deadline time.Time, path string) (result Value, err error) {
	buf, err := ioutil.ReadFile(path)
	if err != nil {
		return Void, err
	}
	c, err := ctx.Parse(path, *(*string)(unsafe.Pointer(&buf)))
	if err != nil {
		return Void, err
	}
	{
		buf, _ := c.Marshal()
		c.Unmarshal(ctx, buf)
	}
	return ctx.Exec(deadline, c)
}

func (ctx *Context) Run(deadline time.Time, tmpl string) (result Value, err error) {
	c, err := ctx.Parse("(memory)", tmpl)
	if err != nil {
		return Void, err
	}
	return ctx.Exec(deadline, c)
}

func (ctx *Context) scan(s *scanner.Scanner, scanOne bool) Value {
	comp := InitListBuilder()
LOOP:
	for tok := s.Scan(); tok != scanner.EOF; tok = s.Scan() {
		// fmt.Println(s.TokenText())
		switch tok {
		case scanner.String, scanner.RawString:
			t, err := strconv.Unquote(s.TokenText())
			ctx.assert(err == nil || ctx.panic("invalid string: %q", s.TokenText()))
			comp = comp.Append(S(t))
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
					comp = comp.Append(I(int64(map[string]rune{
						"space": ' ', "newline": '\n', "return": '\r', "tab": '\t', "backspace": '\b', "alert": '\a', "form": '\f', "backslash": '\\',
					}[strings.ToLower(n)])))
				default:
					r, l := utf8.DecodeRuneInString(n)
					ctx.assert(l != 0 || ctx.panic("invalid char: %q", n))
					comp = comp.Append(I(int64(r)))
				}
			case 't', 'f':
				s.Scan()
				comp = comp.Append(B(pr == 't'))
			case 'v':
				s.Scan()
				comp = comp.Append(Void)
			default:
				comp = comp.Append(Y("#"+scanToDelim(s), uint32(s.Pos().Line)))
			}
		case ';':
			for ; ; s.Scan() {
				if next := s.Peek(); next == scanner.EOF || next == '\n' {
					break
				}
			}
		case '(', '[':
			comp = comp.Append(ctx.scan(s, false))
		case ')', ']':
			break LOOP
		case '.':
			c := ctx.scan(s, true)
			ctx.assert(comp.last != nil || ctx.panic("invalid dot syntax")) // invalid e.g.: ( . a )
			comp.last.SetCdr(c)
			s := s.Scan()
			ctx.assert(s == scanner.EOF || s == ']' || s == ')' || ctx.panic("invalid dot syntax")) // invalid e.g.: ( a . b c )
			return comp.Build()
		case '\'', '`':
			c := ctx.scan(s, true)
			ctx.assert(c != Void || ctx.panic("invalid quote syntax"))
			comp = comp.Append(L(Empty, Y(ifstr(tok == '\'', "quote", "quasiquote"), 0), c))
		case ',':
			sp := s.Peek() == '@'
			if sp {
				s.Scan()
			}
			c := ctx.scan(s, true)
			ctx.assert(c != Void || ctx.panic("invalid unquote syntax"))
			comp = comp.Append(L(Empty, Y(ifstr(sp, "unquote-splicing", "unquote"), 0), c))
		default:
			text := s.TokenText() + scanToDelim(s)
			if v := ParseNumber(text); v != Void {
				comp = comp.Append(v)
			} else {
				ctx.assert(tok != scanner.Int && tok != scanner.Float || ctx.panic("invalid number: %v", text))
				comp = comp.Append(Y(text, uint32(s.Pos().Line)))
			}
		}
		if scanOne && comp.Len >= 1 {
			return comp.head.val
		}
	}
	return comp.Build()
}

func scanToDelim(s *scanner.Scanner) string {
	for p := (bytes.Buffer{}); ; {
		next := s.Peek()
		if unicode.IsSpace(next) || next < 0 /* scanner.XXXX */ || strings.IndexRune("[]();", next) > -1 {
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

func ifstr(v bool, t, f string) string {
	if v {
		return t
	}
	return f
}
func ifint(v bool, t, f int) int {
	if v {
		return t
	}
	return f
}
func panicif(v bool, t string) {
	if v {
		panic(t)
	}
}

// V creates Value from interface{}
func V(v interface{}) (va Value) {
	if vv, ok := v.(Value); ok {
		return vv
	} else if f, ok := v.(*Func); ok {
		return F(f)
	}
	switch rv := reflect.ValueOf(v); rv.Kind() {
	case reflect.Interface:
		return V(rv.Elem())
	case reflect.Invalid:
		return Void
	case reflect.Int64, reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32:
		return I(rv.Int())
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		return I(int64(rv.Uint()))
	case reflect.Float32, reflect.Float64:
		return N(rv.Float())
	case reflect.String:
		return S(rv.String())
	case reflect.Bool:
		return B(rv.Bool())
	case reflect.Func:
		rt := rv.Type()
		f, rtNumIn := &Func{Vararg: rt.IsVariadic()}, rt.NumIn()
		f.MinArgNum = rtNumIn + ifint(f.Vararg, -1, 0) + ifint(rtNumIn > 0 && rt.In(0) == stateType, -1, 0)
		f.F = func(s *State) {
			ins := make([]reflect.Value, 0, rtNumIn)
			for i := 0; i < rtNumIn+ifint(f.Vararg, -1, 0); i++ {
				if t := rt.In(i); i == 0 && t == stateType {
					ins = append(ins, reflect.ValueOf(s))
				} else {
					ins = append(ins, s.In().TypedVal(t))
				}
			}
			s.Args.Foreach(func(v Value) bool { ins = append(ins, s.In().TypedVal(rt.In(rtNumIn-1).Elem())); return true })
			switch outs := rv.Call(ins); rt.NumOut() {
			case 1:
				s.Out = V(outs[0].Interface())
			case 2:
				err, _ := outs[1].Interface().(error)
				s.Out.nop(err != nil && s.Out.of(V(err)) || s.Out.of(V(outs[0].Interface())))
			default:
				r := InitListBuilder()
				for _, o := range outs {
					r = r.Append(V(o.Interface()))
				}
				s.Out.nop(r.Len != 0 && s.Out.of(r.Build()) || s.Out.of(Void))
			}
		}
		return F(f)
	}
	return Value{val: uint64(INTF), ptr: unsafe.Pointer(&v)}
}

func L(lst *Pair, l ...Value) Value {
	for i := len(l) - 1; i >= 0; i-- {
		n := &Pair{val: l[i], next: lst}
		lst = n
	}
	return Value{val: uint64(LIST), ptr: unsafe.Pointer(lst)}
}

func N(v float64) (n Value) {
	return n.nop(float64(int64(v)) == v && n.of(I(int64(v))) || n.of(Value{val: math.Float64bits(v), ptr: float64Marker}))
}

func I(v int64) (i Value) {
	return Value{val: uint64(v), ptr: int64Marker}
}

func B(v bool) (b Value) {
	return b.nop(v && b.of(Value{val: 1, ptr: boolMarker}) || b.of(Value{val: 0, ptr: boolMarker}))
}

func Y(v string, ln uint32) Value {
	return Value{ptr: unsafe.Pointer(&v), val: 1<<51 | uint64(ln)}
}

func S(v string) (vs Value) {
	return Value{val: uint64(TEXT), ptr: unsafe.Pointer(&v)}
}

func F(f *Func) Value {
	return Value{val: uint64(FUNC), ptr: unsafe.Pointer(f)}
}

func (v Value) Quote() (q Value) {
	t := v.Type()
	return q.nop((t == LIST || t == SYM) && q.of(L(Empty, Quote, v)) || q.of(v))
}

func (v Value) Type() ValueType {
	switch v.ptr {
	case boolMarker:
		return BOOL
	case int64Marker, float64Marker:
		return NUM
	}
	switch v.val {
	case uint64(LIST), uint64(FUNC), uint64(TEXT), uint64(INTF):
		return ValueType(v.val)
	}
	if v.val >= 1<<51 {
		return SYM
	}
	if v == Void {
		return VOID
	}
	panic("corrupted value")
}

func (v Value) stringify(goStyle bool) string {
	switch v.Type() {
	case NUM:
		vf, vi, vIsInt := v.Number()
		if vIsInt {
			return strconv.FormatInt(vi, 10)
		}
		return strconv.FormatFloat(vf, 'f', -1, 64)
	case TEXT:
		return strconv.Quote(v.Text())
	case SYM:
		return v.Text() + ifstr(v.SymLineInfo() > 0, fmt.Sprintf(ifstr(goStyle, " /*L%d*/", " #|L%d|#"), v.SymLineInfo()), "")
	case LIST:
		p := bytes.NewBufferString("( ")
		for vl := v.List(); vl != nil && !vl.empty; vl = vl.next {
			p.WriteString(ifstr(vl.next == nil, ". ", ""))
			p.WriteString(vl.val.stringify(goStyle))
			p.WriteString(" ")
		}
		p.WriteString(")")
		return p.String()
	case BOOL:
		return ifstr(v.Bool(), ifstr(goStyle, "true", "#t"), ifstr(goStyle, "false", "#f"))
	case INTF:
		return "#" + fmt.Sprintf("%#v", v.Interface())
	case FUNC:
		return v.Func().String()
	default:
		return ifstr(goStyle, "nil", "#v")
	}
}

func (v Value) Interface() interface{} {
	switch v.Type() {
	case NUM:
		vf, vi, vIsInt := v.Number()
		if vIsInt {
			return vi
		}
		return vf
	case TEXT, SYM:
		return v.Text()
	case LIST:
		var a []interface{}
		v.List().Foreach(func(v Value) bool { a = append(a, v.Interface()); return true })
		return a
	case BOOL:
		return v.Bool()
	case INTF:
		return *(*interface{})(v.ptr)
	case FUNC:
		return v.Func()
	default:
		return nil
	}
}

func (v Value) Equals(v2 Value) bool {
	if v == v2 {
		return true
	} else if vflag, v2flag := v.Type(), v2.Type(); vflag == v2flag {
		switch vflag {
		case SYM, TEXT:
			return v.Text() == v2.Text()
		case INTF:
			return v.Interface() == v2.Interface()
		}
	}
	return false
}

func (v Value) findSym(depth int) (string, uint32) {
	if t := v.Type(); t == SYM {
		return strings.Repeat("(", depth) + v.Text() + strings.Repeat(" ...)", depth), v.SymLineInfo()
	} else if t == LIST {
		return v.List().val.findSym(depth + 1)
	}
	return "", 0
}
func (v Value) expect(s *State, t ValueType) Value {
	s.assert(v.Type() == t || s.panic("invalid argument #%d, expect %s, got %v", s.argIdx, Types[t], v))
	return v
}

func (v Value) Number() (floatVal float64, intVal int64, isInt bool) {
	if v.ptr == int64Marker {
		return float64(int64(v.val)), int64(v.val), true
	}
	f := math.Float64frombits(v.val)
	return f, int64(f), false
}
func (v Value) Int() int64 {
	if v.ptr == int64Marker {
		return int64(v.val)
	}
	return int64(math.Float64frombits(v.val))
}
func (v Value) Func() *Func               { return (*Func)(v.ptr) }
func (v Value) Bool() bool                { return v.val == 1 }
func (v Value) Text() string              { return *(*string)(v.ptr) }
func (v Value) List() *Pair               { return (*Pair)(v.ptr) }
func (v Value) SetText(text string) Value { return Y(text, uint32(v.Type()/SYM)*v.SymLineInfo()) }
func (v Value) SymLineInfo() uint32       { return uint32(v.val) }
func (v Value) IsFalse() bool             { return v == Void || v.val == 0 } // 0: void, 1: false
func (v Value) String() string            { return v.stringify(false) }
func (v Value) GoString() string          { return fmt.Sprintf("{val:%016x ptr:%016x}", v.val, v.ptr) }

func (v *Value) nop(b bool) Value { return *v }
func (v *Value) of(v2 Value) bool { *v = v2; return true }

func (p *Pair) Car() Value           { panicif(p.Empty(), "car: empty list"); return p.val }
func (p *Pair) SetCar(v Value) *Pair { panicif(p.Empty(), "car: empty list"); p.val = v; return p }
func (p *Pair) Improper() bool       { return p.next == nil && !p.empty }
func (p *Pair) Empty() bool          { return p.next == nil && p.empty }
func (p *Pair) MustProper() *Pair    { panicif(p.Improper(), "improper list"); return p }
func (p *Pair) HasProperCdr() bool   { return p.next != nil && !p.next.MustProper().Empty() }
func (p *Pair) Length() (length int) {
	for ; !p.MustProper().Empty(); p = p.next {
		length++
	}
	return
}
func (p *Pair) Foreach(cb func(Value) bool) {
	for flag := true; flag && !p.MustProper().Empty(); p = p.next {
		flag = cb(p.val)
	}
}
func (p *Pair) ToSlice() (s []Value) {
	p.Foreach(func(v Value) bool { s = append(s, v); return true })
	return
}
func (p *Pair) match(state execState, pattern *Pair, metWildcard bool, symbols map[string]struct{}, m map[string]Value) bool {
	if pattern.MustProper().Empty() {
		return p.MustProper().Empty()
	}
	isWildcard := func(s string) string {
		if strings.HasSuffix(s, "*") {
			panicif(metWildcard, "multiple wildcards in one pattern")
			return ifstr(len(s) == 1, "*", s[:len(s)-1])
		}
		return ""
	}
	if p.MustProper().Empty() {
		if pattern.val.Type() == SYM && !pattern.HasProperCdr() {
			if w := isWildcard(pattern.val.Text()); w != "" {
				m[w] = L(Empty)
				return true
			}
		}
		return false
	}
	switch pattern.val.Type() {
	case SYM:
		sym := pattern.val.Text()
		if sym == "_" {
			break
		}
		if _, ok := symbols[sym]; ok {
			if !pattern.val.Equals(p.val) {
				return false
			}
			break
		}
		if w := isWildcard(sym); w != "" {
			if pattern.HasProperCdr() {
				n := p.Length() - pattern.next.Length()
				if n < 0 { // the remaining symbols in 'p' is less than 'pattern', so we are sure the match will fail
					return false
				}
				// The first n symbols will go into 'ww'
				ww := InitListBuilder()
				for ; n > 0; n-- {
					ww = ww.Append(p.val)
					p = p.next
				}
				m[w] = ww.Build()
				return p.match(state, pattern.next, true, symbols, m)
			}
			m[w] = L(p)
			return true
		}
		if strings.HasPrefix(sym, "#:") {
			if !p.val.Equals(pattern.val) {
				return false
			}
			break
		}
		m[sym] = p.val
	case LIST:
		if lst := pattern.val.List(); lst.val.Type() == SYM && lst.val.Text() == "quote" {
			if __exec(lst.next.val, execState{
				deadline: state.deadline,
				debug:    state.debug,
				local:    &Context{parent: state.local, M: map[string]Value{"_": p.val}},
			}).IsFalse() {
				return false
			}
			m["_"] = p.val
			break
		}
		if p.val.Type() != LIST {
			return false
		}
		if !p.val.List().match(state, pattern.val.List(), false, symbols, m) {
			return false
		}
	default:
		if !p.val.Equals(pattern.val) {
			return false
		}
	}
	return p.next.match(state, pattern.next, false, symbols, m)
}

// Take takes n values from the list, -1 means all values, -2 means all but the last value
func (p *Pair) Take(n int) *Pair {
	b := InitListBuilder()
	for ; p != nil && !p.Empty() && (b.Len < n || n < 0); p = p.next {
		b = b.Append(p.val)
	}
	if n == -2 {
		panicif(b.last == nil, "take(-2): empty list")
		*b.last = *Empty
	} else if n == -1 { // take all, do nothing
	} else if b.Len != n {
		panic(fmt.Errorf("take(%d): not enough values (%d)", n, b.Len))
	}
	return b.head
}
func (p *Pair) Last() (last *Pair) {
	for ; p != nil && !p.Empty(); p = p.next {
		last = p
	}
	return
}
func (p *Pair) Proper() bool {
	for ; ; p = p.next {
		if p.Improper() || p.Empty() {
			return p.Empty()
		}
	}
}
func (p *Pair) Cdr() (v Value) {
	p = p.next
	panicif(p == nil, "cdr: empty list")
	return v.nop(p.Improper() && v.of(p.val) || v.of(L(p)))
}
func (p *Pair) SetCdr(v Value) *Pair {
	panicif(p.Empty(), "cdr: empty list")
	if v.Type() == LIST {
		p.next = v.List()
	} else {
		p.next = &Pair{val: v}
	}
	return p
}
func moveCdr(ll **Pair) bool {
	if (*ll).HasProperCdr() {
		*ll = (*ll).next
		return true
	}
	*ll = Empty
	return false
}
func Cons(v, v2 Value) *Pair           { return (&Pair{val: v}).SetCdr(v2) }
func InitListBuilder() (b ListBuilder) { b.Cur = &Pair{empty: true}; b.head = b.Cur; return b }
func (b ListBuilder) Build() Value     { return L(b.head) }
func (b ListBuilder) Append(v Value) ListBuilder {
	panicif(!b.Cur.empty, "append to improper list")
	b.Cur.val, b.Cur.next, b.Cur.empty = v, &Pair{empty: true}, false
	b.last = b.Cur
	b.Cur, b.Len = b.Cur.next, b.Len+1
	return b
}
func ParseNumber(text string) (vn Value) {
	if v, err := strconv.ParseInt(text, 0, 64); err == nil {
		return I(v)
	}
	v, err := strconv.ParseFloat(text, 64)
	return vn.nop(err == nil && vn.of(N(v)) || vn.of(Void))
}
