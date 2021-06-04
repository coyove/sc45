package sc45

import (
	"bytes"
	"fmt"
	"io/ioutil"
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
	Default, Now, Forever = &Context{}, func() int64 { return time.Now().Unix() }, time.Unix(1<<32, 0)
	Void, Quote, Empty    = Value{}, Sym("quote", 0), &Pair{empty: true}
	stateType             = reflect.TypeOf(&State{})
	charNames             = map[string]rune{
		"space":     ' ',
		"newline":   '\n',
		"return":    '\r',
		"tab":       '\t',
		"backspace": '\b',
		"alert":     '\a',
		"form":      '\f',
		"backslash": '\\',
	}
)

type (
	Function struct {
		Source         string   // filename inherited from the toplevel lambda
		Vararg         bool     // is variadic
		Macro          bool     // is macro
		NativeToplevel bool     // native: toplevel
		NativeArgs     []string // native: arguments binding list
		NativeVararg   string
		NativeCtx      *Context // native: closure
		Native         Value    // native
		GoMinArgNum    int      // go: minimal arguments required
		GoName         string
		Go             func(*State) // go
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
	execState struct {
		assertable
		deadline  int64
		debug     *Stack
		local     *Context
		macroMode bool
	}
	assertable struct {
		err error
	}
)

func New() *Context {
	return Default.Copy()
}

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

func (s *Stack) LastLocation() string {
	return s.Frames[len(s.Frames)-2].Loc
}

func (s *Stack) String() (p string) {
	for _, k := range s.Frames {
		if sym, li := k.K.FindFirstSym(0); sym != "" && li > 0 {
			p = sym + " in " + k.Loc + ":" + strconv.FormatInt(int64(li), 10) + "\n" + p
		}
	}
	return strings.TrimSpace(p)
}

func (f *Function) Call(a ...interface{}) (result Value, err error) {
	v := InitListBuilder()
	for _, a := range a {
		v = v.Append(Val(a))
	}
	return f.CallOnStack(nil, Forever, v.Build())
}

func (f *Function) CallOnStack(dbg *Stack, deadline time.Time, args Value) (result Value, err error) {
	expr := List(args.List(), Func(f).Quote())
	if dbg == nil {
		dbg = &Stack{nextLoc: "(call)"}
	}
	defer debugCatch(dbg, &err)
	return __exec(expr, execState{local: (*Context)(nil), debug: dbg, deadline: deadline.Unix()}), nil
}

func (f *Function) String() string {
	if f.Native.Void() {
		return ifstr(f.GoName == "", "#|missing native code|#", f.GoName+" #|native code|#")
	}
	if f.Vararg && len(f.NativeArgs) == 0 {
		return ifstr(f.Macro, "(lambda-syntax ", "(lambda ") + f.NativeVararg + " " + f.Native.String() + ")"
	}
	return ifstr(f.Macro, "(lambda-syntax (", "(lambda (") + strings.Join(f.NativeArgs, " ") + ifstr(f.Vararg, " . "+f.NativeVararg, "") + ") " + f.Native.String() + ")"
}

// Next pops an argument
func (s *State) Next() Value {
	s.assert(!s.Args.MustProper().Empty() || s.panic("too few arguments, expect at least %d", s.argIdx+1))
	v := s.Args.val
	s.argIdx, s.LastIn = s.argIdx+1, v
	s.Args = s.Args.next
	return v
}
func (s *State) Nv() Value                 { return s.Next().expect(s, NumType) }
func (s *State) N() (float64, int64, bool) { return s.Next().expect(s, NumType).Num() }
func (s *State) I() int64                  { return s.Next().expect(s, NumType).Int() }
func (s *State) S() string                 { return s.Next().expect(s, StrType).Str() }
func (s *State) Y() string                 { return s.Next().expect(s, SymType).Str() }
func (s *State) L() *Pair                  { return s.Next().expect(s, ListType).List() }
func (s *State) B() bool                   { return s.Next().expect(s, BoolType).Bool() }
func (s *State) F() *Function              { return s.Next().expect(s, FuncType).Func() }
func (s *State) V() interface{}            { return s.Next().Interface() }

func (s *State) Deadline() time.Time {
	return time.Unix(s.deadline, 0)
}

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
	if v.Type() == FuncType && v.Func().Go != nil {
		v.Func().GoName = k
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
	if expr.Type() == ListType && !expr.List().MustProper().Empty() {
		lst := expr.List()
		if x := lst.val; x.Type() == SymType {
			switch x.Str() {
			case "unquote":
				state.assert(lst.ProperCdr() || state.panic("invalid unquote syntax"))
				return __exec(lst.next.val, state), nil
			case "unquote-splicing":
				state.assert(lst.ProperCdr() || state.panic("invalid unquote-splicing syntax"))
				v := __exec(lst.next.val, state)
				if v.Type() == ListType {
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
	case ListType: // evaluating the list
	case SymType:
		v, ok := state.local.Load(expr.Str())
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
		return List(Empty)
	}

	head := c.val
	state.debug.push(head, tailCall)

	if head.Type() == SymType {
		switch va := head.Str(); va {
		case "if", "lambda-body":
			state.assert(moveCdr(&c) || state.panic("invalid if syntax, missing condition"))
			if !__exec(c.val, state).Falsy() {
				state.assert(moveCdr(&c) || state.panic("invalid if syntax, missing true branch"))
				expr, tailCall = c.val, true // execute true-branch
				goto TAIL_CALL
			}
			moveCdr(&c)                                  // skip condition
			moveCdr(&c)                                  // skip true branch
			for ; !c.MustProper().Empty(); moveCdr(&c) { // execute rest statements: (if cond true-branch false-1 ... false-n)
				if !c.ProperCdr() {
					expr, tailCall = c.val, true
					goto TAIL_CALL
				}
				__exec(c.val, state)
			}
			return state.debug.popAndReturn(Void)
		case "lambda", "lambda-syntax":
			state.assert(moveCdr(&c) || state.panic("lambda: missing binding list"))
			f := &Function{NativeCtx: state.local, Macro: va != "lambda", Source: state.debug.LastLocation()}
			switch c.val.Type() {
			case SymType: // (lambda* args body)
				f.NativeVararg, f.Vararg = fmt.Sprint(c.val.Interface()), true
			case ListType: // (lambda* (a1 a2 ... an) body)
				for bindings := c.val.List(); bindings != nil; bindings = bindings.next {
					if p := fmt.Sprint(bindings.val.Interface()); bindings.Improper() {
						f.NativeVararg, f.Vararg = p, true
					} else if !bindings.Empty() {
						f.NativeArgs = append(f.NativeArgs, p)
					}
				}
			default:
				f.Vararg = true
			}
			state.assert(moveCdr(&c) || state.panic("lambda: missing body"))
			_ = c.ProperCdr() && f.Native.Set(List(c, head.SetStr("lambda-body"), Void, Void)) || f.Native.Set(c.val)
			return state.debug.popAndReturn(Func(f))
		case "match":
			state.assert(moveCdr(&c) || state.panic("match: missing source"))
			source := __exec(c.val, state)
			state.assert(moveCdr(&c) && c.val.Type() == ListType || state.panic("match: missing symbol list"))
			symbols := c.val.List().ToSlice()
		MATCH_NEXT:
			// ( (pattern subject) ... )
			state.assert(moveCdr(&c) && c.val.Type() == ListType && c.val.List().ProperCdr() || state.panic("match: invalid pattern"))
			pattern, subject, matched := c.val.List().val, c.val.List().next.val, false
			m := &Context{parent: state.local, M: map[string]Value{}}
			if pattern.Type() == ListType && source.Type() == ListType {
				var symbolmap map[string]struct{}
				if len(symbols) > 0 {
					symbolmap = map[string]struct{}{}
					for _, s := range symbols {
						symbolmap[s.Str()] = struct{}{}
					}
				}
				matched = source.List().match(state, pattern.List(), false, symbolmap, m.M)
			} else {
				matched = source.Equals(pattern)
			}
			if matched {
				return state.debug.popAndReturn(__exec(subject, execState{debug: state.debug, local: m, deadline: state.deadline}))
			}
			if c.ProperCdr() {
				goto MATCH_NEXT
			}
			return state.debug.popAndReturn(Void)
		case "quote":
			state.assert(moveCdr(&c) || state.panic("invalid quote syntax"))
			return state.debug.popAndReturn(c.val)
		case "quasiquote":
			state.assert(moveCdr(&c) || state.panic("invalid quasiquote syntax"))
			v, p := __execQuasi(c.val, state)
			return state.debug.popAndReturn(v.nop(p != nil && v.Set(List(p)) || v.Set(v)))
		case "unquote", "unquote-splicing":
			panic(fmt.Errorf("unquote outside quasiquote"))
		case "set!":
			state.assert(moveCdr(&c) && c.val.Type() == SymType || state.panic("set!: missing symbol"))
			x := c.val.Str()
			oldValue, m := state.local.find(x)
			state.assert(m != nil || state.panic("set!: unbound %s", x))
			state.assert(moveCdr(&c) || state.panic("set!: missing bound value"))
			state.assert(oldValue.Type() != FuncType || !oldValue.Func().Macro || state.panic("set!: alter bounded macro"))
			m.set(x, __exec(c.val, state))
			return state.debug.popAndReturn(Void)
		case "define":
			switch moveCdr(&c); c.val.Type() {
			case SymType:
				x := c.val.Str()
				_, def := state.local.M[x]
				state.assert(!def || state.panic("re-define %s", x)).assert(moveCdr(&c) || state.panic("define: missing bound value"))
				state.local.set(x, __exec(c.val, state))
			case ListType:
				lst := c.val.List()
				state.assert(!lst.MustProper().Empty() || state.panic("define: missing function name"))
				state.assert(moveCdr(&c) || state.panic("define: missing bound value"))
				s := List(Empty, head.SetStr("define"), lst.val, List(c, head.SetStr("lambda"), List(lst.next)))
				__exec(s, state)
			default:
				panic("define: missing binding symbol")
			}
			return state.debug.popAndReturn(Void)
		}
	}

	fn := __exec(head, state)
	state.assert(fn.Type() == FuncType || state.panic("invalid function: %v", head))
	cc := fn.Func()

	if cc.Macro && !state.macroMode {
		args := InitListBuilder().Append(Func(cc))
		c.next.Foreach(func(v Value) bool { args = args.Append(v.Quote()); return true })
		state.macroMode = true
		u := __exec(args.Build(), state)
		if head.Type() == SymType {
			// The macro is bounded with a symbol and will not be altered ever, so we can replace the expression with the unwrapped one
			// The opposite case is like: ((if cond macro1 macro2) a b c ...), we have to unwrap every time
			*c = *u.nop(u.Type() == ListType && u.Set(u) || u.Set(List(Empty, head.SetStr("if"), Void, Void, u))).List()
		}
		state.macroMode = false
		return state.debug.popAndReturn(__exec(u, state))
	}

	state.macroMode = false // clear the macro flag because a macro may call other macros as well, so more unwrappings may take place
	if cc.Go == nil {
		m := &Context{parent: cc.NativeCtx}
		for i, name := range cc.NativeArgs {
			state.assert(moveCdr(&c) || state.panic("too few arguments, expect at least %d", i+1))
			m.set(name, __exec(c.val, state))
		}
		if cc.Vararg {
			values := InitListBuilder()
			c.next.Foreach(func(v Value) bool { values = values.Append(__exec(v, state)); return true })
			m.set(cc.NativeVararg, values.Build())
		} else {
			state.assert(!c.ProperCdr() || state.panic("too many arguments, expect exact %d", len(cc.NativeArgs)))
		}
		state.local, expr, tailCall = m, cc.Native, true
		state.debug.nextLoc = (cc.Source)
		goto TAIL_CALL
	}

	args := InitListBuilder()
	c.next.Foreach(func(v Value) bool { args = args.Append(__exec(v, state)); return true })
	state.assert(args.Len == cc.GoMinArgNum || (cc.Vararg && args.Len >= cc.GoMinArgNum) || state.panic("call: expect %d arguments", cc.GoMinArgNum))

	state.debug.nextLoc = (cc.Source)
	s := State{Context: state.local, Caller: head, Stack: state.debug, Args: args.head, deadline: state.deadline}
	cc.Go(&s)
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
	_ = v.Type() == ListType && v.Set(List(v.List(), Sym("if", 0), Void, Void)) || v.Set(List(Empty, Sym("if", 0), Void, Void, v))
	v = Func(&Function{Native: v, NativeCtx: ctx, NativeToplevel: true, Source: filename})
	return List(Empty, v), nil
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
			comp = comp.Append(Str(t))
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
					comp = comp.Append(Int(int64(charNames[strings.ToLower(n)])))
				default:
					r, l := utf8.DecodeRuneInString(n)
					ctx.assert(l != 0 || ctx.panic("invalid char: %q", n))
					comp = comp.Append(Int(int64(r)))
				}
			case 't', 'f':
				s.Scan()
				comp = comp.Append(Bool(pr == 't'))
			case 'v':
				s.Scan()
				comp = comp.Append(Void)
			default:
				comp = comp.Append(Sym("#"+scanToDelim(s), uint32(s.Pos().Line)))
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
			comp = comp.Append(List(Empty, Sym(ifstr(tok == '\'', "quote", "quasiquote"), 0), c))
		case ',':
			sp := s.Peek() == '@'
			if sp {
				s.Scan()
			}
			c := ctx.scan(s, true)
			ctx.assert(c != Void || ctx.panic("invalid unquote syntax"))
			comp = comp.Append(List(Empty, Sym(ifstr(sp, "unquote-splicing", "unquote"), 0), c))
		default:
			text := s.TokenText() + scanToDelim(s)
			if v := ParseNumber(text); v != Void {
				comp = comp.Append(v)
			} else {
				ctx.assert(tok != scanner.Int && tok != scanner.Float || ctx.panic("invalid number: %v", text))
				comp = comp.Append(Sym(text, uint32(s.Pos().Line)))
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

func panicerr(err error) {
	if err != nil {
		panic(err)
	}
}

func ParseNumber(text string) (vn Value) {
	if v, err := strconv.ParseInt(text, 0, 64); err == nil {
		return Int(v)
	}
	v, err := strconv.ParseFloat(text, 64)
	return vn.nop(err == nil && vn.Set(Num(v)) || vn.Set(Void))
}
