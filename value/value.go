package value

import (
	"bytes"
	"fmt"
	"math"
	"reflect"
	"strconv"
	"strings"
	"unsafe"
)

type (
	Assertable struct {
		err error
	}

	Value struct {
		val uint64
		ptr unsafe.Pointer
	}

	Pair struct {
		Next  *Pair
		Val   Value
		empty bool
	}

	Func struct {
		Source string // filename inherited from the toplevel lambda
		Name   string // variadic argument name, native: last assigned name
		Vararg bool   // is variadic function
		Macro  bool   // is macro

		GoToplevel bool     // go toplevel
		GoArgNames []string // go arguments binding list
		GoCtx      *Context // go closure
		Go         Value    // go function

		MinArgNum int          // native: minimal arguments required
		Callee    func(*State) // native function
	}

	ExecState struct {
		Assertable
		Deadline  int64
		Debug     *Stack
		Local     *Context
		MacroMode bool
	}

	State struct {
		*Context
		Assertable
		argIdx              int
		deadline            int64
		Args                *Pair
		LastIn, Caller, Out Value
		Stack               *Stack
	}

	Context struct {
		Assertable
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
)

func New(v interface{}) (va Value) {
	if vv, ok := v.(Value); ok {
		return vv
	} else if f, ok := v.(*Func); ok {
		return Lambda(f)
	}
	switch rv := reflect.ValueOf(v); rv.Kind() {
	case reflect.Interface:
		return New(rv.Elem())
	case reflect.Invalid:
		return Void
	case reflect.Int64, reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32:
		return Int(rv.Int())
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		return Int(int64(rv.Uint()))
	case reflect.Float32, reflect.Float64:
		return Num(rv.Float())
	case reflect.String:
		return Text(rv.String())
	case reflect.Bool:
		return Bool(rv.Bool())
	case reflect.Func:
		rt := rv.Type()
		f, rtNumIn := &Func{Vararg: rt.IsVariadic()}, rt.NumIn()
		f.MinArgNum = rtNumIn + IfInt(f.Vararg, -1, 0) + IfInt(rtNumIn > 0 && rt.In(0) == stateType, -1, 0)
		f.Callee = func(s *State) {
			ins := make([]reflect.Value, 0, rtNumIn)
			for i := 0; i < rtNumIn+IfInt(f.Vararg, -1, 0); i++ {
				if t := rt.In(i); i == 0 && t == stateType {
					ins = append(ins, reflect.ValueOf(s))
				} else {
					ins = append(ins, s.Next().ReflectValue(t))
				}
			}
			s.Args.Foreach(func(v Value) bool { ins = append(ins, s.Next().ReflectValue(rt.In(rtNumIn-1).Elem())); return true })
			switch outs := rv.Call(ins); rt.NumOut() {
			case 0:
				s.Out = Void
			case 1:
				s.Out = New(outs[0].Interface())
			default:
				r := InitListBuilder()
				for _, o := range outs {
					r = r.Append(New(o.Interface()))
				}
				s.Out.nop(r.Len != 0 && s.Out.Set(r.Build()) || s.Out.Set(Void))
			}
		}
		return Lambda(f)
	}
	return Value{val: uint64(InterfaceType), ptr: unsafe.Pointer(&v)}
}

func List(lst *Pair, l ...Value) Value {
	for i := len(l) - 1; i >= 0; i-- {
		n := &Pair{Val: l[i], Next: lst}
		lst = n
	}
	return Value{val: uint64(ListType), ptr: unsafe.Pointer(lst)}
}

func Num(v float64) (n Value) {
	return n.nop(float64(int64(v)) == v && n.Set(Int(int64(v))) || n.Set(Value{val: math.Float64bits(v), ptr: float64Marker}))
}

func Int(v int64) (i Value) {
	return Value{val: uint64(v), ptr: int64Marker}
}

func Bool(v bool) (b Value) {
	return b.nop(v && b.Set(Value{val: 1, ptr: boolMarker}) || b.Set(Value{val: 0, ptr: boolMarker}))
}

func Sym(v string, ln uint32) Value {
	return Value{ptr: unsafe.Pointer(&v), val: 1<<51 | uint64(ln)}
}

func Text(v string) (vs Value) {
	return Value{val: uint64(TextType), ptr: unsafe.Pointer(&v)}
}

func Lambda(f *Func) Value {
	return Value{val: uint64(FuncType), ptr: unsafe.Pointer(f)}
}

func (v Value) Quote() (q Value) {
	if t := v.Type(); t == ListType || t == SymbolType {
		q = List(Empty, Quote, v)
	} else {
		q = v
	}
	return
}

func (v Value) Type() Type {
	switch v.ptr {
	case boolMarker:
		return BoolType
	case int64Marker, float64Marker:
		return NumberType
	}
	switch v.val {
	case uint64(ListType), uint64(FuncType), uint64(TextType), uint64(InterfaceType):
		return Type(v.val)
	}
	if v.val >= 1<<51 {
		return SymbolType
	}
	if v == Void {
		return VoidType
	}
	panic("corrupted value")
}

func (v Value) stringify(goStyle bool) string {
	switch v.Type() {
	case NumberType:
		vf, vi, vIsInt := v.Num()
		if vIsInt {
			return strconv.FormatInt(vi, 10)
		}
		return strconv.FormatFloat(vf, 'f', -1, 64)
	case TextType:
		return strconv.Quote(v.Text())
	case SymbolType:
		return v.Text() + IfStr(v.SymLineInfo() > 0, fmt.Sprintf(IfStr(goStyle, " /*L%d*/", " #|L%d|#"), v.SymLineInfo()), "")
	case ListType:
		p := bytes.NewBufferString("( ")
		for vl := v.List(); vl != nil && !vl.empty; vl = vl.Next {
			p.WriteString(IfStr(vl.Next == nil, ". ", ""))
			p.WriteString(vl.Val.stringify(goStyle))
			p.WriteString(" ")
		}
		p.WriteString(")")
		return p.String()
	case BoolType:
		return IfStr(v.Bool(), IfStr(goStyle, "true", "#t"), IfStr(goStyle, "false", "#f"))
	case InterfaceType:
		return "#" + fmt.Sprintf("%#v", v.Interface())
	case FuncType:
		return v.Func().String()
	default:
		return IfStr(goStyle, "nil", "#v")
	}
}

func (v Value) Interface() interface{} {
	switch v.Type() {
	case NumberType:
		vf, vi, vIsInt := v.Num()
		if vIsInt {
			return vi
		}
		return vf
	case TextType, SymbolType:
		return v.Text()
	case ListType:
		var a []interface{}
		v.List().Foreach(func(v Value) bool { a = append(a, v.Interface()); return true })
		return a
	case BoolType:
		return v.Bool()
	case InterfaceType:
		return *(*interface{})(v.ptr)
	case FuncType:
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
		case SymbolType, TextType:
			return v.Text() == v2.Text()
		case InterfaceType:
			return v.Interface() == v2.Interface()
		}
	}
	return false
}

func (v Value) Num() (floatVal float64, intVal int64, isInt bool) {
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

func (v Value) Func() *Func {
	return (*Func)(v.ptr)
} // unsafe

func (v Value) Bool() bool {
	return v.val == 1
} // unsafe

func (v Value) Text() string {
	return *(*string)(v.ptr)
} // unsafe

func (v Value) List() *Pair {
	return (*Pair)(v.ptr)
} // unsafe

func (v Value) SetText(text string) Value {
	return Sym(text, uint32(v.Type()/SymbolType)*v.SymLineInfo())
} // unsafe

func (v Value) SymLineInfo() uint32 {
	return uint32(v.val)
} // unsafe

func (v Value) Falsy() bool {
	return v == Void || v.val == 0
} // unsafe

func (v Value) Void() bool {
	return v == Void
}

func (v Value) String() string {
	return v.stringify(false)
}

func (v Value) GoString() string {
	return fmt.Sprintf("{val:%016x ptr:%016x}", v.val, v.ptr)
}

func (v *Value) nop(b bool) Value {
	return *v
}

func (v *Value) Set(v2 Value) bool {
	*v = v2
	return true
}

func (v Value) ReflectValue(t reflect.Type) reflect.Value {
	if t == valueType {
		return reflect.ValueOf(v)
	}
	if v.Type() == ListType {
		s := reflect.MakeSlice(t, 0, 0)
		v.List().Foreach(func(v Value) bool { s = reflect.Append(s, v.ReflectValue(t.Elem())); return true })
		return s
	}
	vv := v.Interface()
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
	if v.Type() == NumberType {
		return rv.Convert(t)
	}
	return rv
}

func (v Value) Add(v2 Value) (n Value) {
	vf, vi, vIsInt := v.Num()
	v2f, v2i, v2IsInt := v2.Num()
	if vIsInt && v2IsInt {
		return Int(vi + v2i)
	}
	return Num(vf + v2f)
}

func (v Value) Sub(v2 Value) Value {
	vf, vi, vIsInt := v.Num()
	v2f, v2i, v2IsInt := v2.Num()
	if vIsInt && v2IsInt {
		return Int(vi - v2i)
	}
	return Num(vf - v2f)
}

func (v Value) Mul(v2 Value) Value {
	vf, vi, vIsInt := v.Num()
	v2f, v2i, v2IsInt := v2.Num()
	if vIsInt && v2IsInt {
		return Int(vi * v2i)
	}
	return Num(vf * v2f)
}

func (v Value) Div(v2 Value) Value {
	vf, vi, vIsInt := v.Num()
	v2f, v2i, v2IsInt := v2.Num()
	if vIsInt && v2IsInt {
		if r := vi / v2i; r*v2i == vi {
			return Int(r)
		}
	}
	return Num(vf / v2f)
}

func (v Value) IDiv(v2 Value) Value {
	vf, vi, vIsInt := v.Num()
	v2f, v2i, v2IsInt := v2.Num()
	if vIsInt && v2IsInt {
		return Int(vi / v2i)
	}
	return Int(int64(vf / v2f))
}

func (v Value) Less(v2 Value) bool {
	vf, vi, vIsInt := v.Num()
	v2f, v2i, v2IsInt := v2.Num()
	if vIsInt && v2IsInt {
		return vi < v2i
	}
	return vf < v2f
}

func (v Value) LessEqual(v2 Value) bool {
	vf, vi, vIsInt := v.Num()
	v2f, v2i, v2IsInt := v2.Num()
	if vIsInt && v2IsInt {
		return vi <= v2i
	}
	return vf <= v2f
}

func (v Value) MustNum() Value {
	return v.check(NumberType)
}

func (v Value) MustText() Value {
	return v.check(TextType)
}

func (v Value) MustList() Value {
	return v.check(ListType)
}

func (v Value) MustSym() Value {
	return v.check(SymbolType)
}

func (v Value) MustBool() Value {
	return v.check(BoolType)
}

func NewRec(v interface{}) Value {
	rv := reflect.ValueOf(v)
	switch rv.Kind() {
	case reflect.Slice, reflect.Array:
		l := InitListBuilder()
		for i := 0; i < rv.Len(); i++ {
			l = l.Append(NewRec(rv.Index(i).Interface()))
		}
		return l.Build()
	}
	return New(v)
}

func (v Value) FindFirstSym(depth int) (string, uint32) {
	switch v.Type() {
	case SymbolType:
		return strings.Repeat("(", depth) + v.Text() + strings.Repeat(" ...)", depth), v.SymLineInfo()
	case ListType:
		return v.List().Val.FindFirstSym(depth + 1)
	}
	return "", 0
}

func (v Value) expect(s *State, t Type) Value {
	s.Assert(v.Type() == t || s.Panic("invalid argument #%d, expect %s, got %v", s.argIdx, Types[t], v))
	return v
}

func (p *Pair) Car() Value {
	PanicIf(p.Empty(), "car: empty list")
	return p.Val
}

func (p *Pair) SetCar(v Value) *Pair {
	PanicIf(p.Empty(), "car: empty list")
	p.Val = v
	return p
}

func (p *Pair) Improper() bool {
	return p.Next == nil && !p.empty
}

func (p *Pair) Empty() bool {
	return p.Next == nil && p.empty
}

func (p *Pair) MustProper() *Pair {
	PanicIf(p.Improper(), "improper list")
	return p
}

func (p *Pair) HasProperCdr() bool {
	return p.Next != nil && !p.Next.MustProper().Empty()
}

func (p *Pair) Length() (length int) {
	for ; !p.MustProper().Empty(); p = p.Next {
		length++
	}
	return
}

func (p *Pair) Foreach(cb func(Value) bool) {
	for flag := true; flag && !p.MustProper().Empty(); p = p.Next {
		flag = cb(p.Val)
	}
}

func (p *Pair) ToSlice() (s []Value) {
	p.Foreach(func(v Value) bool { s = append(s, v); return true })
	return
}

func (p *Pair) Match(state ExecState, exec func(Value, ExecState) Value, pattern *Pair, symbols map[string]struct{}) (map[string]Value, bool) {
	m := map[string]Value{}
	return m, p.match(state, exec, pattern, false, symbols, m)
}

func (p *Pair) match(state ExecState, exec func(Value, ExecState) Value, pattern *Pair, metWildcard bool, symbols map[string]struct{}, m map[string]Value) bool {
	if pattern.MustProper().Empty() {
		return p.MustProper().Empty()
	}
	isWildcard := func(s string) string {
		if strings.HasSuffix(s, "*") {
			PanicIf(metWildcard, "multiple wildcards in one pattern")
			return IfStr(len(s) == 1, "*", s[:len(s)-1])
		}
		return ""
	}
	if p.MustProper().Empty() {
		if pattern.Val.Type() == SymbolType && !pattern.HasProperCdr() {
			if w := isWildcard(pattern.Val.Text()); w != "" {
				m[w] = List(Empty)
				return true
			}
		}
		return false
	}
	switch pattern.Val.Type() {
	case SymbolType:
		sym := pattern.Val.Text()
		if sym == "_" {
			break
		}
		if _, ok := symbols[sym]; ok {
			if !pattern.Val.Equals(p.Val) {
				return false
			}
			break
		}
		if w := isWildcard(sym); w != "" {
			if pattern.HasProperCdr() {
				n := p.Length() - pattern.Next.Length()
				if n < 0 { // the remaining symbols in 'p' is less than 'pattern', so we are sure the match will fail
					return false
				}
				// The first n symbols will go into 'ww'
				ww := InitListBuilder()
				for ; n > 0; n-- {
					ww = ww.Append(p.Val)
					p = p.Next
				}
				m[w] = ww.Build()
				return p.match(state, exec, pattern.Next, true, symbols, m)
			}
			m[w] = List(p)
			return true
		}
		if strings.HasPrefix(sym, "#:") {
			if !p.Val.Equals(pattern.Val) {
				return false
			}
			break
		}
		m[sym] = p.Val
	case ListType:
		if lst := pattern.Val.List(); lst.Val.Type() == SymbolType && lst.Val.Text() == "quote" {
			if exec(lst.Next.Val, ExecState{
				Deadline: state.Deadline,
				Debug:    state.Debug,
				Local:    &Context{parent: state.Local, M: map[string]Value{"_": p.Val}},
			}).Falsy() {
				return false
			}
			m["_"] = p.Val
			break
		}
		if p.Val.Type() != ListType {
			return false
		}
		if !p.Val.List().match(state, exec, pattern.Val.List(), false, symbols, m) {
			return false
		}
	default:
		if !p.Val.Equals(pattern.Val) {
			return false
		}
	}
	return p.Next.match(state, exec, pattern.Next, false, symbols, m)
}

// Take takes n values from the list, -1 means all values, -2 means all but the last value
func (p *Pair) Take(n int) *Pair {
	b := InitListBuilder()
	for ; p != nil && !p.Empty() && (b.Len < n || n < 0); p = p.Next {
		b = b.Append(p.Val)
	}
	if n == -2 {
		PanicIf(b.last == nil, "take(-2): empty list")
		*b.last = *Empty
	} else if n == -1 {
		// take all, do nothing
	} else if b.Len != n {
		panic(fmt.Errorf("take(%d): not enough values (%d)", n, b.Len))
	}
	return b.head
}

func (p *Pair) Last() (last *Pair) {
	for ; p != nil && !p.Empty(); p = p.Next {
		last = p
	}
	return
}

func (p *Pair) Proper() bool {
	for ; ; p = p.Next {
		if p.Improper() || p.Empty() {
			return p.Empty()
		}
	}
}

func (p *Pair) Cdr() (v Value) {
	p = p.Next
	PanicIf(p == nil, "cdr: empty list")
	return v.nop(p.Improper() && v.Set(p.Val) || v.Set(List(p)))
}

func (p *Pair) SetCdr(v Value) *Pair {
	PanicIf(p.Empty(), "cdr: empty list")
	if v.Type() == ListType {
		p.Next = v.List()
	} else {
		p.Next = &Pair{Val: v}
	}
	return p
}

func (f *Func) String() string {
	if f.Go == Void {
		return IfStr(f.Name == "", "#|missing native code|#", f.Name+" #|native code|#")
	}
	if f.Vararg && len(f.GoArgNames) == 0 {
		return IfStr(f.Macro, "(lambda-syntax ", "(lambda ") + f.Name + " " + f.Go.String() + ")"
	}
	s := IfStr(f.Macro, "lambda-syntax (", "lambda (") + strings.Join(f.GoArgNames, " ")
	if f.Vararg {
		s += " . " + f.Name + ") "
	} else {
		s += ") "
	}
	return "(" + s + f.Go.String() + ")"
}

func InitListBuilder() (b ListBuilder) {
	b.Cur = &Pair{empty: true}
	b.head = b.Cur
	return b
}

func (b ListBuilder) Build() Value {
	return List(b.head)
}

func (b ListBuilder) Append(v Value) ListBuilder {
	PanicIf(!b.Cur.empty, "append to improper list")
	b.Cur.Val, b.Cur.Next, b.Cur.empty = v, &Pair{empty: true}, false
	b.last = b.Cur
	b.Cur, b.Len = b.Cur.Next, b.Len+1
	return b
}

func (e *Assertable) Assert(ok bool) *Assertable {
	if !ok {
		panic(e.err)
	}
	return e
}

func (e *Assertable) Panic(t string, a ...interface{}) bool {
	e.err = fmt.Errorf(t, a...)
	return false
}

func (s *State) Next() Value {
	s.Assert(!s.Args.MustProper().Empty() || s.Panic("too few arguments, expect at least %d", s.argIdx+1))
	v := s.Args.Val
	s.argIdx, s.LastIn = s.argIdx+1, v
	s.Args = s.Args.Next
	return v
}

func (t Value) check(wrong Type) Value {
	if t.Type() != wrong {
		panic("invalid value, expect " + Types[t.Type()] + ", got " + Types[wrong])
	}
	return t
}
