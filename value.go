package sc45

import (
	"bytes"
	"crypto/sha1"
	"encoding/binary"
	"encoding/gob"
	"fmt"
	"io"
	"math"
	"reflect"
	"strconv"
	"strings"
	"unsafe"
)

type Type byte

type Value struct {
	val uint64
	ptr unsafe.Pointer
}

var (
	goTypesReg    = map[uint32]reflect.Type{}
	goTypesRegRev = map[reflect.Type]uint32{}
	int64Marker   = unsafe.Pointer(new(int64))
	boolMarker    = unsafe.Pointer(new(int64))
	float64Marker = unsafe.Pointer(new(int64))
)

var Types = map[Type]string{
	StrType:       "string",
	SymType:       "symbol",
	NumType:       "number",
	ListType:      "list",
	InterfaceType: "interface",
	FuncType:      "function",
	VoidType:      "void",
	BoolType:      "boolean",
}

const StrType, SymType, NumType, BoolType, ListType, InterfaceType, FuncType, VoidType Type = 's', 'y', 'n', 'b', 'l', 'i', 'f', 'v'

func RegisterGoType(dummy interface{}) {
	t := reflect.TypeOf(dummy)
	x := sha1.Sum([]byte(t.String()))
	h := binary.BigEndian.Uint32(x[:4])
	goTypesReg[h] = t
	goTypesRegRev[t] = h
}

// Val creates a Value struct
func Val(v interface{}) (va Value) {
	if vv, ok := v.(Value); ok {
		return vv
	}
	if f, ok := v.(*Function); ok {
		return Func(f)
	}
	switch rv := reflect.ValueOf(v); rv.Kind() {
	case reflect.Interface:
		return Val(rv.Elem())
	case reflect.Invalid:
		return Void
	case reflect.Int64, reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32:
		return Int(rv.Int())
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		return Int(int64(rv.Uint()))
	case reflect.Float32, reflect.Float64:
		return Num(rv.Float())
	case reflect.String:
		return Str(rv.String())
	case reflect.Bool:
		return Bool(rv.Bool())
	case reflect.Func:
		rt := rv.Type()
		f, rtNumIn := &Function{Vararg: rt.IsVariadic()}, rt.NumIn()
		f.MinArgNum = rtNumIn
		if f.Vararg {
			f.MinArgNum--
		}
		if rtNumIn > 0 && rt.In(0) == stateType {
			f.MinArgNum--
		}
		f.F = func(s *State) {
			ins := make([]reflect.Value, 0, rtNumIn)
			for i := 0; i < rtNumIn+ifint(f.Vararg, -1, 0); i++ {
				if t := rt.In(i); i == 0 && t == stateType {
					ins = append(ins, reflect.ValueOf(s))
				} else {
					ins = append(ins, s.In().ReflectValue(t))
				}
			}
			s.Args.Foreach(func(v Value) bool { ins = append(ins, s.In().ReflectValue(rt.In(rtNumIn-1).Elem())); return true })
			if outs := rv.Call(ins); rt.NumOut() == 1 {
				s.Out = Val(outs[0].Interface())
			} else if rt.NumOut() > 1 {
				r := InitListBuilder()
				for _, o := range outs {
					r = r.Append(Val(o.Interface()))
				}
				s.Out.nop(r.Len != 0 && s.Out.Set(r.Build()) || s.Out.Set(Void))
			}
		}
		return Func(f)
	}
	return Value{val: uint64(InterfaceType), ptr: unsafe.Pointer(&v)}
}

func ValRec(v interface{}) Value {
	rv := reflect.ValueOf(v)
	switch rv.Kind() {
	case reflect.Slice, reflect.Array:
		l := InitListBuilder()
		for i := 0; i < rv.Len(); i++ {
			l = l.Append(ValRec(rv.Index(i).Interface()))
		}
		return l.Build()
	}
	return Val(v)
}

func ProperList(l ...Value) Value {
	return List(Empty, l...)
}

func List(suffix *Pair, l ...Value) Value {
	for i := len(l) - 1; i >= 0; i-- {
		n := &Pair{val: l[i], next: suffix}
		suffix = n
	}
	return Value{val: uint64(ListType), ptr: unsafe.Pointer(suffix)}
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

func Str(v string) (vs Value) {
	return Value{val: uint64(StrType), ptr: unsafe.Pointer(&v)}
}

func Func(f *Function) Value {
	return Value{val: uint64(FuncType), ptr: unsafe.Pointer(f)}
}

func (v Value) Quote() (q Value) {
	t := v.Type()
	return q.nop((t == ListType || t == SymType) && q.Set(List(Empty, Quote, v)) || q.Set(v))
}

func (v Value) Type() Type {
	switch v.ptr {
	case boolMarker:
		return BoolType
	case int64Marker, float64Marker:
		return NumType
	}
	switch v.val {
	case uint64(ListType), uint64(FuncType), uint64(StrType), uint64(InterfaceType):
		return Type(v.val)
	}
	if v.val >= 1<<51 {
		return SymType
	}
	if v == Void {
		return VoidType
	}
	panic("corrupted value")
}

func (v Value) stringify(goStyle bool) string {
	switch v.Type() {
	case NumType:
		vf, vi, vIsInt := v.Num()
		if vIsInt {
			return strconv.FormatInt(vi, 10)
		}
		return strconv.FormatFloat(vf, 'f', -1, 64)
	case StrType:
		return strconv.Quote(v.Str())
	case SymType:
		return v.Str() + ifstr(v.SymLineInfo() > 0, fmt.Sprintf(ifstr(goStyle, " /*L%d*/", " #|L%d|#"), v.SymLineInfo()), "")
	case ListType:
		p := bytes.NewBufferString("( ")
		for vl := v.List(); vl != nil && !vl.empty; vl = vl.next {
			p.WriteString(ifstr(vl.next == nil, ". ", ""))
			p.WriteString(vl.val.stringify(goStyle))
			p.WriteString(" ")
		}
		p.WriteString(")")
		return p.String()
	case BoolType:
		return ifstr(v.Bool(), ifstr(goStyle, "true", "#t"), ifstr(goStyle, "false", "#f"))
	case InterfaceType:
		return "#" + fmt.Sprintf("%#v", v.Interface())
	case FuncType:
		return v.Func().String()
	default:
		return ifstr(goStyle, "nil", "#v")
	}
}

func (v Value) Interface() interface{} {
	switch v.Type() {
	case NumType:
		vf, vi, vIsInt := v.Num()
		if vIsInt {
			return vi
		}
		return vf
	case StrType, SymType:
		return v.Str()
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
	if v.Type() == NumType {
		return rv.Convert(t)
	}
	return rv
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

func (v Value) Float() float64 {
	if v.ptr == float64Marker {
		return math.Float64frombits(v.val)
	}
	return float64(v.val)
}

func (v Value) Func() *Function {
	return (*Function)(v.ptr)
} // unsafe

func (v Value) Bool() bool {
	return v.val == 1
} // unsafe

func (v Value) Str() string {
	return *(*string)(v.ptr)
} // unsafe

func (v Value) List() *Pair {
	return (*Pair)(v.ptr)
} // unsafe

func (v Value) SetStr(text string) Value {
	return Sym(text, uint32(v.Type()/SymType)*v.SymLineInfo())
} // unsafe

func (v Value) SymLineInfo() uint32 {
	return uint32(v.val)
} // unsafe

func (v Value) Falsy() bool {
	return v == Void || v.val == 0
} // unsafe

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

func (v Value) FindFirstSym(depth int) (string, uint32) {
	if t := v.Type(); t == SymType {
		return strings.Repeat("(", depth) + v.Str() + strings.Repeat(" ...)", depth), v.SymLineInfo()
	} else if t == ListType {
		return v.List().val.FindFirstSym(depth + 1)
	}
	return "", 0
}

func (v Value) expect(s *State, t Type) Value {
	s.assert(v.Type() == t || s.panic("invalid argument #%d, expect %s, got %v", s.argIdx, Types[t], v))
	return v
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

func (v Value) Div(v2 Value, idiv bool) Value {
	vf, vi, vIsInt := v.Num()
	v2f, v2i, v2IsInt := v2.Num()
	if vIsInt && v2IsInt {
		if r := vi / v2i; r*v2i == vi || idiv {
			return Int(r)
		}
	}
	return Num(vf / v2f)
}

func (v Value) LessEqual(v2 Value) bool {
	vf, vi, vIsInt := v.Num()
	v2f, v2i, v2IsInt := v2.Num()
	if vIsInt && v2IsInt {
		return vi <= v2i
	}
	return vf <= v2f
}

func (v Value) Less(v2 Value) bool {
	vf, vi, vIsInt := v.Num()
	v2f, v2i, v2IsInt := v2.Num()
	if vIsInt && v2IsInt {
		return vi < v2i
	}
	return vf < v2f
}

func (v Value) Equals(v2 Value) bool {
	if v == v2 {
		return true
	} else if vflag, v2flag := v.Type(), v2.Type(); vflag == v2flag {
		switch vflag {
		case SymType, StrType:
			return v.Str() == v2.Str()
		case InterfaceType:
			return v.Interface() == v2.Interface()
		}
	}
	return false
}

func (v Value) Marshal() (buf []byte, err error) {
	defer func() {
		if r := recover(); r != nil {
			err, _ = r.(error)
			if err == nil {
				err = fmt.Errorf("marshal panic: %v", r)
			}
		}
	}()
	p := &bytes.Buffer{}
	if v.Type() == ListType {
		if vl := v.List(); !vl.empty && vl.next == Empty && vl.val.Type() == FuncType && vl.val.Func().natToplevel {
			// ( (toplevel-lambda) )
			f := vl.val.Func()
			p.WriteByte('T')
			p.WriteByte('s') // write a STR value
			writeString(p, f.Source)
			v = f.nat
		}
	}
	v.marshal(p)
	return p.Bytes(), nil
}

func (v *Value) Unmarshal(ctx *Context, buf []byte) (err error) {
	defer func() {
		if r := recover(); r != nil {
			err, _ = r.(error)
			if err == nil {
				err = fmt.Errorf("unmarshal panic: %v", r)
			}
		}
	}()
	v.unmarshal(ctx, bytes.NewReader(buf))
	return
}

func writeString(p *bytes.Buffer, s string) {
	var tmp [10]byte
	n := binary.PutVarint(tmp[:], int64(len(s)))
	p.Write(tmp[:n])
	p.WriteString(s)
}

func (v Value) marshal(p *bytes.Buffer) {
	switch v.Type() {
	case NumType:
		vf, vi, vIsInt := v.Num()
		if vIsInt {
			p.WriteByte('N')
			var tmp [10]byte
			n := binary.PutVarint(tmp[:], vi)
			p.Write(tmp[:n])
		} else {
			p.WriteByte('n')
			binary.Write(p, binary.BigEndian, vf)
		}
	case SymType:
		p.WriteByte('y')
		var tmp [10]byte
		n := binary.PutVarint(tmp[:], int64(v.SymLineInfo()))
		p.Write(tmp[:n])
		fallthrough
	case StrType:
		p.WriteByte('s')
		writeString(p, v.Str())
	case ListType:
		p.WriteByte('l')
		vl := v.List()
		for vl != nil && !vl.empty {
			if vl.next == nil {
				p.WriteByte(0)
			} else {
				p.WriteByte(1)
			}
			vl.val.marshal(p)
			vl = vl.next
		}
		p.WriteByte('L')
	case BoolType:
		if v.Bool() {
			p.WriteByte('B')
		} else {
			p.WriteByte('b')
		}
	case FuncType:
		panic(fmt.Errorf("function cannot be marshalled"))
	case InterfaceType:
		i := v.Interface()
		t := reflect.TypeOf(i)
		if goTypesRegRev[t] == 0 {
			panic(fmt.Errorf("marshal: %v is not registered", t))
		}
		p.WriteByte('i')
		binary.Write(p, binary.BigEndian, goTypesRegRev[t])
		gob.NewEncoder(p).Encode(i)
	default:
		p.WriteByte('v')
	}
}

func (v *Value) unmarshal(ctx *Context, p interface {
	io.ByteReader
	io.Reader
}) {
	var tag byte
	panicerr(binary.Read(p, binary.BigEndian, &tag))
	switch tag {
	case 'T':
		var src, body Value
		src.unmarshal(ctx, p)
		panicif(src.Type() != StrType, "invalid toplevel binary data")
		body.unmarshal(ctx, p)
		*v = List(Empty, Func(&Function{nat: body, natCls: ctx, natToplevel: true, Source: src.Str()}))
	case 'n':
		var v2 float64
		panicerr(binary.Read(p, binary.BigEndian, &v2))
		*v = Num(v2)
	case 'N':
		v2, err := binary.ReadVarint(p)
		panicerr(err)
		*v = Int(v2)
	case 'y':
		line, err := binary.ReadVarint(p)
		panicerr(err)
		var v2 Value
		v2.unmarshal(ctx, p)
		panicif(v2.Type() != StrType, "invalid symbol binary data")
		*v = Sym(v2.Str(), uint32(line))
	case 's':
		ln, err := binary.ReadVarint(p)
		panicerr(err)
		var buf = make([]byte, ln)
		_, err = p.Read(buf)
		panicerr(err)
		*v = Str(*(*string)(unsafe.Pointer(&buf)))
	case 'l':
		vl := InitListBuilder()
	LOOP:
		for {
			var tag byte
			var v2 Value
			panicerr(binary.Read(p, binary.BigEndian, &tag))
			switch tag {
			case 1:
				v2.unmarshal(ctx, p)
				vl = vl.Append(v2)
			case 0:
				v2.unmarshal(ctx, p)
				vl.Cur.val, vl.Cur.empty = v2, false
			case 'L':
				break LOOP
			}
		}
		*v = vl.Build()
	case 'b', 'B':
		*v = Bool(tag == 'B')
	case 'f':
		panic(fmt.Errorf("unmarshaler: impossible case"))
	case 'i':
		var typetag uint32
		panicerr(binary.Read(p, binary.BigEndian, &typetag))
		rt := goTypesReg[typetag]
		if rt == nil {
			panic(fmt.Errorf("unmarshaler: missing data type to recover interface{}"))
		}

		if rt.Kind() == reflect.Ptr {
			rv := reflect.New(rt.Elem())
			panicerr(gob.NewDecoder(p).Decode(rv.Interface()))
			*v = Val(rv.Interface())
		} else {
			rv := reflect.New(rt)
			panicerr(gob.NewDecoder(p).Decode(rv.Interface()))
			*v = Val(rv.Elem().Interface())
		}
	default:
		*v = Void
	}
	// fmt.Println("====", *v)
}
