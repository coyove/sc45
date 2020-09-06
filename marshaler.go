package sc45

import (
	"bytes"
	"crypto/sha1"
	"encoding/binary"
	"encoding/gob"
	"fmt"
	"io"
	"reflect"
	"unsafe"
)

var (
	goTypesReg    = map[uint32]reflect.Type{}
	goTypesRegRev = map[reflect.Type]uint32{}
)

func RegisterGoType(dummy interface{}) {
	t := reflect.TypeOf(dummy)
	x := sha1.Sum([]byte(t.String()))
	h := binary.BigEndian.Uint32(x[:4])
	goTypesReg[h] = t
	goTypesRegRev[t] = h
}

func panicerr(err error) {
	if err != nil {
		panic(err)
	}
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
	if v.Type() == LIST {
		if vl := v.L(); !vl.empty && vl.next == Empty && vl.val.Type() == FUNC && vl.val.F().natToplevel {
			// ( (toplevel-lambda) )
			f := vl.val.F()
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
	case NUM:
		vf, vi, vIsInt := v.N()
		if vIsInt {
			p.WriteByte('N')
			var tmp [10]byte
			n := binary.PutVarint(tmp[:], vi)
			p.Write(tmp[:n])
		} else {
			p.WriteByte('n')
			binary.Write(p, binary.BigEndian, vf)
		}
	case SYM:
		p.WriteByte('y')
		var tmp [10]byte
		n := binary.PutVarint(tmp[:], int64(v.LineInfo()))
		p.Write(tmp[:n])
		fallthrough
	case STR:
		p.WriteByte('s')
		writeString(p, v.S())
	case LIST:
		p.WriteByte('l')
		vl := v.L()
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
	case BOOL:
		if v.B() {
			p.WriteByte('B')
		} else {
			p.WriteByte('b')
		}
	case FUNC:
		panic(fmt.Errorf("function cannot be marshalled"))
	case INTF:
		i := v.V()
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
		panicif(src.Type() != STR, "invalid toplevel binary data")
		body.unmarshal(ctx, p)
		*v = L(Empty, F(&Func{nat: body, natCls: ctx, natToplevel: true, Source: src.S()}))
	case 'n':
		var v2 float64
		panicerr(binary.Read(p, binary.BigEndian, &v2))
		*v = N(v2)
	case 'N':
		v2, err := binary.ReadVarint(p)
		panicerr(err)
		*v = I(v2)
	case 'y':
		line, err := binary.ReadVarint(p)
		panicerr(err)
		var v2 Value
		v2.unmarshal(ctx, p)
		panicif(v2.Type() != STR, "invalid symbol binary data")
		*v = Y(v2.S(), uint32(line))
	case 's':
		ln, err := binary.ReadVarint(p)
		panicerr(err)
		var buf = make([]byte, ln)
		_, err = p.Read(buf)
		panicerr(err)
		*v = S(*(*string)(unsafe.Pointer(&buf)))
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
		*v = B(tag == 'B')
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
			*v = V(rv.Interface())
		} else {
			rv := reflect.New(rt)
			panicerr(gob.NewDecoder(p).Decode(rv.Interface()))
			*v = V(rv.Elem().Interface())
		}
	default:
		*v = Void
	}
	// fmt.Println("====", *v)
}
