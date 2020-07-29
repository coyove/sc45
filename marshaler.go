package scmbed

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"io"
	"unsafe"
)

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
	v.marshal(p)
	return p.Bytes(), nil
}

func (v *Value) Unmarshal(buf []byte) (err error) {
	defer func() {
		if r := recover(); r != nil {
			err, _ = r.(error)
			if err == nil {
				err = fmt.Errorf("unmarshal panic: %v", r)
			}
		}
	}()
	v.unmarshal(bytes.NewReader(buf))
	return
}

func (v Value) marshal(p *bytes.Buffer) {
	switch v.Type() {
	case 'n':
		if v := v.Num(); float64(int64(v)) == v {
			p.WriteByte('N')
			var tmp [10]byte
			n := binary.PutVarint(tmp[:], int64(v))
			p.Write(tmp[:n])
		} else {
			p.WriteByte('n')
			binary.Write(p, binary.BigEndian, v)
		}
	case 'y':
		p.WriteByte('y')
		line, col := v.Pos()
		var tmp [10]byte
		n := binary.PutUvarint(tmp[:], uint64(line)<<32|uint64(col))
		p.Write(tmp[:n])
		fallthrough
	case 's':
		p.WriteByte('s')
		s := v.Str()
		var tmp [10]byte
		n := binary.PutVarint(tmp[:], int64(len(s)))
		p.Write(tmp[:n])
		p.WriteString(s)
	case 'l':
		p.WriteByte('l')
		vl := v.Lst()
		for vl != nil && !vl._empty {
			if vl.Next == nil {
				p.WriteByte(0)
			} else {
				p.WriteByte(1)
			}
			vl.Val.marshal(p)
			vl = vl.Next
		}
		p.WriteByte('L')
	case 'b':
		p.WriteByte(ifbyte(v.Bln(), 'B', 'b'))
	case 'f', 'i':
		panic(fmt.Errorf("function and interface{} cannot be marshalled"))
	default:
		p.WriteByte('v')
	}
}

func (v *Value) unmarshal(p interface {
	io.ByteReader
	io.Reader
}) {
	var tag byte
	panicerr(binary.Read(p, binary.BigEndian, &tag))
	switch tag {
	case 'n':
		var v2 float64
		panicerr(binary.Read(p, binary.BigEndian, &v2))
		*v = Num(v2)
	case 'N':
		v2, err := binary.ReadVarint(p)
		panicerr(err)
		*v = Num(float64(v2))
	case 'y':
		tmp64, err := binary.ReadUvarint(p)
		panicerr(err)
		line, col := uint32(tmp64>>32), uint32(tmp64)
		var v2 Value
		v2.unmarshal(p)
		if v2.Type() != 's' {
			panic(fmt.Errorf("invalid symbol binary data"))
		}
		*v = Sym(v2.Str(), int(line), int(col))
	case 's':
		ln, err := binary.ReadVarint(p)
		panicerr(err)
		var buf = make([]byte, ln)
		_, err = p.Read(buf)
		panicerr(err)
		*v = Str(*(*string)(unsafe.Pointer(&buf)))
	case 'l':
		vl := initlistbuilder()
	LOOP:
		for {
			var tag byte
			var v2 Value
			panicerr(binary.Read(p, binary.BigEndian, &tag))
			switch tag {
			case 1:
				v2.unmarshal(p)
				vl = vl.append(v2)
			case 0:
				v2.unmarshal(p)
				vl.p.Val, vl.p._empty = v2, false
				break LOOP
			case 'L':
				break LOOP
			}
		}
		*v = vl.value()
	case 'b', 'B':
		*v = Bln(tag == 'B')
	case 'f', 'i':
		panic(fmt.Errorf("unmarshaler impossible case"))
	default:
		*v = Void
	}
	// fmt.Println("====", *v)
}
