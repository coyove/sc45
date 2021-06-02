package value

import (
	"reflect"
	"unsafe"
)

var (
	Void  = Value{}
	Quote = Sym("quote", 0)
	Empty = &Pair{empty: true}
)

var (
	int64Marker   = unsafe.Pointer(new(int64))
	boolMarker    = unsafe.Pointer(new(bool))
	float64Marker = unsafe.Pointer(new(float64))
	stateType     = reflect.TypeOf(&State{})
	errorType     = reflect.TypeOf((*error)(nil)).Elem()
	valueType     = reflect.TypeOf(Value{})
)

type Type byte

var Types = map[Type]string{
	TextType:      "text",
	SymbolType:    "symbol",
	NumberType:    "number",
	ListType:      "list",
	InterfaceType: "interface",
	FuncType:      "function",
	BoolType:      "boolean",
	VoidType:      "void",
}

const (
	TextType      = 's'
	SymbolType    = 'y'
	NumberType    = 'n'
	BoolType      = 'b'
	ListType      = 'l'
	InterfaceType = 'i'
	FuncType      = 'f'
	VoidType      = 'v'
)
