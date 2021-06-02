package value

import (
	"strconv"
)

func IfStr(v bool, t, f string) string {
	if v {
		return t
	}
	return f
}

func IfInt(v bool, t, f int) int {
	if v {
		return t
	}
	return f
}

func PanicIf(v bool, t string) {
	if v {
		panic(t)
	}
}

func ParseNumber(text string) (vn Value) {
	if v, err := strconv.ParseInt(text, 0, 64); err == nil {
		return Int(v)
	}
	v, err := strconv.ParseFloat(text, 64)
	return vn.nop(err == nil && vn.Set(Num(v)) || vn.Set(Void))
}

func Cons(v, v2 Value) *Pair {
	return (&Pair{Val: v}).SetCdr(v2)
}
