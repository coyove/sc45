package main

import (
	"syscall/js"

	"github.com/coyove/sc45"
)

func main() {
	it := sc45.New()
	js.Global().Set("run", js.FuncOf(func(this js.Value, args []js.Value) interface{} {
		return it
	}))
}
