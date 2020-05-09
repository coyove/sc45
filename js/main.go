package main

import (
	"syscall/js"

	"github.com/coyove/scmbed"
)

func main() {
	it := scmbed.New()
	js.Global().Set("run", js.FuncOf(func(this js.Value, args []js.Value) interface{} {
		return it
	}))
}
