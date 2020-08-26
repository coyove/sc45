package main

import (
	"flag"
	"fmt"
	"io/ioutil"
	"os"
	"syscall"
	"time"

	"github.com/coyove/sc45"
)

var inputFile = flag.String("f", "", "input file")
var inputExpr = flag.String("e", `"Hello world"`, "input expression")
var timeout = flag.Int64("t", 0, "timeout (second)")
var memLimit = flag.Int64("as", 0, "virtual memory limit")
var suppressStdout = flag.Bool("no-script-stdout", false, "suppress script stdout")

func main() {
	flag.Parse()

	if *memLimit > 0 {
		r := &syscall.Rlimit{}
		syscall.Getrlimit(syscall.RLIMIT_AS, r)
		r.Cur = uint64(*memLimit)
		if err := syscall.Setrlimit(syscall.RLIMIT_AS, r); err != nil {
			fmt.Fprintln(os.Stderr, "setrlimit error:", err)
		}
	}

	deadline := time.Now()
	if *timeout == 0 {
		deadline = sc45.Forever
	} else {
		deadline = deadline.Add(time.Duration(*timeout) * time.Second)
	}

	if *suppressStdout {
		sc45.DefaultStdout = ioutil.Discard
	}

	ctx := sc45.New()

	input := *inputFile
	runner := ctx.RunFile
	if input == "" {
		input = *inputExpr
		runner = ctx.Run
	}

	r, err := runner(deadline, input)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
	} else {
		fmt.Fprintln(os.Stdout, r)
	}
}
