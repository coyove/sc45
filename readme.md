Scmbed is a relatively-small-basically-working scheme dialect in Go, its core consists of only one file (scmbed.go) with no external dependencies.

Scmbed serves one purpose: change running programs' states from outside without too much coding efforts, particularly in server-side debugging environment.

Let's say you want to debug a piece of online server code: turn on a flag, do some setups and collect logs, then turn on another flag and repeat the process until safisifed.
This is usually not a tough task, but will introduce too much unnecessary efforts into your debugging process because you have to interact with a running program with complex logics.

You can simplify the problem by pre-defining functions and calling them in scmbed' REPL:
```Go
// During server initalization:
func init() {
    it := scmbed.New()
    it.InstallGo("(turn-on-flag1 ...)", func(v bool) { FLAG1 = v })
    it.InstallGo("(turn-on-flag2 ...)", func(v bool) { FLAG2 = v })
    it.InstallGo("(pre-setup ...)", func(n int, kafkaTopic string) { RerouteMsg(n, kafkaTopic) })
    ...

    // 1. If your server has debug/pprof enabled:
    repl.InjectDebugREPLIntopprof(it, "Title")
    // Navigate to http://.../debug/pprof/repl to use the REPL

    // 2. If you can access to the working directory where your server is running in:
    repl.RunSimplePipeREPL(it, "/tmp/debug_pipe")
    // This will output a 'repl' script in current working dir, you can: cd $CWD && ./repl to use the REPL
    // Note that this script needs mkfifo and access to '/tmp/debug_pipe'

    ...
}
```

Inside REPL:
```Scheme
(turn-on-flag1 #t)
(pre-setup 10 "debug-topic")
...
(turn-on-flag1 #f)
(turn-on-flag2 true)
```

# Language details
- `call/cc` is not supported (due to scmbed's recursive evaluation intepreter, this is also impossible)
- No difference between proper and improper list, because improper list has NO practical applications in scmbed and `(a . b)` is NOT supported
- Numbers are all float64, no numerical tower. For `uint64` and `int64`, use `(i64 ...)` to create them
- Lists are trees in scmbed, thus many operations can be implemented efficiently, e.g.: `(last list)`, in the meantime some operations are not, e.g.: `(set-cdr! list)`
- Macro definition syntax: `(lambda# (paramlist) body)`, it is a legit function which takes expressions as inputs and outputs expressions, so it is more like Lisp macro
