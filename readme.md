Scmbed is a relatively-small-basically-working scheme dialect in Go, its core consists of only one file (scmbed.go) with no external dependencies.

Scmbed serves one purpose: give your program an embedded REPL on-the-fly. 

Let's say you want to debug a piece of online server code: turn on a flag, do some setups and collect logs, then turn on another flag and repeat the process until safisifed.
This is usually not a tough task, but will introduce too much unnecessary efforts into your debugging process because you have to interact with a running program with complex logics.

Having REPL will make things a lot easier:
```Go
// During program initalization:
func init() {
    it := scmbed.New()
    it.InstallGo("(turn-on-flag1 ...)", func(v bool) { FLAG1 = v })
    it.InstallGo("(turn-on-flag2 ...)", func(v bool) { FLAG2 = v })
    it.InstallGo("(pre-setup ...)", func(n int, kafkaTopic string) { RerouteMsg(n, kafkaTopic) })
    ...

    // 1. If your server has debug/pprof enabled:
    repl.InjectDebugPProfREPL(it, "Title")
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
- Numbers are float64 internally, but their raw string representations are stored as well, which means you can cast a `Value` to either a `float64` or a `string`
- Macro definition syntax: `(define-macro name (lambda (paramlist) body))`, macro is a legit function which takes expressions as inputs and outputs expressions, so it is more like Lisp macro
