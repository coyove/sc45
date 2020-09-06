Sc45 is a relatively-small-basically-working scheme dialect in Go, its core consists of only one file (sc45.go) with 1k LOC.

Sc45 serves one purpose: give your program an embedded REPL on-the-fly with minimal efforts:

```Go
func init() {
    it := sc45.New()
    it.Store("turn-on-flag1", sc45.V(func(v bool) { FLAG1 = v }))
    it.Store("turn-on-flag2", sc45.V(func(v bool) { FLAG2 = v }))
    it.Store("pre-setup", sc45.V(func(n int, kafkaTopic string) { RerouteMsg(n, kafkaTopic) }))
    ...

    // 1. If your server has debug/pprof enabled:
    it.InjectDebugPProfREPL("Title")
    // Navigate to http://.../debug/pprof/repl to use the REPL

    // 2. If you can access to the working directory where your server is running in:
    it.RunSimplePipeREPL("/tmp/debug_pipe")
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
- `call/cc` is not supported, due to sc45's recursive evaluation intepreter, this is also impossible
- Numbers are float64 + int64 internally, int64 will be promoted to float64 when needed
- Macro definition syntax: `(define name (lambda-syntax (paramlist) body))`, macro is a legit function which takes expressions as inputs and outputs expressions, and it can also refer upper level symbols
