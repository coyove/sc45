Scmbed is a relatively-small-basically-working scheme dialect in Go.

Its core consists of only one file (scmbed.go) with no external dependencies, so instead of importing it into your project,
which may be tricky under many circumstances (e.g. open source lib review in many companies), you can copy the file directly into your code directory,
run it, get results, and delete it if no longer needed.

Scmbed serves one purpose: change running programs' states from outside without too much coding efforts, particularly in server-side debugging environment.

Let's say you want to debug a piece of online server code: turn on a flag, do some setups and collect logs, then turn on another flag and repeat the process until safisifed.
You can't test this using your local dev setup simply because the code relies on too many inputs that only available online.
So this task was noramlly done by writing debug profiles and load them accordingly using some sort of config center like etcd.

In scmbed, you can just write:
```
func init() {
    it := scmbed.New()
    it.InstallGo("(turn-on-flag1 ...)", func(v bool) { FLAG1 = v })
    it.InstallGo("(turn-on-flag2 ...)", func(v bool) { FLAG2 = v })
    it.InstallGo("(pre-setup ...)", func(n int, kafkaTopic string) { RerouteMsg(n, kafkaTopic) })
    ...
```
during server initalization, then call them:
```
(turn-on-flag1 #t)
(pre-setup 10 "debug-topic")
...
(turn-on-flag1 #f)
(turn-on-flag2 true)
```
But from where? There are 2 options available, depends on what you want:
```
// 1. If your server has debug/pprof enabled:
func init() {
    it := scmbed.New()
    ...
    it.InjectDebugREPLIntopprof("Title")

    // Navigate to http://.../debug/pprof/repl to use the REPL
}

// 2. If you can access to the working directory where your server is running in:
func init() {
    it := scmbed.New()
    ...
    it.RunSimplePipeREPL()

    // This will output a 'repl' script in current working dir, you can: cd $CWD && ./repl to use the REPL
    // Note that this script needs mkfifo, so Windows is not supported
}
```

# Language details
- `call/cc` is not supported (due to scmbed's recursive evaluation intepreter, this is also impossible)
- No difference between proper and improper list, because improper list has NO practical applications in scmbed and `(a . b)` is NOT supported
- Numbers are all float64, no numerical tower. For `uint64` and `int64`, use `(i64 ...)` to create them
- Lists are trees in scmbed, thus many operations can be implemented efficiently, e.g.: `(last list)`, in the meantime some operations are not, e.g.: `(set-cdr! list)`
- Macro definition syntax: `(lambda# (paramlist) body)`, it is a legit function which takes expressions as inputs and outputs expressions, so it is more like Lisp macro
