package sc45

import (
	"fmt"
	"log"
	"net/http"
	"os"
	"strconv"
	"strings"
	"testing"
)

type dummy struct {
	V struct {
		V2 bool
		V3 int
	}
}

func (d *dummy) M(v string, args ...string) string {
	if len(args) == 0 {
		return v + strconv.FormatBool(d.V.V2)
	}
	return v + args[0]
}

func TestMarshal(t *testing.T) {
	RegisterGoType(&dummy{})
	RegisterGoType(dummy{})

	it := New()
	it.Store("pd", NewFunc(Macro, func(s *State) {
		d := &dummy{}
		d.V.V3 = 10
		s.Out = V(d)
	}))
	it.Store("d", NewFunc(Macro, func(s *State) {
		d := dummy{}
		d.V.V3 = 10
		s.Out = V(d)
	}))

	v, _ := it.Parse("", "(pd)")
	buf, err := v.Marshal()
	panicerr(err)
	panicerr(v.Unmarshal(buf))
	if d := v.V().([]interface{})[3].(*dummy); d.V.V3 != 10 {
		t.Fatal(d)
	}
	v, _ = it.Parse("", "(d)")
	buf, err = v.Marshal()
	panicerr(err)
	panicerr(v.Unmarshal(buf))
	if d := v.V().([]interface{})[3].(dummy); d.V.V3 != 10 {
		t.Fatal(d)
	}
	v, _ = it.Parse("", "(i64 10)")
	buf, err = v.Marshal()
	panicerr(err)
	panicerr(v.Unmarshal(buf))
	if d := v.V().([]interface{})[3].(int64); d != 10 {
		t.Fatal(d)
	}
}

func TestOne(t *testing.T) {
	it := New()
	assert := func(v string) {
		r, err := it.RunFile(v)
		if err != nil && strings.HasPrefix(v, "(") {
			r, err = it.Run(v)
		}
		if err != nil {
			t.Fatal(v, err)
		}
		log.Println(v, "===>", r)
	}
	it.Store("assert", NewFunc(1, func(s *State) {
		if s.In().IsFalse() {
			panic(fmt.Errorf("assertion failed"))
		}
	}))
	it.Store("current-location", NewFunc(0, func(s *State) {
		s.Out = S(*s.Debug.L)
	}))
	it.Store("test/struct-gen", NewFunc(1, func(s *State) {
		if s.In().IsFalse() {
			s.Out = V((*dummy)(nil))
			return
		}
		d := &dummy{}
		d.V.V2 = true
		s.Out = V(d)
		return
	}))
	it.Store("make/vararg", Fgo(func(v ...interface{}) []interface{} { return v }))
	it.Store("make/vararg2", Fgo(func(s *State, a1 int32, v2 ...string) []interface{} {
		a := []interface{}{a1}
		for _, v := range v2 {
			a = append(a, v)
		}
		return a
	}))
	it.Store("make/bytes", NewFunc(1, func(s *State) {
		n := s.In().V()
		l := make([]byte, n.(int64))
		for i := 0; i < len(l); i++ {
			l[i] = byte(i) + 1
		}
		s.Out = V(l)
	}))
	it.Store("make/list", NewFunc(1, func(s *State) {
		l := make([]Value, int(s.InType('n').N()))
		for i := 0; i < len(l); i++ {
			l[i] = N(float64(i) + 1)
		}
		s.Out = L(Empty, l...)
	}))
	it.Store("range", NewFunc(2, func(s *State) {
		m := s.InMap()
		f := s.InType('f')
		for k, v := range m {
			err, _ := f.F().Call(S(k), v)
			if err.IsFalse() {
				s.Out = v
				return
			}
		}
	}))
	it.Store("iff", NewFunc(2|Macro, func(s *State) {
		s.In()
		s.Out = s.In()
	}))

	assert("s/basic.scm")
	assert("s/match.scm")
	assert("s/let.scm")
	assert("s/list.scm")
	assert("s/fib.scm")
	assert("s/misc.scm")

	assert(`(define foo (eval (parse "s/module.scm")))
	(eval '(foo (lambda () (display (current-location)) (assert (substring? (current-location) "memory")) )))`)

	{
		_, err := it.Run(`(define foo (eval (parse "s/module.scm"))) (eval '(foo 99))`)
		if !strings.Contains(err.Error(), "(s/module.scm)") {
			t.Fatal(err)
		}
	}

	// 	assert(`(assert (= "true" (cond
	// 			((= 1 2)     (assert false))
	// 			((> "a" "b") (assert false))
	// 			(true        "true"`)
	// 	assert(`(cond
	// 			((= 1 2)  (assert false))
	// 			(else     (assert true))
	// 			(true     (assert false)`)

}

func BenchmarkRun(b *testing.B) {
	text := strings.Repeat("'(1 2 3)", 10)
	for i := 0; i < b.N; i++ {
		it := New()
		it.Run(text)
	}
}

func TestLaunchWeb(t *testing.T) {
	if os.Getenv("WEB") != "" {
		it := New()
		it.InjectDebugPProfREPL("debug")
		http.ListenAndServe(":8080", nil)
	}
}
