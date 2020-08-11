package sc45

import (
	"fmt"
	"log"
	"strconv"
	"strings"
	"testing"
)

type dummy struct {
	V struct {
		V2 bool
	}
}

func (d *dummy) M(v string, args ...string) string {
	if len(args) == 0 {
		return v + strconv.FormatBool(d.V.V2)
	}
	return v + args[0]
}

func TestOne(t *testing.T) {
	it := New()
	assert := func(v string) {
		r, err := it.RunFile(v)
		if err != nil {
			t.Fatal(v, err)
		}
		log.Println(v, "===>", r)
	}
	it.Store("assert", F(1, func(s *State) {
		if s.In().IsFalse() {
			panic(fmt.Errorf("assertion failed"))
		}
	}))
	it.Store("test/struct-gen", F(1, func(s *State) {
		if s.In().IsFalse() {
			s.Out = Val((*dummy)(nil))
			return
		}
		d := &dummy{}
		d.V.V2 = true
		s.Out = Val(d)
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
	it.Store("make/bytes", F(1, func(s *State) {
		n := s.In().Val()
		l := make([]byte, n.(int64))
		for i := 0; i < len(l); i++ {
			l[i] = byte(i) + 1
		}
		s.Out = Val(l)
	}))
	it.Store("make/list", F(1, func(s *State) {
		l := make([]Value, int(s.InType('n').Num()))
		for i := 0; i < len(l); i++ {
			l[i] = Num(float64(i) + 1)
		}
		s.Out = Lst(Empty, l...)
	}))
	it.Store("range", F(2, func(s *State) {
		m := s.InMap()
		f := s.InType('f')
		for k, v := range m {
			err, _ := f.Fun().Call(Str(k), v)
			if err.IsFalse() {
				s.Out = v
				return
			}
		}
	}))
	it.Store("iff", F(2|Macro, func(s *State) {
		s.In()
		s.Out = s.In()
	}))

	assert("s/basic.scm")
	assert("s/match.scm")
	assert("s/let.scm")
	assert("s/list.scm")
	assert("s/fib.scm")
	assert("s/misc.scm")

	{
		_, err := it.Run(`(define foo (eval (parse "s/module.scm")))
(eval '(foo (lambda () (raise 99))))`)
		if !strings.Contains(err.Error(), "((memory))") {
			t.Fatal(err)
		}
	}
	{
		_, err := it.Run(`(define foo (eval (parse "s/module.scm")))
(eval '(foo 99))`)
		if !strings.Contains(err.Error(), "(s/module.scm)") {
			t.Fatal(err)
		}
	}

	// 	assert(`(assert (= (car (var/test 1 2 3)) 3)`)
	// 	assert(`(assert (error? (var/test 100 2 3)`)
	// 	assert(`(assert (= "true" (cond
	// 			((= 1 2)     (assert false))
	// 			((> "a" "b") (assert false))
	// 			(true        "true"`)
	// 	assert(`(cond
	// 			((= 1 2)  (assert false))
	// 			(else     (assert true))
	// 			(true     (assert false)`)

}

// func BenchmarkRun(b *testing.B) {
// 	text := strings.Repeat("'(1 2 3)", 10)
// 	for i := 0; i < b.N; i++ {
// 		it := New()
// 		it.Run(text)
// 	}
// }
//
// func BenchmarkAdd(b *testing.B) {
// 	var a interface{} = strconv.FormatInt(time.Now().Unix(), 10)
// 	for i := 0; i < b.N; i++ {
// 		a = strconv.FormatInt(int64(i), 10)
// 	}
// 	_ = a
// }
//
// func BenchmarkAddValue(b *testing.B) {
// 	var a = Str(strconv.FormatInt(time.Now().Unix(), 10))
// 	for i := 0; i < b.N; i++ {
// 		a = Str(strconv.FormatInt(int64(i), 10))
// 	}
// 	_ = a
// }
