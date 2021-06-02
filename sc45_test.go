package sc45

import (
	"fmt"
	"log"
	"math"
	"math/rand"
	"net/http"
	"os"
	"strconv"
	"strings"
	"testing"
	"time"
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

func set(v *Value, v2 Value) bool { *v = v2; return true }

func TestMarshal(t *testing.T) {
	RegisterGoType(&dummy{})
	RegisterGoType(dummy{})

	it := New()
	it.Store("pd", NewFunc(Macro, func(s *State) {
		d := &dummy{}
		d.V.V3 = 10
		s.Out = Val(d)
	}))
	it.Store("d", NewFunc(Macro, func(s *State) {
		d := dummy{}
		d.V.V3 = 10
		s.Out = Val(d)
	}))

	v, _ := it.Run(Forever, "(pd)")
	buf, err := v.Marshal()
	panicerr(err)
	panicerr(v.Unmarshal(it, buf))
	if d := v.Interface().(*dummy); d.V.V3 != 10 {
		t.Fatal(d)
	}
	v, _ = it.Run(Forever, "(d)")
	buf, err = v.Marshal()
	panicerr(err)
	panicerr(v.Unmarshal(it, buf))
	if d := v.Interface().(dummy); d.V.V3 != 10 {
		t.Fatal(d)
	}

}

func TestNumber(t *testing.T) {
	check := func(n Value, v float64) {
		if vf, _, _ := n.Number(); n.Type() != NUM || vf != v {
			t.Fatal(n.GoString(), v)
		}
	}
	check(N(0), 0)
	check(N(math.Inf(1)), math.Inf(1))
	check(N(math.Inf(-1)), math.Inf(-1))
	check(N(math.MaxFloat64), math.MaxFloat64)
	check(N(-math.MaxFloat64), -math.MaxFloat64)

	rand.Seed(time.Now().Unix())
	for i := 0; i < 1e6; i++ {
		x := rand.Int63()
		v := I(x)
		if v.Type() != NUM || v.Int() != x {
			t.FailNow()
		}
	}

	for _, i := range []int64{1, -1} {
		x := int64(math.MaxInt64) * i
		v := I(x)
		if v.Type() != NUM || v.Int() != x {
			t.FailNow()
		}
	}

	var v uint64 = 0x8ffffffffffffff7
	if I(int64(v)).Equals(N(math.Float64frombits(^v))) {
		t.Fatal("check Value.Equals")
	}
}

func TestOne(t *testing.T) {
	it := New()
	assert := func(v string) {
		r, err := it.RunFile(time.Now().Add(30*time.Second), v)
		if err != nil && strings.HasPrefix(v, "(") {
			r, err = it.Run(Forever, v)
		}
		if err != nil {
			t.Fatal(v, err)
		}
		log.Println(v, "===>", r)
	}
	_ = assert
	it.Store("assert", Val(func(c Value) {
		if c.IsFalse() {
			panic(fmt.Errorf("assertion failed"))
		}
	}))
	it.Store("current-location", NewFunc(0, func(s *State) {
		locs := s.Stack.StackLocations(false)
		fmt.Println(locs)
		s.Out = S(locs[len(locs)-1])
	}))
	it.Store("test/struct-gen", NewFunc(1, func(s *State) {
		if s.In().IsFalse() {
			s.Out = Val((*dummy)(nil))
			return
		}
		d := &dummy{}
		d.V.V2 = true
		s.Out = Val(d)
		return
	}))
	it.Store("make/vararg", Val(func(v ...interface{}) []interface{} { return v }))
	it.Store("make/vararg2", Val(func(s *State, a1 int32, v2 ...string) []interface{} {
		a := []interface{}{a1}
		for _, v := range v2 {
			a = append(a, v)
		}
		return a
	}))
	it.Store("make/bytes", NewFunc(1, func(s *State) {
		n := s.In().Interface()
		l := make([]byte, n.(int64))
		for i := 0; i < len(l); i++ {
			l[i] = byte(i) + 1
		}
		s.Out = Val(l)
	}))
	it.Store("make/list", NewFunc(1, func(s *State) {
		l := make([]Value, s.I())
		for i := 0; i < len(l); i++ {
			l[i] = N(float64(i) + 1)
		}
		s.Out = L(Empty, l...)
	}))
	it.Store("range", NewFunc(2, func(s *State) {
		m := s.InMap()
		f := s.F()
		for k, v := range m {
			err, _ := f.CallOnStack(s.Stack, Forever, L(Empty, S(k), v))
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

	// assert("s/fib.scm")
	assert("s/basic.scm")
	assert("s/match.scm")
	assert("s/let.scm")
	assert("s/list.scm")
	assert("s/misc.scm")

	// assert(`(define foo (eval (parse "s/module.scm")))
	// (eval '(foo (lambda () (display (current-location)) (assert (substring? (current-location) "memory")) )))`)

	{
		_, err := it.Run(Forever, `(define foo (eval (parse "s/module.scm"))) (eval '(foo 99))`)
		if !strings.Contains(err.Error(), "s/module.scm") {
			t.Fatal(err)
		}
	}

	{
		_, err := it.Run(Forever, `(define foo (eval (parse "s/module.scm"))) 
(define m# (lambda-syntax whatever (foo 10)))
(m#)
		`)
		t.Log(err)
		if !strings.Contains(err.Error(), "s/module.scm") {
			t.Fatal(err)
		}
	}
}

func BenchmarkRun(b *testing.B) {
	text := strings.Repeat("'(1 2 3)", 10)
	for i := 0; i < b.N; i++ {
		it := New()
		it.Run(Forever, text)
	}
}

func TestLaunchWeb(t *testing.T) {
	if os.Getenv("WEB") != "" {
		it := New()
		it.InjectDebugPProfREPL("debug")
		http.ListenAndServe("127.0.0.1:8080", nil)
	}
}
