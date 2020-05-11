package scmbed

import (
	"fmt"
	"log"
	"math/rand"
	"strconv"
	"strings"
	"testing"
	"time"
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
	it.Install("(assert)", func(s *State) {
		if !s.In(0, 0).IsTrue() {
			panic(fmt.Errorf("assertion failed"))
		}
	})
	it.Install("var/test", func(s *State) {
		v := s.In(0, 'n').Num()
		a := s.Args[1:]
		if v == 100 {
			s.Out = Val(fmt.Errorf(""))
		} else {
			av := a[0].Num()
			a[0] = Num(av + v)
			s.Out = Lst(append([]Value{}, a...)...)
		}
	})
	// it.Install("callee", "", func(v int64) int64 { return v * 10 })
	it.Install("(test/struct-gen)", func(s *State) {
		if !s.In(0, 0).IsTrue() {
			s.Out = Val((*dummy)(nil))
			return
		}
		d := &dummy{}
		d.V.V2 = true
		s.Out = Val(d)
		return
	})
	it.InstallGo("(make/vararg)", func(v ...interface{}) []interface{} {
		return v
	})
	it.Install("(make/bytes)", func(s *State) {
		n := s.In(0, 0).Val()
		l := make([]byte, n.(int64))
		for i := 0; i < len(l); i++ {
			l[i] = byte(i) + 1
		}
		s.Out = Val(l)
	})
	it.Install("(make/list)", func(s *State) {
		l := make([]Value, int(s.In(0, 'n').Num()))
		for i := 0; i < len(l); i++ {
			l[i] = Num(float64(i) + 1)
		}
		s.Out = Lst(l...)
	})
	it.Install("(range)", func(s *State) {
		m := s.InMap(0)
		f := s.In(1, 'f')
		for k, v := range m {
			err, ok := f.Fun().Call(Str(k), v)
			log.Println("===", err, ok)
			if !err.IsTrue() {
				s.Out = v
				return
			}
		}
	})
	assert := func(v string) {
		r, err := it.Run(v)
		if err != nil {
			t.Fatal(v, err)
		}
		log.Println(v, "===>", r)
	}
	it.Install("#(iff)", func(s *State) {
		s.Out = s.In(1, 0)
	})
	assert("(eval (unwrap-macro (list 'define `(madd2 a ,(atom \"b\")) (list 'let `[(c ,(cons '+ (cons 'a (cons 'b [] ))) )] '(* (let ((a a)) a) b c))")
	assert(`(define# (let*-native bindings)
		(define body (append '(if () ()) (rest-args)))
		(letrec ((work (lambda (lst)
			(if (not (null? lst)) (begin
				(set! body (list 'let (list (last lst)) body))
				(work (init lst))
			))))) (work bindings))
		body
	)`)
	assert(`(assert (= (madd2 10 20) 6000)))`)
	assert("(assert (= #/中 0x4e2d")
	assert(`(if #f (+ 1 #| inline || comment (assert false) #|#  2 3.5) (lambda (a b) ())`)
	assert(`(assert ( [lambda* (a b) (assert (= a 1)) (null? b)] 1) `)
	assert(`( [lambda* (a [b (+ a 1)] ) (assert (= a 1)) (assert (= b 2))] 1) `)
	assert(`( [lambda* (a b c...) (assert (= 1 (length c))) (assert (car c))] 1 2 #t) `)
	assert("(let* ((a 1) (b (+ a 1))) (assert (= b 2))")
	assert("(let*-native ((a 1) (b (+ a 1)) (c (+ b a))) (assert (= c 3))")
	assert(`
	 (define (list-eq? list1 list2)
	 	(if (and (list? list1) (list? list2))
			(if (and (null? list1) (null? list2))
				#t (if (or (null? list1) (null? list2))
					#f (if (not (list-eq? (car list1) (car list2)))
						#f (list-eq? (cdr list1) (cdr list2))
				)))
			(= list1 list2)))

	 (let () (define a '(1))
	 (define #b (add a 3))
	 (set-car! a 100)
	 (assert (list-eq? #b '(100 3))
	 (assert (list-eq? (go-value-wrap (make/vararg 1 2 "a")) '(1 2 "a")))
	 (assert (null? (go-value-wrap (make/vararg))))
	 (assert (list-eq? (make/list 1000) (make/list 1000)`)
	assert("(assert (list-eq? (quasiquote (1 2 3 ,(cons 4 `(5 ,(let ((a 2)) (* a 3) ))))) '(1 2 3 (4 5 6))))")
	assert("(assert (list-eq? `( 1 ',(+ 2 3)) '(1 '5)))")
	// assert("(assert (println (list 'defun 'a) '(defun a)")
	assert(`(let () (define list (make/bytes (i64 @10))) (vector-set-nth! list 0 10) (assert (== 10 (vector-nth list 0)`)
	assert(`(let () (define-record 'user 'name 'ok) (define a (user-new 'ok #f)) (user-ok-set! a #t) (assert (user-ok a)) `)
	assert(`(assert (== 20 (reduce + 0 (map (lambda (a) ($ a * 2)) '(1 2 3 4)`)
	assert(`(define makecps (lambda (f)
	 	 	(lambda	args #|
			multiline 
			comments
			|#
			[ (last args) (apply f (init args)) ])
	 	 ))
	 	(define +& (makecps +))  (apply +& (cons 1 (cons 2 (cons 3 (cons (lambda (r) (assert (= r 6))) ()`)
	// assert(`(define a 1) (assert (== a 1)) (define (aa if p2) (set! if (+ if 1)) (+ if p2)) (assert (== 10 (aa 5 4) `)
	assert(`(define Foreach (lambda (s cb) (letrec [(ForeachImpl (lambda (s cb idx) ; comment
	 		(if (null? s) () (begin
	 			(if (== false (cb (car s) idx )) ()
	 				(ForeachImpl (cdr s) cb (+ idx 1)))))))] (ForeachImpl s cb 0)) ;;`)

	assert(`(define Counter 0) (Foreach (make/list 1000000) (lambda (v) (begin (set! Counter (+ Counter 1)) (assert (== Counter v`)
	assert(`
	 	 // let's play closure
	 	 (define build-incr (lambda (start)
	 		(begin
	 			(let ((incr (lambda (v)
	 				(set! start (+ start v))
	 				start))) (assert true) incr)
	 		)
	 	 ))
	 	 (define incr (build-incr 10))
	 	 (define incr2 (build-incr 1))
	 	 (assert (== (incr 1) 11))
	 	 (assert (== (incr2 1) 2))
	 	 (assert (== (incr -1) 10))
	 	 (assert (= (incr2 0) 2))
	 	 	`)
	assert(`(define StringSplit
	 	(lambda (S Sep) (begin
	 		(define First-occur -1)
	 		(vector-foreach S (lambda (_2 _1)
	 			(begin
	 				(define end (+ _2 (vector-len Sep)))
	 				(if (and (<= end (vector-len S)) (== (vector-slice S _2 end) Sep))
	 					(begin (set! First-occur _2) false)))))
	 		(if (== -1 First-occur)
	 			(list S)
	 			(begin
	 				(define results (list (vector-slice S 0 First-occur) ))
	 				(set! results (vector-concat results (StringSplit (vector-slice S (+ First-occur (vector-len Sep))) Sep)))
	 				results
	 			)
	 		))
	 	))`)
	assert(`(assert (= 1 ( [lambda () 1])`)
	assert(`(assert (= 1 ( [lambda (a) a] 1)`)
	assert(`(assert (= 3 ( [lambda (a) (+ a (length (rest-args))) ] 1 2 3)`)
	assert(`(assert (= 0 ( [lambda (a) (length (rest-args))] 1)`)
	assert(`(= (json (StringSplit "aabbccbbd" "bb") 'c) "[\"aa\",\"cc\",\"d\"]"`)
	assert(`(let ((a (json-parse "{\"a\":{\"b\":1}}"))) (assert (= (map-get (map-get a "a") "b") 1 `)
	assert(`(assert (= 3 ((lambda (a b) (+ a b)) 1 2)`)
	assert(`
	 (define (nth-cdr list n)
	 	(if (= n 0)
	 		list
	 		(nth-cdr (cdr list) (- n 1))))
	
	 (define (set-nth! list n v)
	 	(set-car! (nth-cdr list n) v))
	
	 (define# (defun name paramlist body)
	 	(begin
	 		(define setter '(define))
	 		(set! setter (append setter (cons name () )))
	 		(define fun (append '(lambda) (list paramlist body) ))
	 		(set! setter (add setter fun ))
	 		setter
	 	`)
	assert(`(defun a (a) (* a (length (rest-args)))) (defun b(a) (* a (length (rest-args)))) (assert (= 10 (a 5 "a" ())))
	(assert (= 1 (b 1 1
	`)
	assert(`(eval (unwrap-macro (list 'defun 'madd '(a b) '(+ a b`)
	assert(`(assert (= (madd "a" "b") "ab"))`)
	assert(`(define #or (lambda# args
	 		(begin
	 			(define Build-Macro-Or (lambda (lhs)
	 			(begin
	 				(define if-stat (append '(if) (list 'cond 'true 'cond2)))
	 				(set-nth! if-stat 1 lhs)
	 				(set-nth! if-stat 3 (if (= (length (rest-args)) 1)
	 					(car (rest-args))
	 					(apply Build-Macro-Or (rest-args))
	 				))
	 				if-stat
	 			)))
	 			(apply Build-Macro-Or args)
	 		)
	 	)`)
	assert(`(#or (#or true (assert false)) (= 1 0) true (assert false))`)
	assert(`(iff (assert false) (+ 1 2) )`)
	assert(`(assert (or true (assert false`)
	assert(`(assert (not (and true (or) (assert false))`)
	assert("(stringify '(+ \"asd\" 2))")

	assert(`(assert (list-eq? '(2 3) ((lambda (a) (rest-args)) 1 2 3`)
	assert(`(define s (test/struct-gen true)) (struct-set! 'V 'V2 false s) (assert (not (struct-get 'V 'V2 s`)
	assert(`(set! s (test/struct-gen true)) (setf! s.V.V2 false) (assert (not (getf s.V.V2`)
	assert(`(assert (= ((if true + -) (- (* 2)) 1) (number "-1"))`)
	assert(`(assert (= (car (var/test 1 2 3) 0) 3)`)
	assert(`(assert (error? (var/test 100 2 3)`)
	assert(`(assert (= true (< 1 2`)
	assert(`(assert (if true true false`)
	assert(`(define ha (if (not #t) false #t)) (assert ha`)
	assert(`(assert ha`)
	assert(`(assert (= (+ .5 .5) 1.`)
	assert(`(assert (= (+ "a" "b" "c") "abc"`)
	assert(`(set! a 1) (assert (= ( + a 2) 3`)
	assert(`(assert (= "b" (range (map-new "a" "A" "b" "b" "c" "") (lambda (l r) (if (= l r) (error "ok") #t`)
	assert(`(define Fib (lambda (v) (if (< v 2) v (+ (Fib (- v 1)) (Fib (- v 2)))))) (assert (= (Fib 8) 21`)
	// 	assert(`(assert (eq (list 1 2 3) (cdr (list 0 1 2 3)`)
	assert(`(define args '(1 2 3) ) (assert (= 6 (apply + args) `)
	assert(`
			(set! args '(1 2 "a" "b") )
			(define Fun (lambda args
					(if (null? args)
						""
						(begin
							(define head (car args))
							(+
								(if (number? head) (stringify head) head)
								(apply Fun (cdr args))
							)
						)
					)
	
			))
			(assert (= "12ab" (apply Fun args
			`)
	assert(`(assert (= (vector-nth "abc" 2) 99`)
	assert(`(assert (= "true" (cond
			((= 1 2)     (assert false))
			((> "a" "b") (assert false))
			(true        "true"`)
	assert(`(cond
			((= 1 2)  (assert false))
			(else     (assert true))
			(true     (assert false)`)
	assert(`(assert (= 2 (pcall (lambda (e) (+ e 1)) (lambda () (assert (= 1 1)) (raise 1) (* 3 4)))`)
	assert(`(assert (<= 1 2 2 4`)
	assert(`(assert (>= 10 2 2 1`)
	assert(`(let ((a 1)) (assert (= 2 (eval '(+ a 1`)
	assert(`(set! a (map-new "a" 1)) (map-set! a "a" 2) (assert (= (map-get a "a") 2)`)
}

func BenchmarkRun(b *testing.B) {
	text := strings.Repeat("'(1 2 3)", 10)
	for i := 0; i < b.N; i++ {
		it := New()
		it.Run(text)
	}
}

func BenchmarkAdd(b *testing.B) {
	var a interface{} = strconv.FormatInt(time.Now().Unix(), 10)
	for i := 0; i < b.N; i++ {
		a = strconv.FormatInt(int64(i), 10)
	}
	_ = a
}

func BenchmarkAddValue(b *testing.B) {
	var a = Str(strconv.FormatInt(time.Now().Unix(), 10))
	for i := 0; i < b.N; i++ {
		a = Str(strconv.FormatInt(int64(i), 10))
	}
	_ = a
}

func TestDDD(t *testing.T) {
	count := 10000
	list := []Value{}
ALL:
	for i := 0; ; {
		list = append(list, Num(float64(i)))
		if i++; i == count {
			break ALL
		}
		for rand.Float64() < 0.5 {
			if rand.Intn(2) == 1 {
				list = append(list, _Vddd(nil))
			} else {
				list = append(list, _Vddd([]Value{_Vddd(nil), _Vddd(nil)}))
			}
		}
		for rand.Float64() < 0.33 {
			list = append(list, _Vddd([]Value{Num(float64(i))}))
			if i++; i == count {
				break ALL
			}
		}
		for rand.Float64() < 0.2 {
			list = append(list, _Vddd([]Value{_Vddd([]Value{Num(float64(i))})}))
			if i++; i == count {
				break ALL
			}
		}
	}

	list2 := list
	list3 := list

	if x := Length(list); x != count {
		t.Fatal("length:", x, count, list)
	}

	i := 0.0
	for h, ok := Head(list, false, nil); ok; h, ok = Head(list, false, nil) {
		if n := h.Num(); n != i {
			t.Fatal("head:", h, i, list)
		}
		list, _ = Tail(list)
		i++
	}

	list = list2
	i = float64(count) - 1
	for h, ok := Head(list, true, nil); ok; h, ok = Head(list, true, nil) {
		if n := h.Num(); n != i {
			t.Fatal("last:", h, i, list)
		}
		list, _ = Init(list)
		i--
	}

	_range(0, list3, func(idx int, v Value) (Value, bool) {
		n := v.Num()
		if int(n) != idx {
			t.Fatal(v, idx)
		}
		return v, true
	})
}
