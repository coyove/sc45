package scmbed

import (
	"fmt"
	"log"
	"strconv"
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
	it.Store("assert", F(1, func(s *State) {
		if s.In().IsFalse() {
			panic(fmt.Errorf("assertion failed"))
		}
	}))
	// 	it.Install("var/test", 1|Vararg, func(s *State) {
	// 		v := s.In(0, 'n').Num()
	// 		a := s.Args[1:]
	// 		if v == 100 {
	// 			s.Out = Val(fmt.Errorf(""))
	// 		} else {
	// 			av := a[0].Num()
	// 			a[0] = Num(av + v)
	// 			s.Out = Lst(append([]Value{}, a...)...)
	// 		}
	// 	})
	// 	// it.Install("callee", "", func(v int64) int64 { return v * 10 })
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
	it.InstallGo("make/vararg", func(v ...interface{}) []interface{} {
		return v
	})
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
			err, ok := f.Fun().Call(Str(k), v)
			log.Println("===", err, ok)
			if err.IsFalse() {
				s.Out = v
				return
			}
		}
	}))
	assert := func(v string) {
		r, err := it.Run(v)
		if err != nil {
			t.Fatal(v, err)
		}
		log.Println(v, "===>", r)
	}
	it.Store("iff", F(2|Macro, func(s *State) {
		s.In()
		s.Out = s.In()
	}))

	assert(`(let ((foo (lambda args (match args ()
	(#:string '(<= _ 2)) "str,<=2"
	(#:string '(> _ 2)) (+ "str,>2" (number->string _))
	(#:number) "num"
	(*) "whaat?")))) 

		(assert (= (foo "aa" 1) "str,<=2"))
		(assert (= (foo "bb" 3) "str,>23"))
		(assert (= (foo 0) "num"))
		(assert (= (foo) "whaat?"))
		`)

	assert("(assert (match (append () '(1 2)) () (1 2) #t)")
	assert(`(define-macro let*-native-match (lambda L
			(match L ()
				( (b* (s v)) body ) (quasiquote (let*-native-match ,b (let ((,s ,v)) ,body)))
				( () body ) body
		)`)
	assert(`(define-macro or# (lambda args
	 	 		(match args ()
					() '#f
					(a) a
					(a b*) ` + "`" + `(if ,a ,a ,(cons 'or# b))
	 	 		)
	 	 	)`)
	assert(`
(assert (not (or#)))
(assert (= 1 (or# 1)))
(assert (= 2 (or# #f 2)))
(assert (or# #f #t (assert false`)

	assert(`(assert (= 3 (match '(letadd a (1 2)) (letadd) (letadd a (v1 v2)) (+ v1 v2))`)
	assert(`(assert (= 24 (match '(letaddmul a (1 2 3) mul 4) (letaddmul mul) (letaddmul a (args*) mul s) (* s (reduce + 0 args)`)
	assert(`(assert (= -24 (match '(letsubmul a (1 2 3 4)) (letsubmul) (letsubmul a (args* mul)) (* mul (reduce - 0 args)`)
	assert("(assert (and (not (list? (cons 1 2))) (list? '(1 2")
	assert(`(define Fib (lambda (v) (if (< v 2) v (+ (Fib (- v 1)) (Fib (- v 2)))))) (assert (= 21 (Fib 8) `)
	// assert(`(Fib 35) `)
	// 	assert("(eval (unwrap-macro (list 'define `(madd2 a ,(string->symbol \"b\")) (list 'let `[(c ,(cons '+ (cons 'a (cons 'b [] ))) )] '(* (let ((a a)) a) b c))")
	assert(`(define-macro let*-native (lambda (bindings . body)
	 		(set! body (cons 'begin body))
	 		(letrec ((work (lambda (lst)
	 			(if (not (null? lst)) (begin
	 				(set! body (list 'let (list (last lst)) body))
	 				(work (init lst))
	 			))))) (work bindings))
	 		body
	 	)`)

	assert("(let*-native ((a 1) (b (+ a 1)) (c (+ b a))) (assert (= c 3))")
	assert("(let*-native-match ((a 1) (b (+ a 1)) (c (+ b a))) (assert (= c 3))")
	// 	assert(`(assert (= (madd2 10 20) 6000)))`)
	assert("(assert (= #/中 0x4e2d")
	assert(`(if #f (+ 1 #| inline || comment (assert false) #|#  2 3.5) (lambda (a b) ())`)
	// 	assert(`(assert ( [lambda* (a b) (assert (= a 1)) (null? b)] 1) `)
	// 	assert(`( [lambda* (a [b (+ a 1)] ) (assert (= a 1)) (assert (= b 2))] 1) `)
	// 	assert(`( [lambda* (a b c...) (assert (= 1 (length c))) (assert (car c))] 1 2 #t) `)
	assert("(let* ((a 1) (b (+ a 1))) (assert (= b 2))")
	assert(`
	 	 (define (list-eq? list1 list2)
	 	 	(if (and (list? list1) (list? list2))
	 			(if (and (null? list1) (null? list2))
	 				#t (if (or (null? list1) (null? list2))
	 					#f (if (not (list-eq? (car list1) (car list2)))
	 						#f (list-eq? (cdr list1) (cdr list2))
	 				)))
	 			(= list1 list2)))
	
		 (assert (list-eq? '(cons 2 (3 4 5 13)) ` + "`" + `(cons 2 ,(cons 3 ` + "`" + `(4 5 ,(+ 6 7))))))
	 	 (let () (define a '(1))
	 	 (define b# (append a '(3) ))
	 	 (set-car! a 100)
	 	 (assert (list-eq? b# '(1 3)))
	 	 (assert (list-eq? (go->value (make/vararg 1 2 "a")) '(1 2 "a")))
	 	 (assert (null? (go->value (make/vararg))))
	 	 (assert (list-eq? (make/list 1000) (make/list 1000)`)
	assert("(assert (list-eq? (quasiquote (1 2 3 ,(cons 4 `(5 ,(let ((a 2)) (* a 3) ))))) '(1 2 3 (4 5 6))))")
	assert("(assert (list-eq? `( 1 ',(+ 2 3)) '(1 '5)))")
	// assert("(assert (println (list 'defun 'a) '(defun a)")
	assert(`(let () (define list (make/bytes (i64 10))) (vector-set-nth! list 0 10) (assert (== 10 (vector-nth list 0)`)
	assert(`(let ((a (i64 9223372036854775807))) (assert (= a (i64 0x7fffffffffffffff))) (assert (= "#9223372036854775807" (stringify a)`)
	// assert(`(let () (define-record-type user (fields name ok))
	// 	(define a (make-user "" #f)) (user-ok-set! a #t) (assert (user-ok a)) `)
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

	// assert(`(define Counter 0) (Foreach (make/list 1000000) (lambda (v) (begin (set! Counter (+ Counter 1)) (assert (== Counter v`)
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
	 	 					(begin (set! First-occur _2) #f)
	 						#t
	 					))))
	 	 		(if (== -1 First-occur)
	 	 			(list S)
	 	 			(begin
	 	 				(define results (list (vector-slice S 0 First-occur) ))
	 	 				(set! results (append results (StringSplit (vector-slice S (+ First-occur (vector-len Sep)) (vector-len S) ) Sep)))
	 	 				results
	 	 			)
	 	 		))
	 	 	))`)
	assert(`(define flag #f) (assert (match (StringSplit "aabbccbbd" "bb") () ("aa" "cc" "d") (begin (set! flag #t) #t))) (assert flag`)
	assert(`(assert (= 1 ( [lambda () 1])`)
	assert(`(assert (= 1 ( [lambda (a) a] 1)`)
	assert(`(assert (= 3 ( [lambda (a . r) (+ a (length r)) ] 1 2 3)`)
	assert(`(assert (= 0 ( [lambda (a . r) (length r)] 1)`)
	// 	assert(`(let ((a (json-parse "{\"a\":{\"b\":1}}"))) (assert (= (map-get (map-get a "a") "b") 1 `)
	assert(`
	 	 (define (nth-cdr list n)
	 	 	(if (= n 0)
	 	 		list
	 	 		(nth-cdr (cdr list) (- n 1))))
	
	 	 (define (set-nth! list n v)
	 	 	(set-car! (nth-cdr list n) v))
	
	 	 (define-macro defun (lambda (name paramlist body)
	 	 	(quasiquote (define ,name (lambda ,paramlist ,body))
	 	 	`)
	assert(`(defun a (a . r) (* a (length r))) (defun b(a . r) (* a (length r))) (assert (= 10 (a 5 "a" ())))
	// 	(assert (= 1 (b 1 1
	// 	`)
	// 	assert(`(eval (unwrap-macro (list 'defun 'madd '(a b) '(+ a b`)
	// 	assert(`(assert (= (madd "a" "b") "ab"))`)
	assert(`(iff (assert false) (+ 1 2) )`)
	assert(`(assert (or true (assert false`)
	assert(`(assert (not (and true (or) (assert false))`)
	// 	assert("(stringify '(+ \"asd\" 2))")
	//
	assert(`(assert (list-eq? '(2 3) ((lambda (a . r) r) 1 2 3`)
	assert(`(define s (test/struct-gen true)) (struct-set! s false 'V 'V2) (assert (not (struct-get s 'V 'V2`)
	assert(`(set! s (test/struct-gen true)) (setf! s.V.V2 false) (assert (not (getf s.V.V2`)
	assert(`(assert (= ((if true + -) (- (* 2)) 1) (string->number "-1"))`)
	// 	assert(`(assert (= (car (var/test 1 2 3)) 3)`)
	// 	assert(`(assert (error? (var/test 100 2 3)`)
	assert(`(assert (= (+ .5 .5) 1.`)
	assert(`(assert (= (+ "a" "b" "c") "abc"`)
	assert(`(assert (= "b" (range (hash-new "a" "A" "b" "b" "c" "") (lambda (l r) (!= l r)`)
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
	// 	assert(`(assert (= "true" (cond
	// 			((= 1 2)     (assert false))
	// 			((> "a" "b") (assert false))
	// 			(true        "true"`)
	// 	assert(`(cond
	// 			((= 1 2)  (assert false))
	// 			(else     (assert true))
	// 			(true     (assert false)`)
	assert(`(assert (= 2 (pcall (lambda (e) (+ e 1)) (lambda () (assert (= 1 1)) (raise 1) (* 3 4)))`)
	assert(`(assert (<= 1 2 2 4`)
	assert(`(assert (>= 10 2 2 1`)
	assert(`(let ((a 1)) (assert (= 2 (eval '(+ a 1`)
	assert(`(set! a (hash-new "a" 1)) (hash-set! a "a" 2) (assert (= (hash-get a "a") 2)`)
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
