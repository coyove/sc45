(letrec ((i64start 6862298800095086341)
      (foo (lambda (v n l) (if (< n 1) v
                           (assert (= v (car l))) (foo (+ v 1) (- n 1) (cdr l) )))))
  (assert (=
            (foo i64start 4 '(6862298800095086341 6862298800095086342 6862298800095086343 6862298800095086344))
            6862298800095086345))
  (display (+ 1.2 6862298800095086345))
  )

(assert (= 0x3fffffffffffff (+ 0x3ffffffffffffe 1)))
(assert (= 36028797018963964 (* 0x3ffffffffffffe 2)))
(assert (= (/ 36028797018963962 2) 0x3ffffffffffffd)))
(assert (< 0x7ffffffffffffe (string->number "0x7fffffffffffff")))

(assert (= 2 (pcall (lambda (e) (+ e 1)) (lambda () (assert (= 1 1)) (raise 1) (* 3 4)))))
(assert (<= 1 2 2 4))
(assert (>= 10 2 2 1))
(let ((a 1)) (assert (= 2 (eval '(+ a 1)))))
(define a (hash-new "a" 1))
(hash-set! a "a" 2)
(assert (= (hash-get a "a")))
(assert (= #/中 0x4e2d))

(iff (assert false) (+ 1 2) )
(assert (or true (assert false)))
(assert (not (and true (or) (assert false))))

(if #f (+ 1 #| inline || comment (assert false) |#  2 3.5) (lambda (a b) ()))

(assert (and (not (list? (cons 1 2))) (list? '(1 2))))
(assert (= 1 ( [lambda () 1])))
(assert (= 1 ( [lambda (a) a] 1)))
(assert (= 3 ( [lambda (a . r) (+ a (length r)) ] 1 2 3)))
(assert (= 0 ( [lambda (a . r) (length r)] 1)))
(assert (= (+ .5 .5) 1.))
(assert (= (+ "a" "b" "c") "abc"))
(assert (= "b" (range (hash-new "a" "A" "b" "b" "c" "") (lambda (l r) (!= l r)))))
(define args '(1 2 3) )
(assert (= 6 (apply + args)))
(assert (= ((if true + -) (- (* 2)) 1) (string->number "-1")))

(assert (= (vector-nth "abc" 2) 99))

(let ((a 9223372036854775807)) (assert (= a 0x7fffffffffffffff)) (assert (= "9223372036854775807" (stringify a))))
(assert (== 20 (reduce + 0 (map (lambda (a) ($ a * 2)) '(1 2 3 4)))))

	(define makecps (lambda (f)
                      (lambda	args #|
                                multiline
                                comments
                                |#
                                [ (last args) (apply f (init args)) ])
                      ))

(define +& (makecps +))  
(apply +& (cons 1 (cons 2 (cons 3 (cons (lambda (r) (assert (= r 6))) ())))))

;; let's play closure
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

(define or# (lambda-syntax args
                           (match args ()
                                  [() '#f]
                                  [(a) a]
                                  [(a b*) `(if ,a ,a ,(cons 'or# b))]
                                  )
                           ))
(assert (not (or#)))
(assert (= 1 (or# 1)))
(assert (= 2 (or# #f 2)))
(assert (or# #f #t (assert false)))

(let ()
  (define defun (lambda-syntax (name paramlist body)
                               (quasiquote (define ,name (lambda ,paramlist ,body)))))
  (defun a (a . r) (* a (length r)))
  (defun b(a . r) (* a (length r)))
  (assert (= 10 (a 5 "a" ())))

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
  (assert (= "12ab" (apply Fun args)))
  )

(assert (= 0.5 ((lambda-syntax (a b)
                               `(begin
                                  (display "macro inline" ,a ,b) 
                                  (/ ,b ,a))) 2 1)))
