(let ((foo (lambda args (match args ()
	(#:string '(<= _ 2)) "str,<=2"
	(#:string '(> _ 2)) (+ "str,>2" (number->string _))
	(#:number) "num"
	(*) "whaat?")))) 

		(assert (= (foo "aa" 1) "str,<=2"))
		(assert (= (foo "bb" 3) "str,>23"))
		(assert (= (foo 0) "num"))
        (display "wtf")
		(assert (= (foo) "whaat?")))


(assert (match (append () '(1 2)) () (1 2) #t))
(assert (= 3 (match '(letadd a (1 2)) (letadd) (letadd a (v1 v2)) (+ v1 v2))))
(assert (= 24 (match '(letaddmul a (1 2 3) mul 4) (letaddmul mul) (letaddmul a (args*) mul s) (* s (reduce + 0 args)))))
(assert (= -24 (match '(letsubmul a (1 2 3 4)) (letsubmul) (letsubmul a (args* mul)) (* mul (reduce - 0 args)))))

(define cond-inner (lambda-syntax (s . args)
                            (match args (else)
                                   [(else b)] b
                                   [(c b) rest*] `(if (= ,c ,s) ,b (cond-inner ,s ,@rest))
                                   [] #f)))

(define cond (lambda-syntax (s . args) `(let ((s ,s)) (cond-inner s ,@args))))

(assert (= "A" (cond 1 (1 "A"))))
(assert (= "B" (cond 2 (1 "A") (2 "B"))))
(assert (= "C" (cond 3 (1 "A") (2 "B") (else "C"))))

(let* ((counter 0) (foo (lambda (v) (set! counter (+ counter 1)) v)))
  (display "cond counter")
  (assert (= "B" (cond (foo 2)
                       (1 "A")
                       (2 "B"))))
  (assert (= counter 1)))
