(let ((foo (lambda args (match args ()
	('(<= _ 2)) "str,<=2"
	('(> _ 2)) (+ "str,>2" (number->string _))
	(*) "whaat?")))) 

		(assert (= (foo 1) "str,<=2"))
		(assert (= (foo 3) "str,>23"))
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

(define for "for")

((lambda ()
(define for (lambda-syntax args
                            (match args ()
                                   [v start end #:step step body*]
                                   `(letrec ((foo (lambda (current end step)
                                                    (if ([if (<= step 0) >= <=] current end)
                                                      (begin
                                                        (define ,v current)
                                                        ,@body
                                                        (foo (+ current step) end step))))))
                                      (foo ,start ,end ,step))
                                   [v start end body*]
                                   `(letrec ((foo (lambda (current end)
                                                    (if (<= current end)
                                                      (begin
                                                        (define ,v current)
                                                        ,@body
                                                        (set! current (+ current 1))
                                                        (foo current end))))))
                                      (foo ,start ,end)))))

(define macro-gen-9-counter 0)
(define macro-gen-9-flag "")
(define macro-gen-9 (lambda-syntax () 
                                   (set! macro-gen-9-counter (+ 1 . (macro-gen-9-counter . ())))
                                   `(begin
                                      (set! macro-gen-9-flag
                                        (+ macro-gen-9-flag (number->string ,macro-gen-9-counter)))
                                      9)))

(let ((text ""))
  (for i 0 (macro-gen-9)
       (for j (macro-gen-9) i #:step -1
            (set! text (+ text (number->string i) "-" (number->string j) " ")))
       (set! text (+ text "\n")))
  (display text))

(assert (= macro-gen-9-flag "12222222222"))

(let ((l '(2 4 6))) 
  (for i 2 6 #:step 2
       (display l)
       (assert (= (car l) i))
       (set! l (cdr l))))

(eval '(let ((l '(2 4 6))) 
  (for i 2 6 #:step 2
       (display l)
       (assert (= (car l) i))
       (set! l (cdr l))))) 
))

(assert (= for "for"))
