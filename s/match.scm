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
