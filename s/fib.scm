(define Fib (lambda (v) (if (< v 2) v (+ (Fib (- v 1)) (Fib (- v 2)))))) (assert (= 21 (Fib 8)))
(Fib 35)
