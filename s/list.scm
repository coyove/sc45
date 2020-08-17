(define (list-eq? list1 list2)
  (if (and (list? list1) (list? list2))
    (if (and (null? list1) (null? list2))
      #t (if (or (null? list1) (null? list2))
           #f (if (not (list-eq? (car list1) (car list2)))
                #f (list-eq? (cdr list1) (cdr list2))
                )))
    (= list1 list2)))

(assert (list-eq? '(cons 2 (3 4 5 13)) `(cons 2 ,(cons 3 `(4 5 ,(+ 6 7))))))
(let () (define a '(1))
  (define b# (append a '(3) ))
  (set-car! a 100)
  (assert (list-eq? b# '(1 3)))
  (assert (list-eq? (go->value (make/vararg 1 2 "a")) '(1 2 "a")))
  (assert (list-eq? (go->value (make/vararg2 1 "a")) '(1 "a")))
  (assert (list-eq? (go->value (make/vararg2 1)) '(1)))
  (assert (null? (go->value (make/vararg))))
  (assert (list-eq? (make/list 1000) (make/list 1000)))

  (assert (list-eq? (quasiquote (1 2 3 ,(cons 4 `(5 ,(let ((a 2)) (* a 3) ))))) '(1 2 3 (4 5 6))))
  (assert (list-eq? `( 1 ',(+ 2 3)) '(1 '5)))

  (define (nth-cdr list n)
    (if (= n 0)
      list
      (nth-cdr (cdr list) (- n 1))))

  (define (set-nth! list n v)
    (set-car! (nth-cdr list n) v))

  (assert (list-eq? '(2 3) ((lambda (a . r) r) 1 2 3)))

(let ((a `(1 ,@3))) (assert (= (cdr a) 3)))
