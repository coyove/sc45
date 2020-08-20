(define Foreach (lambda (s cb) (letrec [(ForeachImpl (lambda (s cb idx) ; comment
                                                       (if (null? s) () (begin
                                                                          (if (== false (cb (car s) idx )) ()
                                                                            (ForeachImpl (cdr s) cb (+ idx 1)))))))] (ForeachImpl s cb 0)))) ;;

;; (define Counter 0) (Foreach (make/list 1000000) (lambda (v) (begin (set! Counter (+ Counter 1)) (assert (== Counter v)))))
(define StringSplit
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
    ))

(display "misc")
(define flag #f)
(assert (match (StringSplit "aabbccbbd" "bb") () ("aa" "cc" "d") (begin (set! flag #t) #t)))
(assert flag)

(let ()
  (define list (make/bytes 10))
  (vector-set-nth! list 0 10)
  (assert (== 10 (vector-nth list 0)))
  (define s (test/struct-gen true))
  (struct-set! s false 'V 'V2)
  (assert (not (struct-get s 'V 'V2)))
  (set! s (test/struct-gen true))
  (setf! s.V.V2 false)
  (assert (not (getf s.V.V2)))
  )
