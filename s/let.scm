(define let*-native (lambda-syntax (bindings . body)
                                   (set! body (cons 'begin body))
                                   (letrec ((work (lambda (lst)
                                                    (if (not (null? lst)) (begin
                                                                            (set! body (list 'let (list (last lst)) body))
                                                                            (work (init lst))
                                                                            )
                                                      )
                                                    )
                                                  )) (work bindings))
                                   body
                                   ))

(define let*-native-match (lambda-syntax L
                                         (match L ()
                                                ( (b* (s v)) body* ) (quasiquote 
                                                                       (let*-native-match ,b (let ((,s ,v)) ,(cons 'begin body))))
                                                ( () body* ) (cons 'begin body)
                                                )))


(define flag ())
(let*-native ((a 1) (b (+ a 1)) (c (+ b a))) (assert (= c 3)) (set! flag "let*-native"))
(assert (= flag "let*-native"))

(let*-native-match ((a 1) (b (+ a 1)) (c (+ b a))) (assert (= c 3)) (set! flag "let*-native-match"))
(assert (= flag "let*-native-match"))

(let* ((a 1) (b (+ a 1))) (assert (= b 2)))
