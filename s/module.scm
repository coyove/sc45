(lambda (d) 
  (if (number? d)
    (raise d)
    (d)))
