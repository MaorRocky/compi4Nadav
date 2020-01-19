(define foo
  (lambda (x y z)
    (lambda (a b c)
        (+ a b c x y z))))

(define foo2
    (lambda()
        ((foo 1 2 3) 4 5 6)))

(foo2)




       

