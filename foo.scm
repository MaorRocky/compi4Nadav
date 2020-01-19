(define foo
    (lambda (x)
        ((lambda y y) x)))

(foo 1)