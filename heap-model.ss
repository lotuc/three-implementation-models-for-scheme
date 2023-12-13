(define (lookup var e)
  (let nxtrib ([e e])
    (let nxtelt ([vars (caar e)]
                 [vals (cdar e)])
      (cond
       [(null? vars) (nxtrib (cdr e))]
       [(eq? (car vars) var) vals]
       [else (nxtelt (cdr vars) (cdr vals))]))))

(define (extend env vars vals)
  (cons (cons vars vals) env))

;;;

(define (tail? next)
  (eq? (car next) 'return))

(define (compile x next)
  ;; (display (format "compile: ~s\n" x))
  (cond
   [(symbol? x) `(refer ,x ,next)]
   [(pair? x)
    (record-case x
      [(quote) (obj) `(constant ,obj ,next)]
      [(lambda) (vars body) `(close ,vars ,(compile body '(return)) ,next)]
      [(if) (test then else) (let ([thenc (compile then next)]
                                   [elsec (compile else next)])
                               (compile test `(test ,thenc ,elsec)))]
      [(set!) (var x) (compile x `(assign ,var ,next))]
      [(call/cc) (x) (let ([c `(conti (argument ,(compile x '(apply))))])
                       (if (tail? next)
                           c
                           `(frame ,next ,c)))]
      [else (let loop ([args (cdr x)]
                       [c (compile (car x) '(apply))])
              (if (null? args)
                  (if (tail? next) c `(frame ,next ,c))
                  (loop (cdr args)
                        (compile (car args) `(argument ,c)))))])]
   [else `(constant ,x ,next)]))

(equal? '(constant 42 (halt))
        (compile '42 '(halt)))
(equal? '(refer a (halt))
        (compile 'a '(halt)))
(equal? '(constant 1 (halt))
        (compile '(quote 1) '(halt)))
(equal? '(close (x) (refer x (return))
                (halt))
        (compile '(lambda (x) x) '(halt)))
(equal? '(constant #t (test (constant 42 (halt))
                            (constant 24 (halt))))
        (compile '(if #t 42 24) '(halt)))
(equal? '(constant 1 (assign x (halt)))
        (compile '(set! x 1) '(halt)))
(equal? '(frame (halt) (conti (argument (close (k)
                                               (constant 1 (return))
                                               (apply)))))
        (compile '(call/cc (lambda (k) 1)) '(halt)))
(equal? '(frame (halt) (constant 5 (argument (close (x)
                                                    (refer x (return))
                                                    (apply)))))
        (compile '((lambda (x) x) 5) '(halt)))

