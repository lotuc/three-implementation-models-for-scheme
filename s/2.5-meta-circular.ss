(define (meta exp)
  (exec exp '()))

(define (lookup var e)
  (define (nxtrib e)
    (define (nxtelt vars vals)
      (cond
       [(null? vars) (nxtrib (cdr e))]
       [(eq? (car vars) var) vals]
       [else (nxtelt (cdr vars) (cdr vals))]))
    (nxtelt (caar e) (cdar e)))
  (nxtrib e))

(define (extend env vars vals)
  (cons (cons vars vals) env))

(lookup 'a (extend '() '(a) '(2)))
(lookup 'a (extend (extend '()
                           '(a) '(2))
                   '(a b) '(42 2)))

(define (exec exp env)
  (cond
   [(symbol? exp) (car (lookup exp env))]
   [(pair? exp)
    (record-case exp
      [quote (obj) obj]
      [lambda (vars body) (lambda (vals)
                            (exec body (extend env vars vals)))]
      [if (test then else) (if (exec test env)
                               (exec then env)
                               (exec else env))]
      [set! (var val) (set-car! (lookup var env) (exec val env))]
      [call/cc (exp) (call/cc
                      (lambda (k)
                        ((exec exp env)
                         (list (lambda (args) (k (car args)))))))]
      [else ((exec (car exp) env)
             (map (lambda (x) (exec x env)) (cdr exp)))])]
   [else exp]))

(meta '(quote (a b 42)))
(meta '((lambda (a) a) 2))
(meta '(if #t 1 2))
(meta '((lambda (x) ((lambda (_) x) (set! x 42))) 2))
(meta '(call/cc (lambda (k) 1)))
(meta '(call/cc (lambda (k) (k 10))))
