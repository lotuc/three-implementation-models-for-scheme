;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; utility

(define-syntax record
  (lambda (x)
    (syntax-case x ()
      [(_ val (var ...) exp ...)
       #'(apply (lambda (var ...) exp ...) val)])))

(record '(1 2 39) (a b c) (+ a b c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; environment extend & lookup

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; compile

(define (tail? next)
  (eq? (car next) 'return))

(define trace-compile #f)

(define (compile x next)
  (when trace-compile (display (format "compile: ~s\n" x)))
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

(set! trace-compile #t)
(compile '42 '(halt))
(compile 'a '(halt))
(compile '(quote 1) '(halt))
(compile '(lambda (x) x) '(halt))
(compile '(if #t 42 24) '(halt))
(compile '(set! x 1) '(halt))
(compile '(call/cc (lambda (k) 1)) '(halt))
(compile '((lambda (x) x) 5) '(halt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; VM

(define (closure body env vars)
  (list body env vars))

(define (continuation stack)
  (closure `(nuate ,stack v) '() '(v)))

(define (call-frame exp env rib stack)
  (list exp env rib stack))

(define trace-vm #f)

(define (VM a x e r s)
  (when trace-vm (print (format "> a: ~s, x: ~s, e: ~s, r: ~s, s: ~s\n" a x e r s)))
  (record-case x
    [(halt) () a]
    [(refer) (var x) (VM (car (lookup var e)) x e r s)]
    [(constant) (obj x) (VM obj x e r s)]
    [(close) (vars body x) (VM (closure body e vars) x e r s)]
    [(test) (then else) (VM a (if a then else) e r s)]
    [(assign) (var x)
     (set-car! (lookup var e) a)
     (VM a x e r s)]
    [(conti) (x)
     (VM (continuation s) x e r s)]
    [(nuate) (stack var)
     (VM (car (lookup var e)) '(return) e r stack)]
    [(frame) (ret x)
     (VM a x e '() (call-frame ret e r s))]
    [(argument) (x)
     (VM a x e (cons a r) s)]
    [(apply) ()
     (if (procedure? a)
         (VM (apply a r) '(return) e '() s)
         (record a (body env vars)
                 (VM a body (extend env vars r) '() s)))]
    [(return) ()
     (record s (x e r s)
             (VM a x e r s))]))

;;; - return the (a)ccumulator's value
(VM 42 '(halt) 'env 'rib 'stack)

;;; - replace e(x)pression base on (a)ccumulator's value and continue
;;;   - test-then if a is truthy
;;;   - test-else if a is falsy
(VM #t '(test (constant 4 (halt)) (constant 2 (halt))) 'env 'rib 'stack)
(VM #f '(test (constant 4 (halt)) (constant 2 (halt))) 'env 'rib 'stack)

;;; - mutate (e)nvironment's assign-var to value of (a)ccumulator
;;; - replace e(x)pression with assign-x and continue
(VM 42 '(assign a (halt)) (extend '() '(a b) '(0 0)) 'rib 'stack)

;;; - replace (a)ccumulator with refer-var's value found in (e)nvironment
;;; - replace e(x)pression with refer-x and continue
(VM 'prev-exp '(refer a (halt)) (extend '() '(a) '(42)) 'rib 'stack)

;;; - replace (a)ccumulator to constant-obj
;;; - replace e(x)pression with constant-x and continue
(VM 'prev-exp '(constant 10 (halt)) 'env 'rib 'stack)

;;; - replace (a)ccumulator with captured closure, which consist of
;;;   - close-body & close-vars &
;;; - replace e(x)pression with close-x and continue
(VM 'exp `(close (a) (refer a (halt)) (halt)) 'env 'rib 'stack)

;;; - replace e(x)pression, (e)nvironment, (r)ib & (s)tack with current (s)tack
;;    frame and continue
(VM 'prev-exp '(return) 'prev-env 'prev-rib '((halt) env rib stack))

;;; - replace (a)ccumulator with the nuate-var's value found in (e)nvironment
;;; - replace (s)tack to the nuate-stack
;;; - replace e(x)pression with (return) and continue
(VM 'prev-exp
    '(nuate ((constant 45 (halt)) env rib stack) var)
    (extend '() '(var) '(42))
    'prev-rib
    'prev-stack)

;;; - replace (a)ccumulator with a continuation closure
;;;   - closure-body: (nuate stack v), notice that it captures the current stack
;;;   - closure-var: (v), corresponds to the nuate-var
;;;   - closure-env: empty
;;; - replace e(x)pression with conti-x and continue
(VM 'prev-exp
    '(conti (constant 42 (halt)))
    'prev-env
    'prev-rib
    'prev-stack)

;;; - replace (r)ib with (a)ccumulator's value consed to (r)ib
;;; - replace e(x)pression with argument-x and continue
(VM 'prev-exp '(argument (constant 42 (halt))) 'env '(43) 'stack)

;;; - assume the (a)ccumulator to be a closure
;;; - extend (e)nvironment with closure-var & (r)ib
;;; - replace (r)ib with empty one
;;; - replace e(x)pression with closure-body
(VM '((refer var (halt)) () (var))
    '(apply)
    'prev-env
    '(42)
    'stack)
;;; customized - apply scheme procedure
(VM +
    '(apply)
    'prev-env
    '(42 1)
    '((halt) () () ()))

;;; - replace (s)tack with captured frame of
;;;   - e(x)pression: frame-ret
;;;   - (e)nvironment
;;;   - (r)ib
;;;   - (s)tack
;;; - replace (r)ib with empty rib
;;; - replace e(x)pression with frame-x and continue
(VM 'prev-exp '(frame (halt) (constant 42 (halt))) 'env 'rib 'stack)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; eval

(define (evaluate exp env)
  (VM -1 (compile exp '(halt)) env '() '()))

(evaluate '((lambda (x) x) 42) '())
(evaluate '((lambda (x y) y) 42 24) '())
(evaluate '((lambda (x) ((lambda (_) x) (set! x 42))) 0) '())
(evaluate '(if #t 4 2) '())
(evaluate '(if #f 4 2) '())

(evaluate '(call/cc (lambda (k) 10)) '())
(evaluate '(call/cc (lambda (k) (k 10))) '())
(evaluate '(call/cc (lambda (k) ((lambda (x) (k x)) 20))) '())

(define scheme-env (extend '()
                           '(= + - * / car cdr null?)
                           `(,= ,+ ,- ,* ,/ ,car ,cdr ,null?)))

(evaluate '(= 1 1) scheme-env)
(evaluate '((lambda (x y) (+ x y)) 1 2) scheme-env)

(set! trace-compile #f)
(set! trace-vm #f)

;; recursive with Y combinator

(evaluate '((lambda (h)
              ((h (lambda (fact)
                    (lambda (n)
                      (if (= n 0)
                          1
                          (* n (fact (- n 1)))))))
               10))
            (lambda (h)
              ((lambda (f) (f f))
               (lambda (f) (h (lambda (n) ((f f) n)))))))
          scheme-env)

(evaluate '((lambda (h)
              (((lambda (lst)
                  (lambda (n)
                    (call/cc
                     (lambda (k)
                       (((h (lambda (mul)
                              (lambda (lst)
                                (lambda (n)
                                  (if (null? lst)
                                      n
                                      (if (= 0 (car lst))
                                          (k n)
                                          ((mul (cdr lst))
                                           (* n (car lst)))))))))
                         lst)
                        n)))))
                '(1 2 3 4 5 6 0 8 9))
               1))
            (lambda (h)
              ((lambda (f) (f f))
               (lambda (f) (h (lambda (n) ((f f) n)))))))
          scheme-env)
