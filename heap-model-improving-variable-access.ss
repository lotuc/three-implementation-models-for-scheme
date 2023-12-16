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

;;; static var & dynamic val extending
(define (extend e r)
  (cons r e))

(define (compile-lookup var e)
  (let nxtrib ([e e] [rib 0])
    (let nxtelt ([vars (car e)] [elt 0])
      (cond
       [(null? vars) (nxtrib (cdr e) (+ rib 1))]
       [(eq? (car vars) var) (cons rib elt)]
       [else (nxtelt (cdr vars) (+ elt 1))]))))

(compile-lookup 'a '((a) (b c)))
(compile-lookup 'b '((a) (b c)))
(compile-lookup 'c '((a) (b c)))

(define (lookup access e)
  (let nxtrib ([e e] [rib (car access)])
    (if (zero? rib)
        (let nxtelt ([vs (car e)] [elt (cdr access)])
          (if (zero? elt)
              vs
              (nxtelt (cdr vs) (- elt 1))))
        (nxtrib (cdr e) (- rib 1)))))

(lookup '(0 . 0) '((a) (b c)))
(lookup '(1 . 0) '((a) (b c)))
(lookup '(1 . 1) '((a) (b c)))

;;; lookup from dynamic environment with compile time found position
(lookup (compile-lookup 'a '((a) (b c))) '((42) (43 44)))
(lookup (compile-lookup 'b '((a) (b c))) '((42) (43 44)))
(lookup (compile-lookup 'c '((a) (b c))) '((42) (43 44)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; compile

(define (tail? next)
  (eq? (car next) 'return))

(define trace-compile #t)

(define (compile x e next)
  (when trace-compile (display (format "compile: ~s\n" x)))
  (cond
   [(symbol? x) `(refer ,(compile-lookup x e) ,next)]
   [(pair? x)
    (record-case x
      [(quote) (obj)
       `(constant ,obj ,next)]
      [(lambda) (vars body)
       `(close ,vars ,(compile body (extend e vars) '(return)) ,next)]
      [(if) (test then else)
       (let ([thenc (compile then e next)]
             [elsec (compile else e next)])
         (compile test e `(test ,thenc ,elsec)))]
      [(set!) (var x)
       (compile x e `(assign ,(compile-lookup var e) ,next))]
      [(call/cc) (x)
       (let ([c `(conti (argument ,(compile x e '(apply))))])
         (if (tail? next)
             c
             `(frame ,next ,c)))]
      [else (let loop ([args (cdr x)]
                       [c (compile (car x) e '(apply))])
              (if (null? args)
                  (if (tail? next) c `(frame ,next ,c))
                  (loop (cdr args)
                        (compile (car args) e `(argument ,c)))))])]
   [else `(constant ,x ,next)]))

(set! trace-compile #t)
(compile '42 '() '(halt))
;; This one fails now cause of static lookup of a failed
;; (compile 'a '() '(halt))
(compile 'a '((a)) '(halt))
(compile '(quote 1) '() '(halt))
(compile '(lambda (x) x) '() '(halt))
(compile '(if #t 42 24) '() '(halt))
;; This one fails now cause of static lookup of a failed
;; (compile '(set! x 1) '() '(halt))
(compile '(set! x 1) '((x)) '(halt))
(compile '(call/cc (lambda (k) 1)) '() '(halt))
(compile '((lambda (x) x) 5) '() '(halt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; VM

(define (closure body env vars)
  (list body env vars))

(define (call-frame exp env rib stack)
  (list exp env rib stack))

(define (continuation stack)
  (closure `(nuate ,stack (0 . 0)) '() '(v)))

(define trace-vm #f)

(define (VM a x e r s)
  (when trace-vm (display (format "> a: ~s, x: ~s, e: ~s, r: ~s, s: ~s\n" a x e r s)))
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
                 (VM a body (extend env r) '() s)))]
    [(return) ()
     (record s (x e r s)
             (VM a x e r s))]))

(set! trace-vm #t)
(VM 42 '(halt) 'env 'rib 'stack)
(VM #t '(test (constant 4 (halt)) (constant 2 (halt))) 'env 'rib 'stack)
(VM #f '(test (constant 4 (halt)) (constant 2 (halt))) 'env 'rib 'stack)
(VM 42 '(assign (0 . 0) (halt)) '((0 0)) 'rib 'stack)
(VM 'prev-exp '(refer (0 . 0) (halt)) '((42)) 'rib 'stack)
(VM 'prev-exp '(constant 10 (halt)) 'env 'rib 'stack)
(VM 'exp `(close (a) (refer (0 . 0) (halt)) (halt)) 'env 'rib 'stack)
(VM 'prev-exp '(return) 'prev-env 'prev-rib '((halt) env rib stack))
(VM 'prev-exp
    '(nuate ((constant 45 (halt)) env rib stack) (0 . 0))
    '((42))
    'prev-rib
    'prev-stack)
(VM 'prev-exp
    '(conti (constant 42 (halt)))
    'prev-env
    'prev-rib
    'prev-stack)
(VM 'prev-exp '(argument (constant 42 (halt))) 'env '(43) 'stack)
(VM '((refer (0 . 0) (halt)) () (var))
    '(apply)
    'prev-env
    '(42)
    'stack)
(VM +
    '(apply)
    'prev-env
    '(42 1)
    '((halt) () () ()))
(VM 'prev-exp '(frame (halt) (constant 42 (halt))) 'env 'rib 'stack)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; eval

(define (evaluate exp static-env env)
  (VM -1 (compile exp static-env '(halt)) env '() '()))

(evaluate '((lambda (x) x) 42) '() '())
(evaluate '((lambda (x y) y) 42 24) '() '())
(evaluate '((lambda (x) ((lambda (_) x) (set! x 42))) 0) '() '())
(evaluate '(if #t 4 2) '() '())
(evaluate '(if #f 4 2) '() '())

(evaluate '(call/cc (lambda (k) 10)) '() '())
(evaluate '(call/cc (lambda (k) (k 10))) '() '())
(evaluate '(call/cc (lambda (k) ((lambda (x) (k x)) 20))) '() '())

(define scheme-static-env '((= + - * / car cdr null?)))
(define scheme-env `((,= ,+ ,- ,* ,/ ,car ,cdr ,null?)))

(evaluate '(= 1 1) scheme-static-env scheme-env)
(evaluate '((lambda (x y) (+ x y)) 1 2) scheme-static-env scheme-env)

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
          scheme-static-env
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
          scheme-static-env
          scheme-env)
