;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; utility

(define-syntax record
  (lambda (x)
    (syntax-case x ()
      [(_ val (var ...) exp ...)
       #'(apply (lambda (var ...) exp ...) val)])))

(record '(1 2 39) (a b c) (+ a b c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; stack

(define stack (make-vector 1000))

(define (push x s)
  (vector-set! stack s x)
  (+ s 1))

(define (index s i)
  (vector-ref stack (- (- s i) 1)))

(define (index-set! s i v)
  (vector-set! stack (- (- s i) 1) v))

(define s0 0)
(define s1 (push 20 s0))
(define s2 (push 40 s1))
(index s2 0)                            ; 40
(index s2 1)                            ; 20

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; environment extend & lookup

;;; static var & dynamic val extending
(define (extend e r)
  (cons r e))

(define (compile-lookup var e return)
  (let nxtrib ([e e] [rib 0])
    (let nxtelt ([vars (car e)] [elt 0])
      (cond
       [(null? vars) (nxtrib (cdr e) (+ rib 1))]
       [(eq? (car vars) var) (return rib elt)]
       [else (nxtelt (cdr vars) (+ elt 1))]))))

(compile-lookup 'a '((a) (b c)) (lambda (rib elt) `(,rib . ,elt)))
(compile-lookup 'b '((a) (b c)) (lambda (rib elt) `(,rib . ,elt)))
(compile-lookup 'c '((a) (b c)) (lambda (rib elt) `(,rib . ,elt)))

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
(lookup (compile-lookup 'a '((a) (b c)) (lambda (rib elt) `(,rib . ,elt))) '((42) (43 44)))
(lookup (compile-lookup 'b '((a) (b c)) (lambda (rib elt) `(,rib . ,elt))) '((42) (43 44)))
(lookup (compile-lookup 'c '((a) (b c)) (lambda (rib elt) `(,rib . ,elt))) '((42) (43 44)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; compile

(define (functional body e)
  (list body e))

(define trace-compile #f)

(define (compile x e next)
  (when trace-compile (display (format "compile: ~s\n" x)))
  (cond
   [(symbol? x)
    (compile-lookup
     x e (lambda (rib elt) `(refer ,rib ,elt ,next)))]
   [(pair? x)
    (record-case x
      [(quote) (obj) `(constant ,obj ,next)]
      [(lambda) (vars body)
       `(close
         ,(compile body (extend e vars) `(return ,(+ (length vars) 1)))
         ,next)]
      [(if) (test then else)
       (let ([thenc (compile then e next)]
             [elsec (compile else e next)])
         (compile test e `(test ,thenc ,elsec)))]
      [(set!) (var x)
       (compile-lookup
        var e (lambda (rib elt)
                (compile x e `(assign ,rib ,elt ,next))))]
      [else
       (let loop ([args (cdr x)]
                  [c (compile (car x) e '(apply))])
         (if (null? args)
             (list 'frame next c)
             (loop (cdr args)
                   (compile (car args) e `(argument ,c)))))])]
   [else `(constant ,x ,next)]))

(set! trace-compile #t)
(compile 'a '((a)) '(halt))
(compile 10 '() '(halt))
(compile ''a '() '(halt))
(compile '(lambda (x) x) '() '(halt))
(compile '(if #t 4 2) '() '(halt))
(compile '(set! a 42) '((a)) '(halt))
(compile '((lambda (x) x) 42) '() '(halt))
(compile '((lambda (x y) y) 42) '() '(halt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; vm

(define (find-link n e)
  (if (= n 0)
      e
      (find-link (- n 1) (index e -1))))

(define (VM a x e s)
  (when trace-vm (display (format "> a: ~s, x: ~s, e: ~s, s: ~s\n" a x e s)))
  (record-case x
    [(halt) () a]
    [(refer) (n m x)
     (VM (index (find-link n e) m) x e s)]
    [(constant) (obj x)
     (VM obj x e s)]
    [(close) (body x)
     (VM (functional body e) x e s)]
    [(test) (then else)
     (VM a (if a then else) e s)]
    [(assign) (n m x)
     (index-set! (find-link n e) m a)
     (VM a x e s)]
    [(frame) (ret x)
     (VM a x e (push ret (push e s)))]
    [(argument) (x)
     (VM a x e (push a s))]
    [(apply) ()
     (record a (body link)
             (VM a body s (push link s)))]
    [(return) (n)
     (let ([s (- s n)])
       (VM a (index s 0) (index s 1) (- s 2)))]))

(set! trace-vm #t)

;;; 1. pushes ret-expression & current env into stack
;;; 2. (s)tack increases 2 because of the two pushes
(begin (set! stack (make-vector 3))
       (VM 24 '(frame '(constant 2 (halt)) (halt)) 'env 1)
       (display stack))

;;; 1. push the (a)ccumulator into stack
;;; 2. (s)tack increates 1 because of the push
(begin (set! stack (make-vector 3))
       (VM 24 '(argument (halt)) 'env 1)
       (display stack))

;;; 1. push environment from (a)ccumulator's functional-link into stack
;;; 2. (s)tack increates 1 because of the push
;;; 3. replace e(x)pression with (a)ccumulator's functional-body
;;; 4. replace (e)nvironment with (s)tack
(begin (set! stack (make-vector 3))
       (VM '((halt) env) '(apply) 'prev-env 1)
       (display stack))

;;; (frame, argument..., apply) instruction sequence will create a full call
;;; frame
;;; <ret-exp, env, arg-n, ..., arg-1, functional-link>

;;; with the call frame created, and call
;; (return n)
;;; n = (+ (length arguments) 1)

;;; 1. replace e(x)pression with call-frame--ret-exp
;;; 2. replace (e)nviornment with call-frame--env
;;; 3. replace (s)tack with outer frame
(begin (set! stack (make-vector 4))
       (vector-set! stack 3 '(constant 42 (halt)))
       (vector-set! stack 2 'new-env)
       (VM 0 '(return 2) 'prev-env 6)
       (display stack))

;;; <ret-exp, env, arg-n, ..., arg-1, arg-0, functional-link>
(begin (set! stack (make-vector 10))
       (vector-set! stack 9 5)
       (vector-set! stack 7 42)
       (vector-set! stack 3 142)
       (vector-set! stack 2 1142)
       (display stack) (display "\n")
       ;; 0, 1 : argument 0 of current call frame
       (display (format "=> ~s\n" (VM 0 '(refer 0 1 (halt)) 9 'stack)))
       ;; 1, 1 : argument 1 of the frame where function definition captured
       ;; 1, 2 : argument 2 of the frame where function definition captured
       (display (format "=> ~s\n" (VM 0 '(refer 1 1 (halt)) 9 'stack)))
       (display (format "=> ~s\n" (VM 0 '(refer 1 2 (halt)) 9 'stack))))

(set! stack (make-vector 10))
(VM 42 '(halt) 'env 'stack)
(VM 'prev '(constant 10 (halt)) 'env 'stack)
(VM 'prev '(close (constant 10 (return)) (halt)) 'env 'stack)
(VM #t '(test (constant 4 (halt)) (constant 2 (halt))) 'env 'stack)
(VM #f '(test (constant 4 (halt)) (constant 2 (halt))) 'env 'stack)
(VM 24 '(assign 0 1 (refer 0 1 (halt))) 2 'stack)

(define (evaluate x)
  (VM '() (compile x '() '(halt)) 0 0))

(set! stack (make-vector 1000))
(evaluate '1)
(evaluate '(lambda (x) x))
(evaluate '((lambda (x) x) 10))
