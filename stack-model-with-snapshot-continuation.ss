;;; Chapter 4.2 - Stack allocating the Dynamic Chain
;;;
;;; 1. This one is based on Chapter 3.5 (heap-model-improving-variable-access.ss)
;;; 2. It just replaces the stack implementation with a real one (implemented
;;;    with vector at Chapter 4.1 (heap-model.ss)
;;;    - it only affects the VM stack implementation

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

(define (closure body env)
  (list body env))

(define (call-frame exp env rib stack)
  (list exp env rib stack))

(define stack (make-vector 1000))

(define (save-stack s)
  (let ([v (make-vector s)])
    (let copy ([i 0])
      (unless (= i s)
        (vector-set! v i (vector-ref stack i))
        (copy (+ i 1))))
    v))

(define (restore-stack v)
  (let ([s (vector-length v)])
    (let copy ([i 0])
      (unless (= i s)
        (vector-set! stack i (vector-ref v i))
        (copy (+ i 1))))
    s))

(define (continuation stack)
  (closure `(refer (0 . 0) (nuate ,(save-stack stack) (return)))
           '()))

(define trace-vm #f)

(define (VM a x e r s)
  (when trace-vm (display (format "> a: ~s, x: ~s, e: ~s, r: ~s, s: ~s\n" a x e r s)))
  (record-case x
    [(halt) () a]
    [(refer) (var x) (VM (car (lookup var e)) x e r s)]
    [(constant) (obj x) (VM obj x e r s)]
    [(close) (vars body x) (VM (closure body e) x e r s)]
    [(test) (then else) (VM a (if a then else) e r s)]
    [(assign) (var x)
     (set-car! (lookup var e) a)
     (VM a x e r s)]
    [(conti) (x)
     (VM (continuation s) x e r s)]
    [(nuate) (stack x)
     (VM a x e r (restore-stack stack))]
    [(frame) (ret x)
     (VM a x e '() (push ret (push e (push r s))))]
    [(argument) (x)
     (VM a x e (cons a r) s)]
    [(apply) ()
     (if (procedure? a)
         (VM (apply a r) '(return) e '() s)
         (record a (body env)
                 (VM a body (extend env r) '() s)))]
    [(return) ()
     (VM a (index s 0) (index s 1) (index s 2) (- s 3))]))

(set! trace-vm #t)

;;;
;;; Operations that are affected by the change of stack's implementation
;;;

;;; 1. pushes ret-e(x)pression & current env, and current rib into stack
;;;    - notice that here we pushed rib, and the stack-model one does not
;;; 2. (s)tack increases 3 because of the two pushes
(begin (set! stack (make-vector 4))
       (VM 24 '(frame '(constant 2 (halt)) (halt)) 'env 'rib 1)
       (display stack))

;;; 1. recovers ret-e(x)pression, (e)nvironment, and (r)ib from stack frame
;;; 2. pop up the frame via decreasing (s)tack pointer by 3
(begin (set! stack (make-vector 5))
       (vector-set! stack 3 '(constant 42 (halt)))
       (vector-set! stack 2 'new-env)
       (vector-set! stack 1 'rib)
       (VM 0 '(return) 'prev-env 'prev-rib 4)
       (display stack))

;;; - replace (a)ccumulator with a continuation closure
;;;   - closure-body: (refer 0 0 (nuate copied-stack (return)))
;;;     - here we do a full stack coping
;;;     - the refer 0 0 means that we retrieves the last rib value found in env
;;;       and puts it in (a)ccumulator before do resume continuation with nuate
;;;   - closure-env: empty
;;; - replace e(x)pression with conti-x and continue
(begin (set! stack (make-vector 5))
       (vector-set! stack 3 '(constant 42 (halt)))
       (vector-set! stack 2 'new-env)
       (vector-set! stack 1 'rib)
       (let ([ret (VM 0 '(conti (constant 42 (halt))) 'prev-env 'prev-rib 4)])
         (display stack)
         ret))

;;; - restore (s)tack with nuate-stack
;;; - replace e(x)pression with (return) and continue
(let ([v (make-vector 3)])
  (vector-set! v 2 '(constant 142 (halt)))
  (vector-set! v 1 '((42)))
  (vector-set! v 0 'rib)
  (set! stack (make-vector 10))
  ;; 1. refer updates (a)ccumulator from env
  ;; 2. nuate restores stack
  ;; 3. return pops up a frame from stack and execute return expression from the
  ;;    frame
  (let ([ret (VM 'prev-exp `(refer (0 . 0) (nuate ,v (return))) '((42)) 'prev-rib 'prev-stack)])
    (display stack)
    ret))

;;;
;;; Following operations are the same as Chapter 3.5 (heap-model-improving-variable-access.ss)
;;;

(VM 42 '(halt) 'env 'rib 'stack)
(VM #t '(test (constant 4 (halt)) (constant 2 (halt))) 'env 'rib 'stack)
(VM #f '(test (constant 4 (halt)) (constant 2 (halt))) 'env 'rib 'stack)
(VM 42 '(assign (0 . 0) (halt)) '((0 0)) 'rib 'stack)
(VM 'prev-exp '(refer (0 . 0) (halt)) '((42)) 'rib 'stack)
(VM 'prev-exp '(constant 10 (halt)) 'env 'rib 'stack)
(VM 'exp `(close (a) (refer (0 . 0) (halt)) (halt)) 'env 'rib 'stack)
(VM 'prev-exp '(argument (constant 42 (halt))) 'env '(43) 'stack)
(VM '((refer (0 . 0) (halt)) ())
    '(apply)
    'prev-env
    '(42)
    'stack)

;;; this examples need a frame setup because of the return instruction
(begin
  (set! stack (make-vector 3))
  (vector-set! stack 2 '(halt))
  (vector-set! stack 1 '((42)))
  (vector-set! stack 0 'rib)
  (let ([ret (VM + '(apply) '() '(42 1) 3)])
    (display stack)
    ret))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; eval

(set! stack (make-vector 1024))

(define (evaluate exp static-env env)
  (VM -1 (compile exp static-env '(halt)) env '() 0))

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
