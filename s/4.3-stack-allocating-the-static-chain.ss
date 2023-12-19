;;; Chapter 4.3.1 - Stack Allocating the Static Chain - Including Variable Values in the Call Frame
;;;
;;; Merging the stack-based model in 4.1 & the modified heap-based model in 4.2

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

(define (find-link n e)
  (if (= n 0)
      e
      (find-link (- n 1) (index e -1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; compile

(define trace-compile #t)

(define (compile x e next)
  (when trace-compile (display (format "compile: ~s ~s\n" x e)))
  (cond
   [(symbol? x)
    (compile-lookup
     x e (lambda (rib elt) `(refer ,rib, elt ,next)))]
   [(pair? x)
    (record-case x
      [(quote) (obj)
       `(constant ,obj ,next)]
      [(lambda) (vars body)
       `(close ,(compile body (extend e vars) `(return ,(+ (length vars) 1))) ,next)]
      [(if) (test then else)
       (let ([thenc (compile then e next)]
             [elsec (compile else e next)])
         (compile test e `(test ,thenc ,elsec)))]
      [(call/cc) (x)
       `(frame ,next (conti (argument ,(compile x e '(apply)))))]
      [else (let loop ([args (cdr x)]
                       [c (compile (car x) e '(apply))])
              (if (null? args)
                  `(frame ,next ,c)
                  (loop (cdr args)
                        (compile (car args) e `(argument ,c)))))])]
   [else `(constant ,x ,next)]))

(set! trace-compile #t)
(compile '42 '() '(halt))
(compile 'a '((a)) '(halt))
(compile '(quote 1) '() '(halt))
(compile '(lambda (x) x) '() '(halt))
(compile '(if #t 42 24) '() '(halt))
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
  (closure `(refer 0 0 (nuate ,(save-stack stack) (return 0))) '()))

(define trace-vm #f)

(define (VM a x e s)
  (when trace-vm (display (format "> a: ~s, x: ~s, e: ~s, s: ~s\n" a x e s)))
  (record-case x
    [(halt) () a]
    [(refer) (rib elt x)
     (VM (index (find-link rib e) elt) x e s)]
    [(constant) (obj x)
     (VM obj x e s)]
    [(close) (body x)
     (VM (closure body e) x e s)]
    [(test) (then else)
     (VM a (if a then else) e s)]
    [(conti) (x)
     (VM (continuation s) x e s)]
    [(nuate) (stack x)
     (VM a x e (restore-stack stack))]
    [(frame) (ret x)
     (VM a x e (push ret (push e s)))]
    [(argument) (x)
     (VM a x e (push a s))]
    [(apply) ()
     ;; represents scheme procedure with (<procedure> arity), it happens to be
     ;; the same structure as the closure (it doesn't need to be).
     (record a (body link)
             (if (procedure? body)
                 ;; handles scheme procedure application
                 (let loop ([arg-list '()] [c link])
                   (if (zero? c)
                       (VM (apply body arg-list) `(return ,link) e s)
                       (loop (cons (index s (- c 1)) arg-list)
                             (- c 1))))
                 ;; This is the actual closure-application
                 (VM a body s (push link s))))]
    [(return) (n)
     (let ([s (- s n)])
       (VM a (index s 0) (index s 1) (- s 2)))]))

(set! trace-vm #t)

(VM 42 '(halt) 'env 'stack)
(VM 'prev-exp '(constant 10 (halt)) 'env 'stack)
(VM #t '(test (constant 4 (halt)) (constant 2 (halt))) 'env 'stack)
(VM #f '(test (constant 4 (halt)) (constant 2 (halt))) 'env 'stack)

;;; close
;;; 1. replace (a)ccumulator with captured closure
;;;    - closure-body <- close-body
;;;    - closure-env <- current environmemt
;;; 2. replace e(x)pression with close-x and continue
(VM 'exp `(close (refer 0 0 (halt)) (halt)) 'env 'stack)

;;; argument
;;; 1. pushes (a)ccumulator's value into stack
;;; 2. increment (s)tack by 1
(begin (set! stack (make-vector 2))
       (let ([r (VM 'prev-exp '(argument (constant 42 (halt))) 'prev-env 1)])
         (display stack)
         r))

;;; refer
(begin (set! stack (make-vector 2))
       (vector-set! stack 1 14242)
       (VM 'prev-exp `(refer 0 0 (halt)) 2 2))

;;; frame
;;; 1. pushes ret-e(x)pression & current env into stack
;;; 2. (s)tack increases 2 because of the two pushes
;;; 3. replace (a)ccumulator with frame-x and continue
(begin (set! stack (make-vector 3))
       (let ([r (VM 24 '(frame (constant 2 (halt)) (halt)) 'env 1)])
         (display stack)
         r))

;;; return
;;; 1. recovers ret-e(x)pression, (e)nvironment, and (r)ib from stack frame
;;; 2. pop up the frame via decreasing (s)tack pointer by 2 + length of arguments
(begin (set! stack (make-vector 6))
       (vector-set! stack 4 'arg0)
       (vector-set! stack 3 'arg1)
       (vector-set! stack 2 '(constant 42 (halt)))
       (vector-set! stack 1 'new-env)
       (let ([r (VM 0 '(return 2) 'prev-env 5)])
         (display stack)
         r))

;;; conti
;;; - replace (a)ccumulator with a continuation closure
;;;   - closure-body: (refer 0 0 (nuate copied-stack (return 0)))
;;;     - here we do a full stack coping
;;;     - the refer 0 0 means we'll get value from top of env and puts it in
;;;       (a)ccumulator before do resume continuation with nuate
;;;   - closure-env: empty
;;; - replace e(x)pression with conti-x and continue
(begin (set! stack (make-vector 5))
       (vector-set! stack 3 '(constant 42 (halt)))
       (vector-set! stack 2 'new-env)
       (let ([ret (VM 0 '(conti (constant 42 (halt))) 'prev-env 4)])
         (display stack)
         ret))

;;; nuate
;;; - restore (s)tack with nuate-stack
;;; - replace e(x)pression with (return) and continue
(let ([v (make-vector 2)])
  (vector-set! v 1 '(constant 142 (halt)))
  (vector-set! v 0 '((42)))

  (set! stack (make-vector 10))
  (vector-set! stack 1 14242)
  ;; 1. refer updates (a)ccumulator from env
  ;; 2. nuate restores stack
  ;; 3. return pops up a frame from stack and execute return expression from the
  ;;    frame
  (let ([ret (VM 'prev-exp `(refer 0 0 (nuate ,v (return 0))) 2 2)])
    (display stack)
    ret))

;;; apply
(begin
  (set! stack (make-vector 6))

  ;; ----- frame 1 (2,3,4): s=5
  (vector-set! stack 4 'arg0)
  (vector-set! stack 3 '(halt))
  (vector-set! stack 2 3)
  ;; ---- frame 0 (0,1 - won't reach on this example)

  ;; here return 2: 1 pushed argument + 1 pushed closure-link value
  (let ([ret (VM '((refer 0 0 (return 2)) 3) '(apply) 'prev-env 5)])
    (display stack)
    ret))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; eval

(set! stack (make-vector 1024))

(define (evaluate exp static-envs)
  (let loop ([s 0]
             [vs (reverse (map cdr static-envs))])
    (if (null? vs)
        (VM -1 (compile exp `(,(map car static-envs)) '(halt)) s s)
        (loop (push (car vs) s) (cdr vs)))))

(define scheme-static-envs
  `((= . (,= 2))
    (+ . (,+ 2))
    (- . (,- 2))
    (* . (,* 2))
    (/ . (,/ 2))
    (car . (,car 1))
    (cdr . (,cdr 1))
    (null? . (,null? 1))))


(evaluate '(if #t 4 2) scheme-static-envs)
(evaluate '(if #f 4 2) scheme-static-envs)
(evaluate '((lambda (x) x) 42) scheme-static-envs)
(evaluate '((lambda (x y) y) 42 24) scheme-static-envs)
(evaluate '(+ 1 2) scheme-static-envs)

(evaluate '(call/cc (lambda (k) 10)) scheme-static-envs)
(evaluate '(call/cc (lambda (k) (k 10))) scheme-static-envs)
(evaluate '(call/cc (lambda (k) ((lambda (x) (k x)) 20))) scheme-static-envs)

(evaluate '(= 1 1) scheme-static-envs)
(evaluate '((lambda (x y) (+ x y)) 1 2) scheme-static-envs)
