;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; utility

(define-syntax record
  (lambda (x)
    (syntax-case x ()
      [(_ val (var ...) exp ...)
       #'(apply (lambda (var ...) exp ...) val)])))

(record '(1 2 39) (a b c) (+ a b c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; set operations
(define (set-member? x s)
  (cond [(null? s) #f]
        [(eq? x (car s)) #t]
        [else (set-member? x (cdr s))]))

(define (set-cons x s)
  (if (set-member? x s) s (cons x s)))

(define (set-union s1 s2)
  (if (null? s1) s2 (set-union (cdr s1) (set-cons (car s1) s2))))

(define (set-minus s1 s2)
  (if (null? s1)
      '()
      (if (set-member? (car s1) s2)
          (set-minus (cdr s1) s2)
          (cons (car s1) (set-minus (cdr s1) s2)))))

(define (set-intersect s1 s2)
  (if (null? s1)
      '()
      (if (set-member? (car s1) s2)
          (cons (car s1) (set-intersect (cdr s1) s2))
          (set-intersect (cdr s1) s2))))

(set-cons 'a '(b))
(set-cons 'a '(a b))
(set-union '(a b) '(a c))
(set-minus '(a b) '(a c))
(set-intersect '(a b) '(a c))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; find-free

(define (find-free x b)
  (cond
   [(symbol? x)
    (if (set-member? x b) '() (list x))]
   [(pair? x)
    (record-case x
      [(quote) (obj) '()]
      [(lambda) (vars body)
       (find-free body (set-union vars b))]
      [(if) (test then else)
       (set-union (find-free test b)
                  (set-union (find-free then b)
                             (find-free else b)))]
      [(call/cc) (exp)
       (find-free exp b)]
      [else
       (let next ([x x])
         (if (null? x)
             '()
             (set-union (find-free (car x) b)
                        (next (cdr x)))))])]
   [else '()]))

(find-free 'x '())
(find-free '(lambda (x) x) '())
(find-free '(lambda (x) (+ x y z)) '())
(find-free '(if x y z) '())
(find-free '(if x (lambda (y) x) (lambda (z) y)) '())
(find-free '(call/cc (lambda (k) (k x))) '())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; compile

(define (compile-lookup x e return-local return-free)
  (let nxtlocal ([locals (car e)] [n 0])
    (if (null? locals)
        (let nxtfree ([free (cdr e)] [n 0])
          (if (eq? (car free) x)
              (return-free n)
              (nxtfree (cdr free) (+ n 1))))
        (if (eq? (car locals) x)
            (return-local n)
            (nxtlocal (cdr locals) (+ n 1))))))

(define (compile-refer x e next)
  (compile-lookup x e
                  (lambda (n) `(refer-local ,n ,next))
                  (lambda (n) `(refer-free ,n ,next))))

(compile-refer 'a '((a b) . ()) '(halt))
(compile-refer 'b '((a b) . ()) '(halt))
(compile-refer 'a '((a b) . (a)) '(halt))
(compile-refer 'b '(() . (a b)) '(halt))

(define (collect-free vars e next)
  (if (null? vars)
      next
      (collect-free (cdr vars) e
                    (compile-refer (car vars) e `(argument ,next)))))

(collect-free '(a b) '((a c) . (g b)) '(halt))

(define trace-compile #t)

(define (compile x e next)
  (when trace-compile (display (format "compile: ~s ~s\n" x e)))
  (cond
   [(symbol? x)
    (compile-refer x e next)]
   [(pair? x)
    (record-case x
      [(quote) (obj)
       `(constant ,obj ,next)]
      [(lambda) (vars body)
       (let ([free (find-free body vars)])
         (collect-free free e
                       `(close ,(length free)
                               ,(compile body
                                         (cons vars free)
                                         `(return ,(length vars)))
                               ,next)))]
      [(if) (test then else)
       (let ([thenc (compile then e next)]
             [elsec (compile else e next)])
         (compile test e `(test ,thenc ,elsec)))]
      [(call/cc) (x)
       `(frame ,next (conti (argument ,(compile x e '(apply)))))]
      [else
       (let loop ([args (cdr x)]
                  [c (compile (car x) e '(apply))])
         (if (null? args)
             `(frame ,next ,c)
             (loop (cdr args)
                   (compile (car args) e `(argument ,c)))))])]
   [else `(constant ,x ,next)]))

(compile '(lambda (x) y) '(() . (y)) '(halt))
(compile '(lambda (y) (lambda (x) y)) '() '(halt))
(compile '(call/cc (lambda (k) 42)) '() '(halt))
(compile '(call/cc (lambda (k) (k 42))) '() '(halt))
(compile '((lambda (x) x) 42) '() '(halt))
(compile 'x '((x) . ()) '(halt))
(compile 'x '(() . (x)) '(halt))
(compile '(quote abc) '() '(halt))
(compile 123 '() '(halt))
(compile '(if #t 4 2) '() '(halt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; vm

(define (closure body n s)
  (let ([v (make-vector (+ n 1))])
    (vector-set! v 0 body)
    (let f ([i 0])
      (unless (= i n)
        (vector-set! v (+ i 1) (index s i))
        (f (+ i 1))))
    v))

(define (closure-body c)
  (vector-ref c 0))

(define (index-closure c n)
  (vector-ref c (+ n 1)))

(define (continuation stack)
  (closure `(refer-local 0 (nuate ,(save-stack stack) (return 0))) 0 '()))

(define trace-vm #f)

(define (VM a x f c s)
  (when trace-vm (display (format "> a: ~s, x: ~s, f: ~s, c: ~s, s: ~s\n" a x f c s)))
  (record-case x
    [(halt) () a]
    [(refer-local) (n x)
     (VM (index f n) x f c s)]
    [(refer-free) (n x)
     (VM (index-closure c n) x f c s)]
    [(constant) (obj x)
     (VM obj x f c s)]
    [(close) (n body x)
     (VM (closure body n s) x f c (- s n))]
    [(test) (then else)
     (VM a (if a then else) f c s)]
    [(conti) (x)
     (VM (continuation s) x f c s)]
    [(nuate) (stack x)
     (VM a x f c (restore-stack stack))]
    [(frame) (ret x)
     (VM a x f c (push ret (push f (push c s))))]
    [(argument) (x)
     (VM a x f c (push a s))]
    [(apply) ()
     (if (vector? a)
         ;; now closure is represented by vector
         (VM a (closure-body a) s a s)
         ;; handles scheme procedure application
         (record a (procedure arity)
                 (let loop ([arg-list '()] [c arity])
                   (if (zero? c)
                       (VM (apply procedure arg-list) `(return ,arity) s a s)
                       (loop (cons (index s (- c 1)) arg-list)
                             (- c 1))))))]
    [(return) (n)
     (let ([s (- s n)])
       (VM a (index s 0) (index s 1) (index s 2) (- s 3)))]))

(set! trace-vm #t)

(VM 'prev-exp '(halt) 'prev-f 'prev-c 'prev-s)
(VM 'prev-exp '(constant 42 (halt)) 'prev-f 'prev-c 'prev-s)
(VM #t '(test (constant 4 (halt)) (constant 2 (halt))) 'prev-f 'prev-c 'prev-s)
(VM #f '(test (constant 4 (halt)) (constant 2 (halt))) 'prev-f 'prev-c 'prev-s)

;;; refer-local
;;; - replace (a)ccumulator with call-(f)rame's nth value
;;; - replace e(x)pression with refer-local--x and continue
(begin (set! stack (make-vector 2))
       (vector-set! stack 1 42)
       (vector-set! stack 0 142)
       (VM 'prev-exp '(refer-local 0 (halt)) 2 'prev-c 'prev-s))

;;; refer-free
;;; - replace (a)ccumulator with (c)losure's nth value
;;; - replace e(x)pression with refer-free--x and continue
(begin (define c (make-vector 3))
       (vector-set! c 2 42)
       (vector-set! c 1 142)
       (vector-set! c 0 '(halt))
       (VM 'prev-exp '(refer-free 1 (halt)) 'prev-f c 'prev-s))

;;; close
;;; - replace (a)ccumulator with captured closure, now closure is a vector
;;;   - index-0: close-body
;;;   - index-1: top of stack, index-2: next value on stack ... (totally close-n values)
;;; - decrement (s)tack by close-n
;;; - replace e(x)pression with close-x and continue
(begin (set! stack (make-vector 4))
       (vector-set! stack 1 42)
       (vector-set! stack 0 142)
       (VM 'prev-exp '(close 2 (constant 4242 (halt)) (halt)) 'prev-f 'prev-c 2))

;;; frame
;;; - push (c)losure, call-(f)rame & frame-ret into stack
;;; - increments (s)tack by 3 (cause of the 3 pushed value)
;;; - replace (a)ccumulator with frame-x and continue
(begin (set! stack (make-vector 3))
       (let ([r (VM 'prev-exp '(frame (constant 10 (halt)) (halt)) 'prev-f 'prev-c 0)])
         (display stack)
         r))

;;; conti
;;; - captures continuation as a closure
;;;   - close-body: (refer-local 0 (nuate <saved-stack> (return 0)))
;;;   - close-n: 0
;;; - replace e(x)pression with conti-x and continue
(begin (set! stack (make-vector 1))
       (VM 'prev-exp '(conti (halt)) 'prev-f 'prev-c 1))

;;; nuate
;;; - restore stack & (s)tack pointer
;;; - replace e(x)pression with nuate-x and continue
(let ([s (make-vector 1)])
  (vector-set! s 0 42)
  (set! stack (make-vector 1))
  (let ([r (VM 'prev-exp `(nuate ,s (halt)) 'prev-f 'prev-c 3)])
    ;; recovered from s
    (display stack)
    r))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; eval

(set! stack (make-vector 1000))

(define (evaluate x static-envs)
  (let loop ([s 0]
             [vs (reverse (map cdr static-envs))])
    (if (null? vs)
        (VM '() (compile x `(,(map car static-envs)) '(halt)) s '() s)
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

(evaluate 42 scheme-static-envs)
(evaluate '42 scheme-static-envs)
(evaluate '(if #t 4 2) scheme-static-envs)
(evaluate '(if #f 4 2) scheme-static-envs)
(evaluate '((lambda (x) x) 42) scheme-static-envs)
(evaluate '(((lambda (x) (lambda (y) x)) 42) 24) scheme-static-envs)
(evaluate '(call/cc (lambda (k) 42)) scheme-static-envs)
(evaluate '(call/cc (lambda (k) (k 42))) scheme-static-envs)
(evaluate '(+ 4 2) scheme-static-envs)
(compile '(+ 1 2) '((+)) '(halt))

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
          scheme-static-envs)

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
          scheme-static-envs)
