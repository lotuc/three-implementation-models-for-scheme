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
      [(set!) (var x)
       (if (set-member? var b)
           (find-free x b)
           (set-cons var (find-free x b)))]
      [else
       (let next ([x x])
         (if (null? x)
             '()
             (set-union (find-free (car x) b)
                        (next (cdr x)))))])]
   [else '()]))

(find-free '(set! x 1) '())
(find-free '(set! x y) '())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; find-sets

(define (find-sets x v)
  (cond
   [(symbol? x) '()]
   [(pair? x)
    (record-case x
      [(quote) (obj)
       '()]
      [(lambda) (vars body)
       (find-sets body (set-minus v vars))]
      [(if) (test then else)
       (set-union (find-sets test v)
                  (set-union (find-sets then v)
                             (find-sets else v)))]
      [(set!) (var x)
       (set-union (if (set-member? var v) (list var) '())
                  (find-sets x v))]
      [(call/cc) (exp)
       (find-sets exp v)]
      [else
       (let next ([x x])
         (if (null? x)
             '()
             (set-union (find-sets (car x) v)
                        (next (cdr x)))))])]
   [else '()]))

(find-sets 'x '(x))
(find-sets '(set! x 1) '(x))
(find-sets '(lambda (x) (set! x 1)) '(x))
(find-sets '(lambda (y) (set! x 1)) '(x))

(define (make-boxes sets vars next)
  (let f ([vars vars] [n 0])
    (if (null? vars)
        next
        (if (set-member? (car vars) sets)
            `(box ,n ,(f (cdr vars) (+ n 1)))
            (f (cdr vars) (+ n 1))))))

(make-boxes '(x z) '(x y z) '(halt))

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

(define (compile x e s next)
  (cond
   [(symbol? x)
    (compile-refer x e
                   (if (set-member? x s)
                       `(indirect ,next)
                       next))]
   [(pair? x)
    (record-case x
      [(quote) (obj)
       `(constant ,obj ,next)]
      [(lambda) (vars body)
       (let ([free (find-free body vars)]
             [sets (find-sets body vars)])
         (collect-free free e
                       `(close ,(length free)
                               ,(make-boxes
                                 sets vars
                                 (compile body
                                          (cons vars free)
                                          (set-union sets (set-intersect s free))
                                          `(return ,(length vars))))
                               ,next)))]
      [(if) (test then else)
       (let ([thenc (compile then e s next)]
             [elsec (compile else e s next)])
         (compile test e s `(test ,thenc ,elsec)))]
      [(set!) (var x)
       (compile-lookup var e
                       (lambda (n)
                         (compile x e s `(assign-local ,n ,next)))
                       (lambda (n)
                         (compile x e s `(assign-free ,n ,next))))]
      [(call/cc) (x)
       `(frame ,next (conti (argument ,(compile x e s '(apply)))))]
      [else
       (let loop ([args (cdr x)]
                  [c (compile (car x) e s '(apply))])
         (if (null? args)
             `(frame ,next ,c)
             (loop (cdr args)
                   (compile (car args) e s `(argument ,c)))))])]
   [else
    `(constant ,x ,next)]))

;;; assign non-free variable
(compile '(lambda (x y) (set! x 10)) '((y) . ()) '() '(halt))
;;; assign free variable
(compile '(lambda (x) (set! y 10)) '(() . (y)) '() '(halt))
(compile '(lambda (x) (set! y 10)) '((y) . ()) '() '(halt))

;;; y is identified as boxed value & the reference becomes indirect
(compile '(lambda (y) ((lambda (x) y) (set! y 10))) '(() . ()) '() '(halt))

;;; assign
(compile '(set! x 10) '((x) . ()) '(x) '(halt))
(compile '(set! x 10) '(() . (x)) '(x) '(halt))

;;; refer - indirect
(compile 'a '((a) . ()) '(a) '(halt))
(compile 'a '(() . (a)) '(a) '(halt))
;;; refer - direct
(compile 'a '((a)) '() '(halt))
(compile 'a '(() . (a)) '() '(halt))

(compile ''a '() '() '(halt))

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
  (record-case x
    [(halt) () a]
    [(refer-local) (n x)
     (VM (index f n) x f c s)]
    [(refer-free) (n x)
     (VM (index-closure c n) x f c s)]
    [(indirect) (x)
     (VM (unbox a) x f c s)]
    [(constant) (obj x)
     (VM obj x f c s)]
    [(close) (n body x)
     (VM (closure body n s) x f c (- s n))]
    [(box) (n x)
     (index-set! s n (box (index s n)))
     (VM a x f c s)]
    [(test) (then else)
     (VM a (if a then else) f c s)]
    [(assign-local) (n x)
     (set-box! (index f n) a)
     (VM a x f c s)]
    [(assign-free) (n x)
     (set-box! (index-closure c n) a)
     (VM a x f c s)]
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
         ;; closure is represented by vector
         (VM a (closure-body a) s a s)
         (record a (procedure arity)
                 (let loop ([arg-list '()] [c arity])
                   (if (zero? c)
                       (VM (apply procedure arg-list) `(return ,arity) s a s)
                       (loop (cons (index s (- c 1)) arg-list)
                             (- c 1))))))]
    [(return) (n)
     (let ([s (- s n)])
       (VM a (index s 0) (index s 1) (index s 2) (- s 3)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; eval

(set! stack (make-vector 1000))

(define (evaluate x static-envs)
  (let loop ([s 0]
             [vs (reverse (map cdr static-envs))])
    (if (null? vs)
        (VM '() (compile x `(,(map car static-envs)) '() '(halt)) s '() s)
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

(evaluate '((lambda (y)
              ((lambda (x)
                 ((lambda (_) (+ x y))
                  (set! y 42)))
               y))
            24)
          scheme-static-envs)

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
