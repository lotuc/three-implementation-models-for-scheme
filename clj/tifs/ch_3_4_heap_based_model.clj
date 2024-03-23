(ns tifs.ch-3-4-heap-based-model
  (:refer-clojure :exclude [test])
  (:require
   [hyperfiddle.rcf :as rcf]))

;;; `compile-expression`
;;; `VM`
;;; `evaluate`

(rcf/enable!)

(defn tail? [next-instruction]
  (= (first next-instruction) :return))

(defn compile-expression
  [x next-instruction]
  (cond
    (symbol? x) `(:refer ~x ~next-instruction)
    (not (list? x)) `(:constant ~x ~next-instruction)
    :else
    (let [[op & xs] x]
      (case op
        quote (let [[x] xs]
                `(:constant ~x ~next-instruction))
        lambda (let [[vars body] xs]
                 `(:close ~vars ~(compile-expression body '(:return)) ~next-instruction))
        if (let [[test then else] xs
                 thenc (compile-expression then next-instruction)
                 elsec (compile-expression else next-instruction)]
             (compile-expression test `(:test ~thenc ~elsec)))
        set! (let [[var x] xs]
               (compile-expression x `(:assign ~var ~next-instruction)))
        call/cc (let [[x] xs
                      c `(:conti (:argument ~(compile-expression x '(:apply))))]
                  (if (tail? next-instruction) c `(:frame ~next-instruction ~c)))
        (loop [args xs
               c (compile-expression op '(:apply))]
          (if (empty? args)
            (if (tail? next-instruction) c `(:frame ~next-instruction ~c))
            (recur (rest args) (compile-expression (first args) `(:argument ~c)))))))))

(rcf/tests
 (defn c [x] (compile-expression x '(:halt)))
 (c '42)                   := '(:constant 42 (:halt))
 (c 'a)                    := '(:refer a (:halt))
 (c '(quote 1))            := '(:constant 1 (:halt))
 (c '(lambda (x) x))       := '(:close (x) (:refer x (:return)) (:halt))
 (c '(set! x 1))           := '(:constant 1 (:assign x (:halt)))
 (c '(if true 42 24))      := '(:constant true (:test (:constant 42 (:halt)) (:constant 24 (:halt))))
 (c '(call/cc (lambda (k) 1))) := '(:frame (:halt) (:conti (:argument (:close (k) (:constant 1 (:return)) (:apply)))))
 (c '((lambda (x) x) 5))       := '(:frame (:halt) (:constant 5 (:argument (:close (x) (:refer x (:return)) (:apply)))))
 (c '((lambda (x) (inc x)) 5)) := '(:frame (:halt) (:constant 5 (:argument (:close (x) (:refer x (:argument (:refer inc (:apply)))) (:apply)))))
 (c '((lambda (x y) x) 4 2))   := '(:frame (:halt) (:constant 2 (:argument (:constant 4 (:argument (:close (x y) (:refer x (:return)) (:apply))))))))

(defn closure [body env vars] [body env vars])
(defn continuation [stack] (closure `(:nuate ~stack ~'v) '() '(v)))
(defn call-frame [exp env rib stack] [exp env rib stack])

(defn lookup [var [e0 & es]]
  (if-some [v (e0 var)]
    v
    (if (empty? es)
      (throw (Exception. (str "Unbound variable: " var)))
      (recur var es))))

(defn extend-environment [e vars rib]
  (cons (zipmap vars (map volatile! rib)) e))

(rcf/tests
 @(lookup 'a (-> '()
                 (extend-environment '(a) '(42)))) := 42
 @(lookup 'a (-> '()
                 (extend-environment '(a) '(42))
                 (extend-environment '(b) '(24)))) := 42
 @(lookup 'b (-> '()
                 (extend-environment '(a) '(42))
                 (extend-environment '(b) '(42)))) := 42)

(defn VM [a x e r s]
  (let [[op & xs] x]
    (case op
      :halt a
      :refer (let [[var x] xs]
               (recur @(lookup var e) x e r s))
      :constant (let [[obj x] xs]
                  (recur obj x e r s))
      :close (let [[vars body x] xs]
               (recur (closure body e vars) x e r s))
      :test (let [[then else] xs]
              (recur a (if a then else) e r s))
      :assign (let [[var x] xs]
                (vreset! (lookup var e) a)
                (recur a x e r s))
      :conti (let [[x] xs]
               (recur (continuation s) x e r s))
      :nuate (let [[stack var] xs]
               (recur @(lookup var e) '(:return) e r stack))
      :frame (let [[ret x] xs]
               (recur a x e '() (call-frame ret e r s)))
      :argument (let [[x] xs]
                  (recur a x e (cons a r) s))
      :apply (if (fn? a)
               (recur (apply a r) '(:return) e '() s)
               (let [[body env vars] a]
                 (recur a body (extend-environment env vars r) '() s)))
      :return (let [[x e r s] s]
                (recur a x e r s)))))

(rcf/tests
 (VM false '(:test (:constant 4 (:halt)) (:constant 2 (:halt))) 'env 'rib 'stack) := 2
 (VM 42 '(:assign a (:halt)) (extend-environment '() '(a b) `(0 0)) 'rib 'stack) := 42
 (VM 'prev-exp '(:refer a (:halt)) (extend-environment '() '(a) `(42)) 'rib 'stack) := 42
 (VM 'prev-exp '(:constant 10 (:halt)) 'env 'rib 'stack) := 10
 (VM 'exp `(:close (~'a) (:refer ~'a (:halt)) (:halt)) 'env 'rib 'stack) := '[(:refer a (:halt)) env (a)]
 (VM 'prev-exp '(:return) 'prev-env 'prev-rib '((:halt) env rib stack)) := 'prev-exp
 (VM 'prev-exp '(:nuate ((:constant 45 (:halt)) env rib stack) var) (extend-environment '() '(var) `(42)) 'prev-rib 'prev-stack) := 45
 (VM 'prev-exp '(:conti (:constant 42 (:halt))) 'prev-env 'prev-rib 'prev-stack) := 42
 (VM 'prev-exp '(:argument (:constant 42 (:halt))) 'env `(43) 'stack) := 42
 (VM '((:refer var (:halt)) () (var)) '(:apply) 'prev-env `(42) 'stack) := 42
 (VM + '(:apply) 'prev-env `(42 1) '((:halt) () () ())) := 43
 (VM 'prev-exp '(:frame (:halt) (:constant 42 (:halt))) 'env 'rib 'stack) := 42)

(defn evaluate [exp env]
  (VM -1 (compile-expression exp '(:halt)) env '() '()))

(def env (extend-environment
          nil
          '(= + - * / first rest empty?)
          (list = + - * / first rest empty?)))

(rcf/tests
 (evaluate '(= 1 1) env) := true
 (evaluate '((lambda [x y] (+ x y)) 4 2) env) := 6
 (evaluate '((lambda [x y] x) 4 2) env) := 4
 (evaluate '((lambda [x y] y) 4 2) env) := 2)

(rcf/tests
 (evaluate '((lambda
              (h)
              ((h (lambda
                   (fact)
                   (lambda
                    (n)
                    (if (= n 0)
                      1
                      (* n (fact (- n 1)))))))
               10))
             (lambda (h)
                     ((lambda (f) (f f))
                      (lambda (f) (h (lambda (n) ((f f) n)))))))
           env)
 := 3628800)

(rcf/tests
 (evaluate '((lambda
              (h)
              (((lambda
                 (lst)
                 (lambda
                  (n)
                  (call/cc
                   (lambda
                    (k)
                    (((h (lambda
                          (mul)
                          (lambda
                           (lst)
                           (lambda
                            (n)
                            (if (empty? lst)
                              n
                              (if (= 0 (first lst))
                                (k n)
                                ((mul (rest lst))
                                 (* n (first lst)))))))))
                      lst)
                     n)))))
                '(1 2 3 4 5 6 0 8 9))
               1))
             (lambda (h)
                     ((lambda (f) (f f))
                      (lambda (f) (h (lambda (n) ((f f) n)))))))
           env)
 := 720)
