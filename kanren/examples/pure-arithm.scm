
(define (build n)
  (if (zero? n) '() (cons '() (build (- n 1)))))

(define trans length)

(define zeroo
  (fact () '()))

(define succo
  (extend-relation (a b)
    (fact () '() '(()))
    (fact (x) `(() . ,x) `(() () . ,x)))) 

(define at-least
  (extend-relation (a l)
    (fact () '() `(() . ,_))
    (relation (x l) (to-show `(() . ,x) `(() . ,l)) (at-least x l))))

(define succo-limit ; a+1 = b; b < l
  (extend-relation (a b l)
    (fact () '() '(()) `(() . ,_))
    (relation (x l)
      (to-show `(() . ,x) `(() () . ,x) `(() () . ,l))
      (at-least x l))))

(define ++o 
  (relation (head-let a b c)
    (any
      (all (zeroo b) (== a c))
      (all (zeroo a) (== b c))
      (exists (a1 c1) (all  (succo-limit a1 a c) (++o a1 b c1) (succo c1 c)))
      )))

(define --o
  (lambda (x y out)
    (++o y out x)))
      
(define <o  ; n < m iff n == (m-1) or n < (m-1)
  (relation (head-let n m)
    (exists (m1)
      (all (succo m1 m) (any (== n m1) (<o n m1))))))

(define <o at-least)

; 0 * m = 0
; n * 0 = 0
; (n+1)* m = n*m + m
(define **o
  (relation (head-let n m p)
    (any
      (all (zeroo n) (== p '()))
      (all (zeroo m) (== p '()))
      (all (succo '() n) (== m p))
      (all (succo '() m) (== n p))
      (exists (n1 p1)
	(all (succo-limit n1 n p) (**o n1 m p1) (++o p1 m p))))))

; n = q*m + r
; where 0<=r<m
(define //o
  (relation (head-let n m q)
    (exists (r p)
      (all (<o r m)  (++o p r n) (trace-vars 1 (p r n))
(**o q m p)))))


(define-syntax test
  (syntax-rules ()
    ((_ (x) ant)
      (query (redok subst x) ant
	(display (trans (subst-in x subst)))
	(newline)))))


(test (x) (++o (build 29) (build 3) x))
(test (x) (++o (build 3) x (build 29)))
(test (x) (++o x (build 3) (build 29)))

(test (x) (--o (build 29) (build 3) x))
(test (x) (--o (build 29) x (build 3)))
(test (x) (--o x (build 3) (build 26)))
(test (x) (--o (build 29) (build 29) x))
(test (x) (--o (build 29) (build 30) x))

(test (x) (<o x (build 4)))
(test (x) (all (== x (build 3)) (<o x (build 4))))
(test (x) (all (== x (build 4)) (<o x (build 3))))
(solve 5 (x) (<o x (build 3)))

(test (x) (**o (build 2) (build 3) x))
(test (x) (**o (build 3) x (build 12)))
(test (x) (**o x (build 3) (build 12)))
(test (x) (**o x (build 5) (build 12)))
(test (x) (all (== x (build 2)) (**o x (build 2) (build 4))))
(test (x) (all (== x (build 3)) (**o x (build 2) (build 4))))

(test (x) (//o (build 4) (build 2) x))
(test (x) (//o (build 4) (build 0) x))
(test (x) (//o (build 4) (build 3) x))
(test (x) (//o (build 4) (build 4) x))
(test (x) (//o (build 4) (build 5) x))

(test (x) (//o (build 33) (build 3) x))
(test (x) (//o (build 33) x (build 11)))
(test (x) (//o x (build 3) (build 11)))

; the following take a long time
;(test (x) (//o (build 33) (build 5) x))
;(test (x) (//o (build 29) (build 3) x))

