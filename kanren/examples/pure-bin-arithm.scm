;	     Pure, declarative, and constructive binary arithmetics
;
; aka: division as relation.
; The function divo below is a KANREN relation between four binary numerals
; n, m, q, and r such that the following holds
;	exists r. 0<=r<m, n = q*m + r
;
; See pure-arithm.scm in this directory for Peano arithmetics.

; That relation is more remarkable than it may look. First, it's possible to
; ask (divo 1 0 q _). Obviously, such q does not exist. The relation
; thus fail -- it does not try to enumerate all natural numbers.
; We can also invoke it like (divo 5 m 1 _), where m is a free
; variable. The answers are (5 4 3).
; Again, (divo 5 m 7 _) simply fails and does not loop forever.
; We can even try (divo x y z r), which returns a stream of triples
; among which is
;  ((x.0 (0 *anon.0)) (y.0 (*anon.0)) (z.0 (0 1)) (r.0 ()))
; which says that any even number is evenly divisible by two!
; This is a consequence of our implementation of divo, we did not
; put that rule explicitly!
; We can derive algebraic equalities!
;
; Such relations are easy to implement in an impure system such as Prolog,
; with the help of a predicate 'var'. The latter can tell if its argument
; is an uninstantiated variable. However, 'var' is impure. The present
; file shows the implementation of arithmetic relations in a _pure_
; logic system.
; 
; Furthermore, by judicially setting sound boundaries, we make the system
; constructive. So, our arithmetic relations are not only pure
; and sound but also complete.
;
; The numerals are represented in the binary little-endian
; (least-significant bit first) notation. The higher-order bit must be 1.
; ()  represents 0
; (1) represents 1
; (0 1) represents 2
; (1 1) represents 3
; (0 0 1) represents 4
; etc.

; $Id$

; Auxiliary functions to build and show binary numerals
;
(define (build n)
  (if (zero? n) '() (cons (if (even? n) 0 1) (build (quotient n 2)))))

(define (trans n)
  (if (null? n) 0 (+ (car n) (* 2 (trans (cdr n))))))


; (zeroo x) holds if x is zero numeral
(define zeroo
  (fact () '()))

(define a-positive-number `(,_ . ,_))

; Half-adder: carry-in a b r carry-out
; The relation holds if
; carry-in + a + b = r + 2*carry-out
; where carry-in a b r carry-out are all either 0 or 1.

(define half-adder
  (extend-relation (carry-in a b r carry-out)
    (fact () 0 0 0 0 0)
    (fact () 0 1 0 1 0)
    (fact () 0 0 1 1 0)
    (fact () 0 1 1 0 1)

    (fact () 1 0 0 1 0)
    (fact () 1 1 0 0 1)
    (fact () 1 0 1 0 1)
    (fact () 1 1 1 1 1)
))

; full-adder: carry-in a b r
; holds if carry-in + a + b = r
; where a, b, and r are binary numerals and carry-in is either 0 or 1

(define full-adder
  (extend-relation (carry-in a b r)
    (fact (a) 0 a '() a) 		; 0 + a + 0 = a
    (fact (b) 0 '() b b) 		; 0 + 0 + b = b
    (relation (head-let '1 a '() r)	; 1 + a + 0 = 0 + a + 1
      (full-adder 0 a '(1) r))
    (relation (head-let '1 '() b r)	; 1 + 0 + b = 0 + 1 + b
      (full-adder 0 '(1) b r))

    ; The following three relations are needed
    ; to make all numbers well-formed by construction,
    ; that is, to make sure the higher-order bit is one.
    (relation (head-let carry-in '(1) '(1) r)	; c + 1 + 1 >= 2
      (exists (r1 r2)
	(all (== r `(,r1 ,r2))
	     (half-adder carry-in 1 1 r1 r2))))

    ; 1 + 1 + (2*br + bb) = (2*rr + rb) where br > 0 and so is rr > 0
    (relation (carry-in bb br rb rr)
      (to-show carry-in '(1) `(,bb . ,br) `(,rb . ,rr))
      (all
	(== br `(,_ . ,_))		; br > 0
	(== rr `(,_ . ,_))
	(exists (carry-out)
	  (all
	    (half-adder carry-in 1 bb rb carry-out)
	    (full-adder carry-out '() br rr)))))

    ; symmetric case for the above
    (relation (head-let carry-in a '(1) r)
      (all
	(== a `(,_ ,_ . ,_))
	(== r `(,_ ,_ . ,_))
	(full-adder carry-in '(1) a r)))

    ; carry-in + (2*ar + ab) + (2*br + bb) 
    ; = (carry-in + ab + bb) (mod 2)
    ; + 2*(ar + br + (carry-in + ab + bb)/2)
    ; Also, if ar>0 and br>0 and so rr > 0
    (relation (carry-in ab ar bb br rb rr)
      (to-show carry-in `(,ab . ,ar) `(,bb . ,br) `(,rb . ,rr))
      (all
	(== ar `(,_ . ,_))
	(== br `(,_ . ,_))
	(== rr `(,_ . ,_))
	(exists (carry-out)
	  (all
	    (half-adder carry-in ab bb rb carry-out)
	    (full-adder carry-out ar br rr))))
    )))

; a + b = c
(define ++o
  (relation (head-let a b c)
    (full-adder 0 a b c)))

; a - b = c
(define --o
  (lambda (x y out)
    (++o y out x)))

 
(define <o  ; n < m iff exists x >0 such that n + x = m
  (relation (head-let n m)
    (++o a-positive-number n m)))

; compare the length of two numerals
; (<ol a b) holds if (floor (log2 a)) < (floor (log2 b))
(define <ol
  (extend-relation (n m)
    (fact () '() `(,_ . ,_))
    (relation (x y) (to-show `(,_ . ,x) `(,_ . ,y)) (<ol x y))))

(define =ol
  (extend-relation (n m)
    (fact () '() '())
    (relation (x y) (to-show `(,_ . ,x) `(,_ . ,y)) (=ol x y))))

; n * m = p
(define **o
  (relation (head-let n m p)
    (any
      (all (zeroo n) (== p '()))	; 0 * m = 0
      (all (zeroo m) (== p '()))	; n * 0 = 0
      (all (== n '(1)) (== m p))        ; 1 * m = m
      ; (2*n) * m = 2*(n*m)
      (exists (nr pr)
	(all
	  (== n `(0 . ,nr))
	  (== p `(0 . ,pr))
	  (== nr `(,_ . ,_))
	  (== pr `(,_ . ,_))
	  (**o nr m pr)))
      ; (2*n+1) * m = 2*(n*m) + m
      ; we note that m > 0 and so 2*(n*m) < 2*(n*m) + m
      ; and (floor (log2 (n*m))) < (floor (log2 (2*(n*m) + m)))
      (exists (nr p1)
	(all
	  (== n `(1 . ,nr))
	  (== nr `(,_ . ,_))
	  (== p `(,_ ,_ . ,_))
	  (<ol p1 p)
	  (**o nr m p1)
	  (++o `(0 . ,p1) m p)))
)))

; n = q*m + r
; where 0<=r<m

; This is divo from pure-arithm.scm
; it still works -- but very slow for some operations
; because <o takes linear time...
(define divo
  (relation (head-let n m q r)
    (any-interleave
      (all (== q '()) (== r n) (<o n m))      ; if n < m, then q=0, n=r
      (all (== n m) (== q '(1)) (== r '()))  ; n = 1*n + 0
      (exists (p)
	(all (<o m n) (<o r m)  (++o p r n) ;(trace-vars 1 (p r n))
	  (**o q m p))))))

; A faster divo algorithm
(define divo
  (relation (head-let n m q r)
    (any-interleave
      (all (== r n) (== q '()) (<ol n m)) ; m has more digits than n: q=0,n=r
      (all
	(<ol m n)			; n has mode digits than m
					; q is not zero, n>0, so q*m <= n,
	(exists (p)			; definitely q*m < 2*n
	  (all (<o r m) (<ol p `(0 . ,n))
	    (++o p r n) ;(trace-vars 1 (p r n))
	    (**o q m p)))
	)
      ; n has the same number of digits than m
      (all (== q '(1)) (=ol n m) (++o r m n) (<o r m))
      (all (== q '()) (== r n) (=ol n m) (<o n m))  ; if n < m, then q=0, n=r
      )))
; 	(any-interleave
; 	  (all (== m '(1)) (== r '()) (== n q)) ; n = n*1 + 0
; 	  ; For even divisors:
; 	  ; n = (2*m)*q + r => (n - r) is even and (n-r)/2 = m*q
; 	  (exists (p m1)
; 	    (all (== m `(0 . ,m1))
; 	         (== m1 `(_, . ,_))
; 	         (**o m1 q p)
; 	         (--o n r `(0 . ,p))))


(define-syntax test
  (syntax-rules ()
    ((_ (x) ant)
      (query (redok subst x) ant
	(display (trans (subst-in x subst)))
	(newline)))))

(cout nl "addition" nl)
(test (x) (++o (build 29) (build 3) x))
(test (x) (++o (build 3) x (build 29)))
(test (x) (++o x (build 3) (build 29)))
(test-check 'addition-all-1
  (solve 10 (w)
    (exists (y z)
      (all (++o y z (build 4))
	(project (y z) (== `(,(trans y) ,(trans z)) w)))))
   '(((w.0 (4 0)))
     ((w.0 (0 4)))
     ((w.0 (1 3)))
     ((w.0 (3 1)))
     ((w.0 (2 2)))
     )
  )

(cout nl "subtraction" nl)
(test (x) (--o (build 29) (build 3) x))
(test (x) (--o (build 29) x (build 3)))
(test (x) (--o x (build 3) (build 26)))
(test (x) (--o (build 29) (build 29) x))
(test (x) (--o (build 29) (build 30) x))
(test-check 'subtraction-all-1
  (solve 5 (y z) (--o y z (build 4)))
'(((y.0 (0 0 1)) (z.0 ()))  ; 4 - 0 = 4
 ((y.0 (1 0 1)) (z.0 (1)))  ; 5 - 1 = 4
 ((y.0 (0 1 1)) (z.0 (0 1))) ; 6 -2 = 4
 ((y.0 (0 0 0 1)) (z.0 (0 0 1))) ; 8 -4 = 4
 ((y.0 (0 0 1 *anon.0 . *anon.1)) ; 16*a + 8*b +4 - (16*a +8*b) = 4
  (z.0 (0 0 0 *anon.0 . *anon.1)))) ;forall a and b!!!
)

(cout nl "comparisons" nl)
(test (x) (<o x (build 4)))
(test (x) (all (== x (build 3)) (<o x (build 4))))
(test (x) (all (== x (build 4)) (<o x (build 3))))
(cout (solve 5 (x) (<o x (build 3))) nl)


(cout nl "multiplication" nl)
(test (x) (**o (build 2) (build 3) x))
(test (x) (**o (build 3) x (build 12)))
(test (x) (**o x (build 3) (build 12)))
(test (x) (**o x (build 5) (build 12)))
(test (x) (all (== x (build 2)) (**o x (build 2) (build 4))))
(test-check 'multiplication-fail-1
  (test (x) (all (== x (build 3)) (**o x (build 2) (build 4))))
  '())
(test-check 'multiplication-all-1
  (solve 7 (w) 
    (exists (y z) (all (**o y z (build 6))
		    (project (y z) (== `(,(trans y) ,(trans z)) w)))))
  '(((w.0 (1 6))) ((w.0 (2 3))) ((w.0 (6 1)))  ((w.0 (3 2)))))

(cout nl "division, general" nl)

(test (x) (divo (build 4) (build 2) x _))
(test-check 'div-fail-1 (test (x) (divo (build 4) (build 0) x _)) '())
(test (x) (divo (build 4) (build 3) x _))
(test (x) (divo (build 4) (build 4) x _))
(test (x) (divo (build 4) (build 5) x _))
(test (x) (divo (build 4) (build 5) _ x))

(test (x) (divo (build 33) (build 3) x _))
(test (x) (divo (build 33) x (build 11) _))
(test (x) (divo x (build 3) (build 11) _))

(test (x) (divo x (build 5) _ (build 4)))
(test (x) (divo x (build 5) (build 3) (build 4)))
(test (x) (divo x _ (build 3) (build 4)))
(test-check 'div-fail-2 (test (x) (divo (build 5) x (build 7) _)) '())

(test (x) (divo (build 33) (build 5) x _))

(test-check 'div-all-2
  (solve 7 (w) 
    (exists (z) (all (divo (build 5) z (build 1) _)
		    (project (z) (== `(,(trans z)) w)))))
  '(((w.0 (3))) ((w.0 (5))) ((w.0 (4)))))

(test-check 'div-all-3
  (solve 3 (x y z r) (divo x y z r))
'(((x.0 ()) (y.0 (*anon.0 . *anon.1)) (z.0 ()) (r.0 ())) ; 0 = a*0 + 0, a>0
   ; the following says that any even number is evenly divisible by two!
  ((x.0 (0 *anon.0)) (y.0 (*anon.0)) (z.0 (0 1)) (r.0 ()))
  ; if z = 1, the two numbers must be equal -- but positive!
  ((x.0 (*anon.0)) (y.0 (*anon.0)) (z.0 (1)) (r.0 ()))
))

