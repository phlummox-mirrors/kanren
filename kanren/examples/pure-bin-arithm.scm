;	     Pure, declarative, and constructive binary arithmetics
;
; aka: Addition, Multiplication, Division as always terminating,
; pure and declarative relations that can be used in any mode whatsoever.
; The relations define arithmetics over binary (base-2) integral numerals
; of arbitrary size.
;
; aka: division as relation.
; The function divo below is a KANREN relation between four binary numerals
; n, m, q, and r such that the following holds
;	exists r. 0<=r<m, n = q*m + r
;
; See pure-arithm.scm in this directory for Peano arithmetics.

; The arithmetic relations possess interesting properties.
; For example, given the relation (divo N M Q R) which holds
; iff N = M*Q + R and 0<=R<M, we can try:
;   -- (divo 1 0 Q _). It fails and does not try to enumerate
;      all natural numbers.
;   -- (divo 5 M 1 _). It finds all such M that divide (perhaps unevenly)
;      5 with the quotient of 1. The answer is the set (5 4 3).
; Again, (divo 5 M 7 _) simply fails and does not loop forever.
; We can use the (**o X Y Z) relation either to multiply two numbers
; X and Y -- or to find all factorizations of Z. See the test below.
; Furthermore, we can try to evaluate (++o X 1 Y) and get the stream
; of answers, among which is ((0 *anon.0 . *anon.1) (1 *anon.0 . *anon.1))
; which essentially says that 2*x and 2*x +1 are successors, for all x>0!
;
; Such relations are easy to implement in an impure system such as Prolog,
; with the help of a predicate 'var'. The latter can tell if its argument
; is an uninstantiated variable. However, 'var' is impure. The present
; file shows the implementation of arithmetic relations in a _pure_
; logic system.
;
; The present approach places the correct upper bounds on the
; generated numbers to make sure the search process will terminate.
; Therefore, our arithmetic relations are not only sound
; (e.g., if (**o X Y Z) holds then it is indeed X*Y=Z) but also
; complete (if X*Y=Z is true then (**o X Y Z) holds) and
; refutationally complete (if X*Y=Z is false then (**o X Y Z) fails,
; in finite time).
;
; The numerals are represented in the binary little-endian
; (least-significant bit first) notation. The higher-order bit must be 1.
; ()  represents 0
; (1) represents 1
; (0 1) represents 2
; (1 1) represents 3
; (0 0 1) represents 4
; etc.
;
; This code has been translated to Prolog. The Prolog version has
; termination proofs.
;
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

; Not a zero
(define pos
  (fact () `(,_ . ,_)))

; At least two
(define gt1
  (fact () `(,_ ,_ . ,_)))

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
    (relation (b)			; 0 + 0 + b = b
      (to-show 0 '() b b)
      (pos b))
    (relation (head-let '1 a '() r)	; 1 + a + 0 = 0 + a + 1
      (full-adder 0 a '(1) r))
    (relation (head-let '1 '() b r)	; 1 + 0 + b = 0 + 1 + b
      (all (pos b)
	(full-adder 0 '(1) b r)))

    ; The following three relations are needed
    ; to make all numbers well-formed by construction,
    ; that is, to make sure the higher-order bit is one.
    (relation (head-let carry-in '(1) '(1) r)	; c + 1 + 1 >= 2
      (exists (r1 r2)
	(all (== r `(,r1 ,r2))
	     (half-adder carry-in 1 1 r1 r2))))

    ; cin + 1 + (2*br + bb) = (2*rr + rb) where br > 0 and so is rr > 0
    (relation (carry-in bb br rb rr)
      (to-show carry-in '(1) `(,bb . ,br) `(,rb . ,rr))
      (all
	(pos br) (pos rr)
	(exists (carry-out)
	  (all
	    (half-adder carry-in 1 bb rb carry-out)
	    (full-adder carry-out '() br rr)))))

    ; symmetric case for the above
    (relation (head-let carry-in a '(1) r)
      (all
	(gt1 a) (gt1 r)
	(full-adder carry-in '(1) a r)))

    ; carry-in + (2*ar + ab) + (2*br + bb) 
    ; = (carry-in + ab + bb) (mod 2)
    ; + 2*(ar + br + (carry-in + ab + bb)/2)
    ; The cases of ar= 0 or br = 0 have already been handled.
    ; So, now we require ar >0 and br>0. That implies that rr>0.
    (relation (carry-in ab ar bb br rb rr)
      (to-show carry-in `(,ab . ,ar) `(,bb . ,br) `(,rb . ,rr))
      (all
	(pos ar) (pos br) (pos rr)
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
    (exists (x) (all (pos x) (++o n x m)))))

; compare the length of two numerals
; (<ol a b) holds 
; holds if a=0 and b>0, or if (floor (log2 a)) < (floor (log2 b))
; That is, we compare the length (logarithms) of two numerals
; For a positive numeral, its bitlength = (floor (log2 n)) + 1
(define <ol
  (extend-relation (n m)
    (fact () '() `(,_ . ,_))
    (relation (x y) (to-show `(,_ . ,x) `(,_ . ,y)) (<ol x y))))

; holds if both a and b are zero
; or if (floor (log2 a)) = (floor (log2 b))
(define =ol
  (extend-relation (n m)
    (fact () '() '())
    (relation (x y) (to-show `(,_ . ,x) `(,_ . ,y)) (=ol x y))))

; (<ol3 p1 p n m) holds iff
; p1 = 0 and p > 0 or
; length(p1) < length(p) <= length(n) + length(m)
(define <ol3
  (relation (head-let p1 p n m)
    (any
      (all (== p1 '()) (pos p))
      (exists (p1r pr)
	(all
	  (== p1 `(,_ . ,p1r))
	  (== p  `(,_ . ,pr))
	  (any
	    (exists (mr)
	      (all (== n '()) (== m  `(,_ . ,mr)) 
		(<ol3 p1r pr n mr)))
	    (exists (nr)
	      (all (== n  `(,_ . ,nr)) 
		(<ol3 p1r pr nr m)))
	    ))))))

; n * m = p
(define **o
  (relation (head-let n m p)
    (any
      (all (zeroo n) (== p '()))		; 0 * m = 0
      (all (zeroo m) (pos n) (== p '()))	; n * 0 = 0
      (all (== n '(1)) (pos m) (== m p))        ; 1 * m = m

      ; (2*nr) * m = 2*(nr*m), m>0 (the case of m=0 is taken care of already)
      ; nr > 0, otherwise the number is ill-formed
      (exists (nr pr)
	(all
	  (pos m)
	  (== n `(0 . ,nr))
	  (== p `(0 . ,pr))
	  (pos nr) (pos pr)
	  (**o nr m pr)))

      ; (2*nr+1) * m = 2*(n*m) + m
      ; m > 0; also nr>0 for well-formedness
      ; the result is certainly greater than 1.
      ; we note that m > 0 and so 2*(nr*m) < 2*(nr*m) + m
      ; and (floor (log2 (nr*m))) < (floor (log2 (2*(nr*m) + m)))
      (exists (nr p1)
	(all
	  (pos m)
	  (== n `(1 . ,nr))
	  (pos nr) (gt1 p)
	  (<ol3 p1 p n m)
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
      (all (== r n) (== q '()) (<ol n m) (<o n m)) ; m has more digits than n: q=0,n=r
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
(test-check "all numbers that sum to 4"
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
(test-check "print a few numbers such as X + 1 = Y"
  (solve 5 (x y) (++o x (build 1) y))
   '(((x.0 ()) (y.0 (1))) ; 0 + 1 = 1
     ((x.0 (1)) (y.0 (0 1))) ; 1 + 1 = 2
      ; 2*x and 2*x+1 are successors, for all x>0!
     ((x.0 (0 *anon.0 . *anon.1)) (y.0 (1 *anon.0 . *anon.1)))
     ((x.0 (1 1)) (y.0 (0 0 1)))
     ((x.0 (1 0 *anon.0 . *anon.1)) (y.0 (0 1 *anon.0 . *anon.1))))
  )

(cout nl "subtraction" nl)
(test (x) (--o (build 29) (build 3) x))
(test (x) (--o (build 29) x (build 3)))
(test (x) (--o x (build 3) (build 26)))
(test (x) (--o (build 29) (build 29) x))
(test (x) (--o (build 29) (build 30) x))
(test-check "print a few numbers such as Y - Z = 4"
  (solve 5 (y z) (--o y z (build 4)))
'(((y.0 (0 0 1)) (z.0 ()))  ; 4 - 0 = 4
 ((y.0 (1 0 1)) (z.0 (1)))  ; 5 - 1 = 4
 ((y.0 (0 1 1)) (z.0 (0 1))) ; 6 -2 = 4
 ((y.0 (0 0 0 1)) (z.0 (0 0 1))) ; 8 -4 = 4
 ((y.0 (0 0 1 *anon.0 . *anon.1)) ; 16*a + 8*b +4 - (16*a +8*b) = 4
  (z.0 (0 0 0 *anon.0 . *anon.1)))) ;forall a and b!!!
)

(test-check "print a few numbers such as X - Y = Z"
  (solve 5 (x y z) (--o x y z))
'(((x.0 y.0) (y.0 y.0) (z.0 ())) ; y - y = 0
  ((x.0 (*anon.0 . *anon.1)) (y.0 ()) (z.0 (*anon.0 . *anon.1)))
  ((x.0 (0 1)) (y.0 (1)) (z.0 (1)))
  ((x.0 (1 *anon.0 . *anon.1)) (y.0 (1)) (z.0 (0 *anon.0 . *anon.1)))
  ((x.0 (0 0 1)) (y.0 (1)) (z.0 (1 1))))
)


(cout nl "comparisons" nl)
(test (x) (<o x (build 4)))
(test (x) (all (== x (build 3)) (<o x (build 4))))
(test (x) (all (== x (build 4)) (<o x (build 3))))
(test-check "print all numbers hat are less than 6"
  (solve 10 (x) (<o x (build 6)))
'(((x.0 ())) ((x.0 (1))) ((x.0 (1 0 1))) ((x.0 (0 1)))
  ((x.0 (0 0 1))) ((x.0 (1 1))))
)

(test-check "print a few numbers that are greater than 4"
  (solve 3 (x) (<o (build 4) x))
'(((x.0 (1 0 1))) ((x.0 (0 1 1))) ((x.0 (0 0 0 1))))
)


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

; Only one answer
(test-check 'multiplication-all-2
  (solve 7 (w) 
    (exists (x)
      (all (**o (build 3) (build 2) x)
	(project (x) (== (trans x) w)))))
  '(((w.0 6))))

(test-check 'multiplication-all-3
  (solve 7 (y z) (**o (build 3) y z))
  '(((y.0 ()) (z.0 ())) ; 3 * 0 = 0
    ((y.0 (1)) (z.0 (1 1))) ; 3 * 1 = 3
    ((y.0 (0 1)) (z.0 (0 1 1))) ; 3 * 2 = 6
    ((y.0 (1 1)) (z.0 (1 0 0 1))) ; 3 * 3 = 9
    ((y.0 (0 0 1)) (z.0 (0 0 1 1))) ; 3 * 4 = 12
    ((y.0 (0 1 1)) (z.0 (0 1 0 0 1))) ; 3 * 6 = 18
    ((y.0 (1 0 1)) (z.0 (1 1 1 1))))  ; 3 * 5 = 15
)

(test-check 'multiplication-all-4
  (solve 4 (x z) (**o x (build 3) z))
  '(((x.0 ()) (z.0 ())) ((x.0 (1)) (z.0 (1 1)))
    ((x.0 (0 1)) (z.0 (0 1 1)))
    ((x.0 (0 0 1)) (z.0 (0 0 1 1))))
)

(test-check 'multiplication-all-5
  (solve 5 (x y z) (**o x y z))
  '(((x.0 ()) (y.0 y.0) (z.0 ())) ; 0 * y = 0 for any y whatsoever
    ((x.0 (*anon.0 . *anon.1)) (y.0 ()) (z.0 ())) ; x * 0 = 0 for x > 0
     ; 1 * y = y for y > 0
    ((x.0 (1)) (y.0 (*anon.0 . *anon.1)) (z.0 (*anon.0 . *anon.1)))
     ; 2 * y = even positive number, for y > 0
    ((x.0 (0 1)) (y.0 (*anon.0 . *anon.1)) (z.0 (0 *anon.0 . *anon.1)))
     ; 4 * y = double-even positive number, for y > 0
    ((x.0 (0 0 1)) (y.0 (*anon.0 . *anon.1)) (z.0 (0 0 *anon.0 . *anon.1)))
    )
)

(test-check 'multiplication-even-1
  (solve 5 (y z) (**o (build 2) y z))
  '(((y.0 ()) (z.0 ()))
     ; 2*y is an even number, for any y > 0!
    ((y.0 (*anon.0 . *anon.1)) (z.0 (0 *anon.0 . *anon.1))))
)

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

(test-check "all numbers such as 5/Z = 1"
  (solve 7 (w) 
    (exists (z) (all (divo (build 5) z (build 1) _)
		    (project (z) (== `(,(trans z)) w)))))
  '(((w.0 (3))) ((w.0 (5))) ((w.0 (4)))))

(test-check "all inexact factorizations of 12"
  (solve 100 (w) 
    (exists (m q r n)
      (all 
	(== n (build 12))
	(<o m n)
	(divo n m q r)
	(project (m q r) (== `(,(trans m) ,(trans q) ,(trans r)) w)))))
  '(((w.0 (1 12 0))) ((w.0 (11 1 1)))
    ((w.0 (2 6 0)))  ((w.0 (10 1 2)))
    ((w.0 (4 3 0)))  ((w.0 (8 1 4)))
    ((w.0 (6 2 0)))  ((w.0 (3 4 0)))
    ((w.0 (9 1 3)))  ((w.0 (7 1 5)))
    ((w.0 (5 2 2)))))


(test-check 'div-all-3
  (solve 3 (x y z r) (divo x y z r))
'(((x.0 ()) (y.0 (*anon.0 . *anon.1)) (z.0 ()) (r.0 ())) ; 0 = a*0 + 0, a>0
   ; There, anon.0 must be 1
  ((x.0 (0 *anon.0)) (y.0 (*anon.0)) (z.0 (0 1)) (r.0 ()))
  ; if z = 1, the two numbers must be equal -- but positive!
  ((x.0 (*anon.0)) (y.0 (*anon.0)) (z.0 (1)) (r.0 ()))
))

(test-check 'div-even
  (solve 3  (y z r) (divo `(0 . ,y) (build 2) z r))
  '(((y.0 (0 1)) (z.0 (0 1)) (r.0 ()))
    ((y.0 (1))   (z.0 (1)) (r.0 ()))
    ((y.0 (1 1)) (z.0 (1 1)) (r.0 ())))
)
