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
; We can use the (*o X Y Z) relation either to multiply two numbers
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
; (e.g., if (*o X Y Z) holds then it is indeed X*Y=Z) but also
; complete (if X*Y=Z is true then (*o X Y Z) holds) and
; refutationally complete (if X*Y=Z is false then (*o X Y Z) fails,
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

(load "sempublic.scm")
(define errorf cout)

(define-syntax succ
  (syntax-rules ()
    [(_) succeed]
    [(_ e e* ...)
     (lambda@ (sk fk s)
       (begin
         e
         (@ (succ e* ...) sk fk s)))]))
       
(define-syntax fa
  (syntax-rules ()
    [(_) fail]
    [(_ e e* ...)
     (lambda@ (sk fk s)
       (begin
         e
         (@ (fa e* ...) sk fk s)))]))


(define build
  (lambda (n)
    (cond
      [(zero? n) '()]
      [else (cons (if (even? n) 0 1) (build (quotient n 2)))])))

(define trans
  (lambda (n)
    (cond
      [(null? n) 0]
      [else (+ (car n) (* 2 (trans (cdr n))))])))

; Not a zero
(define pos
  (lambda (n)
    (fresh (_ __)
      (== `(,_ . ,__) n))))

; At least two
(define gt1
  (lambda (n)
    (fresh (_ __)
      (== `(,_ . ,__) n)
      (pos __))))

(define comp-l
  (lambda (n m base-comp)
    (cond@
      [(== '() n) (base-comp m)]
      [else
        (fresh (x y _ __)
          (== `(,_ . ,x) n)
          (== `(,__ . ,y) m)
          (comp-l x y base-comp))])))

; Compare the length of two numerals.  (<ol a b) holds holds if a=0
; and b>0, or if (floor (log2 a)) < (floor (log2 b)) That is, we
; compare the length (logarithms) of two numerals For a positive
; numeral, its bitlength = (floor (log2 n)) + 1
    
(define <ol
  (lambda (n m)
    (comp-l n m pos)))


; holds if both a and b are zero
; or if (floor (log2 a)) = (floor (log2 b))
(define =ol
  (lambda (n m)
    (comp-l n m (lambda (m) (== '() m)))))

; full-adder: carry-in x y r c-out
; The relation holds if
; carry-in + x + y = r + 2*c-out
; where carry-in x y r c-out are all either 0 or 1.

(define no-carry-adder ;;; half-adder
  (lambda (x y r c-out)
    (cond@
      ((== 0 x) (== 0 y) (== 0 r) (== 0 c-out))
      ((== 0 x) (== 1 y) (== 1 r) (== 0 c-out))
      ((== 1 x) (== 0 y) (== 1 r) (== 0 c-out))
      ((== 1 x) (== 1 y) (== 0 r) (== 1 c-out))
      (else fail))))

(define carry-adder
  (lambda (x y r c-out)
    (cond@
      ((== 0 x) (== 0 y) (== 1 r) (== 0 c-out))
      ((== 0 x) (== 1 y) (== 0 r) (== 1 c-out))
      ((== 1 x) (== 0 y) (== 0 r) (== 1 c-out))
      ((== 1 x) (== 1 y) (== 1 r) (== 1 c-out))
      (else fail))))

(define full-adder
  (lambda (c-in x y r c-out)
    (cond@
      ((== 0 c-in) (no-carry-adder x y r c-out))
      ((== 1 c-in) (carry-adder x y r c-out))
      (else fail))))

; adder: c-in m n k
; holds if c-in + m + n = k
; where m, n, and k are binary numerals
; and c-in is either 0 or 1
(define adder*
  (lambda (c-in n m k)
    (cond@
      [(== '() n) (== '() m)
       (cond@
         [(== 0 c-in) (== '() k)]
         [(== 1 c-in) (== '(1) k)]
         [else fail])]            
      [(all (== '() n) (pos m))
       (cond@
         [(== 0 c-in) (== m k)]
         [(== 1 c-in) (adder* 0 '(1) m k)]
         [else fail])]
      [(all (== '() m) (pos n))
       (cond@
         [(== 0 c-in) (== n k)]
         [(== 1 c-in) (adder* 0 n '(1) k)]
         [else fail])]      
      [(ready-for-gen-adder n m) (gen-adder c-in n m k)]
      [else fail])))

;;; We can't invoke gen-adder, unless we know that n and m =/= '().
(define gen-adder
  (lambda (c-in n m k)
    (fresh (nb nr mb mr kb kr)
      (== `(,nb . ,nr) n)
      (== `(,mb . ,mr) m)
      (== `(,kb . ,kr) k)
      (fresh (c-out)
        (full-adder c-in nb mb kb c-out)
        (adder* c-out nr mr kr)))))

(define ready-for-gen-adder
  (lambda (n m)
    (condi
      ((== '(1) n) (== '(1) m))
      ((gt1 n) (== '(1) m))
      ((gt1 m) (== '(1) n))
      ((gt1 n) (gt1 m))
      (else fail))))


(define adder
  (lambda (c-in n m k)
    (cond@
      [(== '() n) (== '() m)
       (cond@
         [(== 0 c-in) (== '() k)]
         [(== 1 c-in) (== '(1) k)]
         [else fail])]            
      [(all (== '() n) (pos m))
       (cond@
         [(== 0 c-in) (== m k)]
         [(== 1 c-in) (adder 0 '(1) m k)]
         [else fail])]
      [(all (== '() m) (pos n))
       (cond@
         [(== 0 c-in) (== n k)]
         [(== 1 c-in) (adder 0 n '(1) k)]
         [else fail])]      
      [else
	(fresh (_)
	  (anyi
	; Note that we take advantage of the fact that if
	; a + b = r and length(b) <= length(a) then length(a) <= length(r)
	    (all (<ol n `(,_ . ,k))		; or, length(a) < length(2*r)
	      (any (<ol m n) (=ol m n))
	      (adder* c-in n m k)
	      )
	    ; commutative case, length(a) < length(b)
	    (all (<ol m `(,_ . ,k))
	      (<ol n m)
	      (adder* c-in n m k)
	      )
	    ))]
	)))



'(define gen-adder
  (lambda (c-in n m k)
    (fresh (nb nr mb mr kb kr)
      (== `(,nb . ,nr) n)
      (== `(,mb . ,mr) m)
      (== `(,kb . ,kr) k)
      (fresh (c-out)
        (full-adder c-in nb mb kb c-out)
        (adder c-out nr mr kr)))))


; a + b = c
(define +o
  (lambda (n m k)
    (adder 0 n m k)))

; a - b = c
(define -o
  (lambda (n m k)
    (+o m k n)))
    
; (<ol3 q p n m) holds iff
; q = '() and (pos p) or
; width(q) < width(p) <= width(n) + width(m)
; The way that n is counted down is subtle.  When
; it hits 0, m takes the role of n, since it may have some
; bits left.  When n and m are both 0, both cases fail.
; q and p are counted down naturally.
(define <ol3
  (lambda (q p n m)
    (cond@
      [(== q '()) (pos p)]
      [else
        (fresh (qr pr _ __)
          (== `(,_ . ,qr) q)
          (== `(,__ . ,pr) p)
          (condi
            [(fresh (mr _)
               (== '() n)
               (== `(,_ . ,mr) m) 
               (<ol3 qr pr mr '()))]
            [(fresh (nr _)
                (== `(,_ . ,nr) n) 
                (<ol3 qr pr nr m))]
            [else fail]))])))

; n * m = p

(define oddo
  (lambda (n)
    (fresh (_)
      (== `(1 . ,_) n))))

(define poseveno
  (lambda (n)
    (fresh (_)
      (== `(0 . ,_) n))))

(define *o
  (lambda (n m p)
    (condi
      [(== '() n) (== '() p)]		    ; 0 * m = 0
      [(== '() m) (pos n) (*o m n p)]
      [(== '(1) n) (pos m) (== m p)]    ; 1 * m = m
      ; n > 1, n is even, and m > 0 and n*m = p.
      ; <n/2> * m = (m*n)/2 = p/2
      [(gt1 n) (poseveno n) (pos m)
         (fresh (_ n/2 p/2)
           (== `(,_ . ,n/2) n)
	       (== `(0 . ,p/2) p)
	       (*o n/2 m p/2))]
      ; n > 1, n is odd, and m > 0 and n*m = p.
      ; (n-1)/2 * m = ((n * m) - m)/2 = (p - m)/2 = res
      ; so p - m = 2*res, and 2*res is represented as `(0 . ,res)
      ; A translation of Oleg's comments follows:
      ; (2 * (n-1)/2 + 1) * m = 2 * ((n-1)/2 * m) + m ; yes.
      ; m > 0; also (n-1)/2>0 for well-formedness
      ; the result is certainly greater than 1.
      ; We rely on the general fact that for a and b =/= 0,
      ; (floor (log2 (* a b))) + 1 <= (floor(log2(a)) + 1) + (floorlog2(b) + 1)
      ; Take for example: a = 7 and b = 31.  7 is 111, so (floor(log2(7)) + 1,
      ; since log2(7) is about 2.9, and its floor is 2, but we add one to make
      ; it 3. (count the number of bits) and 31 = 11111, so log2(31) is 4.9.
      ; its floor is 4, and we add one to make it 5.
      ; Its sum is 8.  If some of the 1's were replaced by 0, its total
      ; would still be 8, since we only want the number of bits.  Now,
      ; 7 * 31 is 217.  2^8 is 256, so 217 <= 256.  Thus we know that no
      ; number should be tried that makes the number have more than 8 bits.
      ; That''s all there is to why we use <ol3.  It keeps us from trying
      ; numbers that can't possibly be right.
      [(gt1 n) (oddo n) (pos m)
        (fresh (_ <n-1>/2 res)
	      (== `(,_ . ,<n-1>/2) n)
          (<ol3 res p n m) ;; This is the only upper bound
	      (*o <n-1>/2 m res)
	      (+o `(0 . ,res) m p))]
      [else fail])))

(define <o  ; n < m iff exists x > 0 such that n + x = m
  (lambda (n m)
    (fresh (x)
      (pos x)
      (+o n x m))))


; n = q*m + r where 0<=r<m
(define divo
  (lambda (n m q r)
    (condi
      [(== '() q) (<ol n m) (== r n) (<o n m)] 
                     ; m has more digits than n: q=0,n=r
      [(<ol m n) (<o r m)     ; n has more digits than m
		                      ; q is not zero, n>0, so q*m <= n,
       (fresh (res)           ; definitely q*m < 2*n
         (<ol res `(0 . ,n))
         (-o n res r)
         (*o q m res))]
          ; (width m) = (width n); r < m, q = 1.
      [(=ol m n) (<o r m) (== q '(1)) (-o n m r)]
          ; (width m) = (width n); n < m, q = 0, r = n
      [(== '() q) (=ol m n) (== r n) (<o n m)]
      [else fail])))

(display "addition")
(newline)
(test-check "addition"
  (run (q)
    (fresh (x)
      (+o (build 29) (build 3) x)
      (project (x) (== (trans x) q))))
  32)

(test-check "addition"
  (run (q)
    (fresh (x)
      (+o (build 3) x (build 29))
      (project (x) (== (trans x) q))))
  26)

(test-check "all numbers that sum to 4"
  (prefix 10
    (run-stream (w)
    (fresh (y z)
      (+o y z (build 4))
      (project (y z) (== `(,(trans y) ,(trans z)) w)))))
 '((0 4) (4 0) (3 1) (1 3) (2 2)))
 
;; 

(cout "Test recursive enumerability of addition" nl)
(let ((n 7))
  (do ((i 0 (+ 1 i))) ((> i n))
    (do ((j 0 (+ 1 j))) ((> j n))
      (let ((p (+ i j)))
	(test-check
	  (string-append "enumerability: " (number->string i)
	    "+" (number->string j) "=" (number->string p))
	  (run (q)
	    (fresh (x y z) 
	      (all (+o x y z)
		(== x (build i)) (== y (build j)) (== z (build p))
		(== q (list x y z)))))
	  `(,(build i) ,(build j) ,(build p)))))))


(test-check "print a few numbers such as X + 1 = Y"
  (prefix 5
    (run-stream (w)
      (fresh (x y)
        (+o x (build 1) y) (== `(,x ,y) w))))
      '((() (1))                       ; 0 + 1 = 1
        ((1) (0 1))                    ; 1 + 1 = 2
        ((0 _.0 . __.0) (1 _.0 . __.0)) ; 2*x 
                                            ; and 2*x+1 
                                            ; are successors, for all x>0!    
        ((1 1) (0 0 1))                     ; the successor of 3 is 4
        ((1 0 _.0 . __.0) (0 1 _.0 . __.0))))
                                            ; 1 added to an odd is an even.

(display "subtraction")
(newline)

(test-check "subtraction-1"
  (run (q)
    (fresh (x)
      (-o (build 29) (build 3) x)
      (project (x) (== (trans x) q))))
  26)

(test-check "subtraction-2"
  (run (q)
    (fresh (x)
      (-o (build 29) x (build 3))
      (project (x) (== (trans x) q))))
  26)

(test-check "subtraction-3"
  (run (q)
    (fresh (x)
      (-o x (build 3) (build 26))
      (project (x) (== (trans x) q))))
  29)

(test-check "subtraction-4"
  (run (q)
    (fresh (x)
      (-o (build 29) (build 29) x)
      (project (x) (== (trans x) q))))
  0)

(test-check "subtraction-5"
  (run (q)
    (fresh (x)
      (-o (build 29) (build 29) x)
      (project (x) (== (trans x) q))))
  0)

(test-check "subtraction-6"
  (run (q)
    (fresh (x)
      (-o (build 29) (build 30) x)
      (project (x) (== (trans x) q))))
  #f)

(test-check "print a few numbers such as y - z = 4"
  (prefix 5
    (run-stream (w)
      (fresh (x y)
        (-o x y (build 4))
        (== `(,x ,y) w))))
  '(((0 0 1) ())                        ; 4 - 0 = 4
    ((1 0 1) (1))                       ; 5 - 1 = 4
    ((0 1 1) (0 1))                     ; 6 - 2 = 4
    ((0 0 0 1) (0 0 1))                 ; 8 - 4 = 4
    ((0 0 1 _.0 . __.0) (0 0 0 _.0 . __.0))))
     ; 16*a + 8*b + 4 - (16*a + 8*b) = 4 forall a and b!!!  

(test-check "print a few numbers such as x - y = z"
  (prefix 15
    (run-stream (w)
      (fresh (x y z)
        (-o x y z)
        (== `(,x ,y ,z) w))))
  '((() () ())
    ((_.0 . __.0) () (_.0 . __.0))
    ((_.0 . __.0) (_.0 . __.0) ())
    ((0 1) (1) (1))
    ((1 _.0 . __.0) (0 _.0 . __.0) (1))
    ((0 0 1) (1 1) (1))
    ((0 1 _.0 . __.0) (1 0 _.0 . __.0) (1))
    ((0 0 0 1) (1 1 1) (1))
    ((0 0 1 _.0 . __.0) (1 1 0 _.0 . __.0) (1))
    ((0 0 0 0 1) (1 1 1 1) (1))
    ((0 0 0 1 _.0 . __.0) (1 1 1 0 _.0 . __.0) (1))
    ((0 0 0 0 0 1) (1 1 1 1 1) (1))
    ((0 0 0 0 1 _.0 . __.0) (1 1 1 1 0 _.0 . __.0) (1))
    ((0 0 0 0 0 0 1) (1 1 1 1 1 1) (1))
    ((0 0 0 0 0 1 _.0 . __.0) (1 1 1 1 1 0 _.0 . __.0) (1))))

(display "comparisons")
(newline)

(test-check "comparison-1"
  (run (q)
    (fresh (x)
      (<o x (build 4))
      (project (x) (== (trans x) q))))
  0)

(test-check "comparison-2"
  (run (q)
    (fresh (x)
      (== x (build 3))
      (<o x (build 4))
      (project (x) (== (trans x) q))))
  3)

(test-check "comparison-3"
  (run (q)
    (fresh (x)
      (== x (build 4))
      (<o x (build 3))
      (project (x) (== (trans x) q))))
  #f)

(test-check "print all numbers less than 6"
  (prefix 10 (run-stream (x) (<o x (build 6))))
  '(() (1 0 1) (1) (0 0 1) (0 1) (1 1)))

(test-check "print a few numbers that are greater than 4"
  (prefix 10 (run-stream (x) (<o (build 4) x)))
  '((1 0 1)
    (0 1 1)
	(0 0 0 1)
	(0 0 1 _.0 . __.0)
	(0 0 0 0 1)
	(0 0 0 1 _.0 . __.0)
	(0 0 0 0 0 1)
	(0 0 0 0 1 _.0 . __.0)
	(0 0 0 0 0 0 1)
	(0 0 0 0 0 1 _.0 . __.0)))

(display "multiplication")
(newline)

(display "Test recursive enumerability")
(newline)
(let ((n 7))
  (do ((i 0 (+ 1 i))) ((> i n))
    (do ((j 0 (+ 1 j))) ((> j n))
      (let ((p (* i j)))
	    (test-check
	      (string-append "enumerability: " (number->string i)
	        "*" (number->string j) "=" (number->string p))
	    (run (q) 
          (fresh (x y z) 
	        (*o x y z)
	        (== (build i) x)
            (== (build j) y)
            (== (build p) z)
            (== `(,x ,y ,z) q)))
	    `(,(build i) ,(build j) ,(build p)))))))

(test-check "multiplication-1"
  (run (q)
    (fresh (x)
      (*o (build 2) (build 3) x)
      (project (x) (== (trans x) q))))
  6)

(test-check "multiplication-2"
  (run (q)
    (fresh (x)
      (*o (build 3) x (build 12))
      (project (x) (== (trans x) q))))
  4)

(test-check "multiplication-3"
  (run (q)
    (fresh (x)
      (*o x (build 3) (build 12))
      (project (x) (== (trans x) q))))
  4)

(test-check "multiplication-4"
  (run (q)
    (fresh (x)
      (*o x (build 5) (build 12))))
  #f)

(test-check "multiplication-5"
  (run (q)
    (fresh (x)
      (== x (build 2))
      (*o x (build 2) (build 4))
      (project (x) (== (trans x) q))))
  2)

(test-check "multiplication-fail-1"
  (run (q)
    (fresh (x)
      (== x (build 3))
      (*o x (build 2) (build 4))
      (project (x) (== (trans x) q))))
  #f)

(test-check "multiplication-all-1"
  (prefix 10
    (run-stream (x)
      (fresh (y z)
        (*o y z (build 6))
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((1 6) (2 3) (3 2) (6 1)))

(test-check "multiplication-all-2"
  (prefix 10
    (run-stream (x)
      (fresh (y z)
        (*o y z (build 24))
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((1 24) (2 12) (3 8) (4 6) (6 4) (8 3) (12 2) (24 1)))

(test-check "multiplication-all-3"
  (prefix 7
    (run-stream (x)        
      (fresh (y z)
        (*o (build 3) y z)
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((0 0)
    (1 3)
    (2 6)
    (3 9)
    (4 12)
    (6 18)
    (5 15)))

(test-check "multiplication-all-4"
  (prefix 5
    (run-stream (x)        
      (fresh (y z)
        (*o y (build 3) z)
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((0 0) (1 3) (2 6) (3 9) (4 12)))

(test-check "multiplication-all-5"
  (prefix 7
    (run-stream (q)        
      (fresh (x y z)
        (*o x y z)
        (== `(,x ,y ,z) q))))
  '((() y.0 ())  ;; 0 * y = 0 for any y whatsoever
    ((_.0 . __.0) () ()) ;; x * 0 = 0 for all x (for x positive)
    ((1) (_.0 . __.0) (_.0 . __.0)) ;; 1 * x = x (for x positive)
    ((0 1) (_.0 . __.0) (0 _.0 . __.0))
    ((1 1) (1) (1 1))
    ((0 0 1) (_.0 . __.0) (0 0 _.0 . __.0))
    ((1 1) (0 1) (0 1 1))))

(test-check "multiplication-even-1"
  (prefix 5
    (run-stream (q)        
      (fresh (y z)
        (*o (build 2) y z)
        (== `(,y ,z) q))))
  '((() ())
    ; 2*y is an even number, for any y > 0!
    ((_.0 . __.0) (0 _.0 . __.0))))

(display "division, general")
(newline)

(test-check "division-1"
  (run (q)
    (fresh (x _)
      (divo (build 4) (build 2) x _)
      (project (x) (== (trans x) q))))
  2)

(test-check "division-fail-1"
  (run (q)
    (fresh (x _)
      (divo (build 4) (build 0) x _)
      (project (x) (== (trans x) q))))
  #f)

(test-check "division-2"
  (run (q)
    (fresh (x _)
      (all
        (divo (build 4) (build 3) x _)
        (project (x) (== (trans x) q)))))
  1)

(test-check "division-3"
  (run (q)
    (fresh (x _)
      (divo (build 4) (build 4) x _)
      (project (x) (== (trans x) q))))
  1)

(test-check "division-4"
  (run (q)
    (fresh (x _)
      (divo (build 4) (build 5) x _)
      (project (x) (== (trans x) q))))
  0)

(test-check "division-5"
  (run (q)
    (fresh (x _)
      (divo (build 33) (build 3) x _)
      (project (x) (== (trans x) q))))
  11)

(test-check "remainder-4"
  (run (q)
    (fresh (x _)
      (divo (build 4) (build 5) _ x)
      (project (x) (== (trans x) q))))
  4)

(test-check "division-5"
  (run (q)
    (fresh (x _)
      (divo (build 33) (build 3) x _)
      (project (x) (== (trans x) q))))
  11)

(test-check "division-6"
  (run (q)
    (fresh (x _)
      (divo (build 33) x (build 11) _)
      (project (x) (== (trans x) q))))
  3)

(test-check "division-7"
  (run (q)
    (fresh (x _)
      (divo x (build 3) (build 11) _)
      (project (x) (== (trans x) q))))
  33)

(test-check "division-8"
  (run (q)
    (fresh (x _)
      (divo x (build 5) _ (build 4))
      (project (x) (== (trans x) q))))
  9)

(test-check "division-9"
  (run (q)
    (fresh (x _)
      (divo x (build 5) (build 3) (build 4))
      (project (x) (== (trans x) q))))
  19)

(test-check "division-10"
  (run (q)
    (fresh (x _)
      (divo x _ (build 3) (build 4))
      (project (x) (== (trans x) q))))
  19)

(test-check "division-fail-2"
  (run (q)
    (fresh (x _)
      (divo (build 5) x (build 7) _)
      (project (x) (== (trans x) q))))
  #f)

(test-check "division-11"
  (run (q)
    (fresh (x _)
      (divo (build 33) (build 5) x _)
      (project (x) (== (trans x) q))))
  6)

(test-check "all numbers such as 5/Z = 1"
  (prefix 5
    (run-stream (q)        
      (fresh (z _)
        (divo (build 5) z (build 1) _)
        (project (z) (== (trans z) q)))))
  '(3 5 4))

(test-check "all inexact factorizations of 12"
  (prefix 100
    (run-stream (w)
      (fresh (m q r n)
        (== n (build 12))
        (<o m n)
        (divo n m q r)
        (project (m q r) (== `(,(trans m) ,(trans q) ,(trans r)) w)))))
  '((11 1 1)
    (1 12 0)
    (10 1 2)
    (2 6 0)
    (8 1 4)
	(4 3 0)
	(6 2 0)
	(9 1 3)
	(3 4 0)
	(5 2 2)
	(7 1 5)))

(test-check "div-all-3"
  (prefix 8
    (run-stream (w)
      (fresh (x y z r)
        (divo x y z r)
        (== `(,x ,y ,z ,r) w))))
  '((() (_.0 . __.0) () ())
    ((0 _.0) (_.0) (0 1) ())
	((1) (0 1) () (1))
	((__.0) (__.0) (1) ())
	((1) (1 _.0 . __.0) () (1))
	((1 1) (1) (1 1) ())
	((1) (0 0 1) () (1))
	((0 _.0) (1 _.0) () (0 _.0))))
  
(test-check "div-even"
  (prefix 4
    (run-stream (w)
      (fresh (y z r)
        (divo `(0 . ,y) (build 2) z r)
        (== `(,y ,z ,r) w))))
  '(((0 1) (0 1) ())
    ((1) (1) ())
    ((1 1) (1 1) ())
    ((0 0 1) (0 0 1) ())))



