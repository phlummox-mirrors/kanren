;; http://www.sics.se/quintus/crypt.pl
; crypt
;
; Cryptomultiplication:
; Find the unique answer to:
;	OEE
;	 EE
; 	---
;      EOEE
;      EOE
;      ----
;      OOEE
;
; where E=even, O=odd.
; This program generalizes easily
; to any such problem.
; Written by Peter Van Roy

(define crypt
  (relation (a b c d e f g h i j k l m n o p)
    (to-show `(,a ,b ,c ,d ,e ,f ,g ,h ,i ,j ,k ,l ,m ,n ,o ,p))
    (all!
      (odd a)
      (even b)
      (even c)
      (even e)
      (exists (x)
	(all!!
	  (mult `(,c ,b ,a) e `(,i ,h ,g ,f . ,x))
	  (lefteven f)
	  (odd g)
	  (even h)
	  (even i)
	  (zero x)))
      (lefteven d)
      (exists (y)
	(all!!
	  (mult `(,c ,b ,a) d `(,l ,k ,j . ,y))
	  (lefteven j)
	  (odd k)
	  (even l)
	  (zero y)))
      (exists (z)
	(all!!
	  (sum `(,i ,h ,g ,f) `(0 ,l ,k ,j) `(,p ,o ,n ,m . ,z))
	  (odd m)
	  (odd n)
	  (even o)
	  (even p)
	  (zero z))))))
      
(define sum
  (relation (head-let al bl cl)
    (sum4 al bl 0 cl)))

(define sum4
  (extend-relation (a1 a2 a3 a4)
    (relation (a al b bl carry c cl)
      (to-show `(,a . ,al) `(,b . ,bl) carry `(,c . ,cl))
      (project (a b carry)
	(exists (x)
	  (all!!
	    (== x (+ a b carry))
	    (project (x)
	      (all!!
		(== c (modulo x 10))
		(exists (newcarry)
		  (all!!
		    (== newcarry (quotient x 10))
		    (sum4 al bl newcarry cl)))))))))
    (fact (bl) '() bl 0 bl)
    (fact (al) al '() 0 al)
    (relation (b bl carry c cl)
      (to-show '() `(,b . ,bl) carry `(,c . ,cl))
      (project (b carry)
	(exists (x)
	  (all!!
	    (== x (+ b carry))
	    (project (x)
	      (exists (newcarry)
		(all!!
		  (== newcarry (quotient x 10))
		  (== c (modulo x 10))
		  (sum4 '() bl newcarry cl))))))))
    (relation (a al carry c cl)
      (to-show `(,a . ,al) '() carry `(,c . ,cl))
      (project (a carry)
	(exists (x)
	  (all!!
	    (== x (+ a carry))
	    (project (x)
	      (exists (newcarry)
		(all!!
		  (== newcarry (quotient x 10))
		  (== c (modulo x 10))
		  (sum4 '() al newcarry cl))))))))
    (fact (carry) '() '() carry `(,carry))))

(define mult
  (relation (head-let al d bl)
    (mult4 al d 0 bl)))

(define mult4
  (extend-relation (a1 a2 a3 a4)
    (relation (carry c cend)
      (to-show '() _ carry `(,c ,cend))
      (project (carry)
	(all!!
	  (== c (modulo carry 10))
	  (== cend (quotient carry 10)))))
    (relation (a al d carry b bl)
      (to-show `(,a . ,al) d carry `(,b . ,bl))
      (project (a d carry)
	(exists (x)
	  (all!!
	    (== x (+ (* a d) carry))
	    (project (x)
	      (all!!
		(== b (modulo x 10))
		(exists (newcarry)
		  (all!!
		    (== newcarry (quotient x 10))
		    (mult4 al d newcarry bl)))))))))))

(define zero
  (extend-relation (a1)
    (fact () '())
    (relation (l)
      (to-show `(0 . ,l))
      (zero l))))

(define odd
  (extend-relation (a1)
    (fact () 1)
    (fact () 3)
    (fact () 5)
    (fact () 7)
    (fact () 9)))

; odd(1).
; odd(3).
; odd(5).
; odd(7).
; odd(9).

(define even
  (extend-relation (a1)
    (fact () 0)
    (fact () 2)
    (fact () 4)
    (fact () 6)
    (fact () 8)))

; even(0).
; even(2).
; even(4).
; even(6).
; even(8).

(define lefteven
  (extend-relation (a1)
    (fact () 2)
    (fact () 4)
    (fact () 6)
    (fact () 8)))

; lefteven(2).
; lefteven(4).
; lefteven(6).
; lefteven(8).

(define crypt-test
  (lambda ()
    (solution (a b c d e f g h i j k l m n o p)
      (crypt `(,a ,b ,c ,d ,e ,f ,g ,h ,i ,j ,k ,l ,m ,n ,o ,p)))))

(write (crypt-test))
(newline)

(define benchmark_count 100)

(display "Timing per iterations: ") (display benchmark_count) (newline)
(time (do ((i 0 (+ 1 i))) ((>= i benchmark_count))
      (crypt-test)))


