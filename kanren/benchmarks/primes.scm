;; http://www.sics.se/quintus/primes.pl

; $Id$

(define primes
  (relation (head-let limit ps)
    (exists (ls)
      (all
	(integers 2 limit ls)
	(sift ls ps)))))

(define integers
  (extend-relation (a1 a2 a3)
    (relation (low high rest)
      (to-show low high `(,low . ,rest))
      (all!!
	(predicate (low high)
	  (<= low high))
	(exists (m)
	  (all!!
	    (project (low)
	      (== m (+ low 1)))
	    (integers m high rest)))))
    (fact () _ _ '())))

(define sift
  (extend-relation (a1 a2)
    (fact () '() '())
    (relation (i is ps)
      (to-show `(,i . ,is) `(,i . ,ps))
      (exists (new)
	(all!!
	  (remove i is new)
	  (sift new ps))))))

(define remove
  (extend-relation (a1 a2 a3)
    (fact () _ '() '())
    (relation (p i is (once nis0))
      (to-show p `(,i . ,is) nis0)
      (all!!
        (predicate (i p)
	  (not (zero? (modulo i p))))
	(exists (nis)
	  (all!!
	    (project/no-check (i nis)
	      (== nis0 `(,i . ,nis)))
	    (remove p is nis)))))
    (relation ((once p) is (once nis))
      (to-show p `(,_ . ,is) nis)
      (remove p is nis))))

(define test
  (lambda ()
    (pretty-print
      (time (solve 1 (x) (primes 98 x))))))
