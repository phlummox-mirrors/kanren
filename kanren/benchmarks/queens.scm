;;http://www.sics.se/quintus/queens.pl
;;9-queens program

(define queen
  (relation ((once out) (once data))
    (to-show data out)
    (queen2 data '() out)))

(define queen2
  (extend-relation (a1 a2 a3)
    (fact () '() _ '())
    (relation (h t history q m)
      (to-show `(,h . ,t) history `(,q . ,m))
      (exists (l1)	
	(all
	  (qdelete q h t l1)
	  (nodiag history q 1)
	  (queen2 l1 `(,q . ,history) m))))))

(define qdelete
  (extend-relation (a1 a2 a3 a4)
    (fact (a l) a a l l)
    (relation ((once x) a h t r)
      (to-show x a `(,h . ,t) `(,a . ,r))
      (qdelete x h t r))))

(define nodiag
  (extend-relation (a1 a2 a3)
    (fact () '() _ _)
    (relation (n l b d)
      (to-show `(,n . ,l) b d)
      (all
	(predicate (d b n)
	  (and
	    (not (= d (- n b)))
	    (not (= d (- b n)))))
	(exists (d1)
	  (project (d)
	    (all
	      (== d1 (+ d 1))
	      (nodiag l b d1))))))))

(define test
  (lambda ()
    (time
      (solve 1000 (x) (queen '(1 2 3 4 5 6 7 8 9) x)))))
