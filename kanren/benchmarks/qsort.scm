;; http://www.sics.se/quintus/qsort.pl

; $Id$

;   qsort
;
;   David H. D. Warren
;
;   quicksort a list of 50 integers

(define qsort
  (extend-relation (a1 a2 a3)
    (fact (r) '() r r)
    (relation (x l (once r) (once r0))
      (to-show `(,x . ,l) r r0)
      (exists (l1 l2 r1)
        (all
         (partition l x l1 l2)
         (qsort l2 r1 r0)
         (project/no-check (x r1)
           (qsort l1 r `(,x . ,r1))))))))

(define partition
  (extend-relation (a1 a2 a3 a4)
    (fact () '() _ '() '())
    (relation (x l y l1 (once l2))
      (to-show `(,x . ,l) y `(,x . ,l1) l2)
      (all!
       (predicate (x y)
         (<= x y))
       (partition l y l1 l2)))
    (relation (x l (once y) (once l1) l2)
      (to-show `(,x . ,l) y l1 `(,x . ,l2))
      (partition l y l1 l2))))

(define data '(27 74 17 33 94 18 46 83 65 2 32 53 28 85 99 47 28 82 6 11 55 29 39 81 90 37 10 0 66 51 7 21 85 27 31 63 75 4 95 99 11 28 61 74 18  92 40 53 59 8))

(define test-qsort
  (lambda ()
    (pretty-print
     (time (solve 1 (x) (qsort data x '()))))))