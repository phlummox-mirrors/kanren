(define path
  (extend-relation-with-recur-limit 3 (a1 a2)
    (relation ((once x) (once y))
      (to-show x y)
      (exists (z)
        (all (path x z) (edge z y))))
    (relation ((once x) (once y))
      (to-show x y)
      (edge x y))))

(define edge
  (extend-relation (a1 a2)
    (fact () 1 2)
    (fact () 2 3)
    (fact () 3 4)
    (fact () 4 5)
    (fact () 5 6)
    (fact () 5 2)))

(test-check 'test-left-recursive-path
  (list
    (query (fk subst x) (edge 2 x) (cons (subst-in x subst) (fk)))
    (query (fk subst x) (edge 5 x) (cons (subst-in x subst) (fk)))
    (map (lambda (i) (query (fk subst x) (path i x) (cons (subst-in x subst) (fk))))
      '(1 2 3 4 5 6)))
  '((3) (6 2) ((5 4 3 2) (6 2 5 4 3) (3 6 2 5 4) (4 3 6 2 5) (5 4 3 6 2) ())))
