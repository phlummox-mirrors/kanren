;minikanrentests.scm
;<li><a href="http://www.cs.indiana.edu/l/www/classes/c311/miniaop.pdf">Outcome-Oriented Programming (Mini)</a><BR><BR>
;<li><a href="http://www.cs.indiana.edu/l/www/classes/c311/minirop.pdf">Relation-Oriented Programming (Mini)</a><BR><BR>
;<li><a href="http://www.cs.indiana.edu/l/www/classes/c311/minilop.pdf">Logic-Oriented Programming (Mini)</a><BR><BR>
;<li><a href="http://www.cs.indiana.edu/l/www/classes/c311/miniunify.pdf">Understanding Unification (Mini)</a><BR><BR>
;<li><a href="http://www.cs.indiana.edu/l/www/classes/c311/minitypes.pdf">Type Inference and Type Habitation (Mini)</a><BR><BR>

(define father
  (lambda (dad child)
    (all!! (== dad 'jon) (== child 'sam))))
(define father2
  (lambda (dad child)
    (all!! (== dad 'sam) (== child 'pete))))
(define father4
  (lambda (dad child)
    (any
      (father dad child)
      (father2 dad child)
      (all!! (== dad 'pete) (== child 'sol)))))
(run (x y) (all (father4 x y) (project (x y) (trace-vars "=0=" (x y)))) fk subst (fk) #f)

(run-once (x y)
  (all!! (father4 x y) (project (x y) (trace-vars "=1=" (x y))) (any))
  (void))

(run-once (x y)
  (all! (father4 x y) (project (x y) (trace-vars "=2=" (x y))) (any)) (void))

(run (x y)
  (all! (father4 x y) (project (x y) (trace-vars "=3=" (x y)))) fk sub (fk) #f)

(run (x y)
  (all
    (any (fails (father4 x y)) (all))
    (project (x y)
      (when-only (predicate (var? x))
        (trace-vars "=4=" (x)))))
  fk sub (fk) #f)


(display "Zebra") (newline)

(define memb
  (lambda (item lst)
    (any
      (== lst `(,item . ,_))
      (exists (rest)
	(when-only (all!! (== lst `(,_ . ,rest))) (memb item rest))))))

(define next-to
  (lambda (item1 item2 rest)
    (any (on-right item1 item2 rest) (on-right item2 item1 rest))))

(define on-right
  (lambda (item1 item2 ls)
    (any
      (all!! (== ls `(,item1 ,item2 . ,_)))
      (exists (rest)
        (all
          (== ls `(,_ . ,rest))
          (on-right item1 item2 rest))))))
                
(define zebra
  (lambda (h)
    (when-only
      (all! (== h `((norwegian ,_ ,_ ,_ ,_) ,_ (,_ ,_ milk ,_ ,_) ,_ ,_))
	(memb `(englishman ,_ ,_ ,_ red) h)
	(on-right `(,_ ,_ ,_ ,_ ivory) `(,_ ,_ ,_ ,_ green) h)
	(next-to `(norwegian ,_ ,_ ,_ ,_) `(,_ ,_ ,_ ,_ blue) h)
	(memb `(,_ kools ,_ ,_ yellow) h)
	(memb `(spaniard ,_ ,_ dog ,_) h)
	(memb `(,_ ,_ coffee ,_ green) h)
	(memb `(ukrainian ,_ tea ,_ ,_) h)
	(memb `(,_ luckystrikes oj ,_ ,_) h)
	(memb `(japanese parliaments ,_ ,_ ,_) h)
	(memb `(,_ oldgolds ,_ snails ,_) h)
	(next-to `(,_ ,_ ,_ horse ,_) `(,_ kools ,_ ,_ ,_) h)
	(next-to `(,_ ,_ ,_ fox ,_) `(,_ chesterfields ,_ ,_ ,_) h))
      (all
	(memb `(,_ ,_ water ,_ ,_) h)
	(memb `(,_ ,_ ,_ zebra ,_) h)))))

(test-check "Zebra"
  (time (run-once (h) (zebra h) h))
  '((norwegian kools water fox yellow)
    (ukrainian chesterfields tea horse blue)
    (englishman oldgolds milk snails red)
    (spaniard luckystrikes oj dog ivory)
    (japanese parliaments coffee zebra green)))


(define benchmark
  (letrec
      ([queen
         (lambda (data out)
           (all
             (qperm data out)
             (safe out)))]
       [qperm
         (lambda (a b)
           (any
             (all!! (== a '()) (== b '()))
             (when-only (project (a) (predicate (pair? a)))
               (exists (z u v)
                 (all
                   (qdelete u a z)
                   (== b `(,u . ,v))
                   (qperm z v))))))]
       [qdelete
         (lambda (a b c)
           (exists (l)
             (any
               (all!! (== b `(,a . ,l)) (== c l))
               (exists (h r)
                 (when-only (all!! (== b `(,h . ,l)) (== c `(,h . ,r)))
                   (qdelete a l r))))))]
       [safe
         (lambda (a)
           (any
             (all!! (== a '()))
             (exists (n l)
               (when-only (all!! (== a `(,n . ,l)))
                 (all
                   (nodiag n 1 l)
                   (safe l))))))]
       [nodiag
         (lambda (b d c)
           (any
             (all!! (== c '()))
             (exists (n l)
               (when-only (all!! (== c `(,n . ,l)))
                 (project (n b d)
                   (all!!
                     (predicate (not (= d (- n b))))
                     (predicate (not (= d (- b n))))
                     (nodiag b (+ d 1) l)))))))])
    (lambda (data out)
      (queen data out))))

(define data '(1 2 3 4 5 6 7 8))

(printf "~s~n" (run-once (out) (benchmark data out) out))



(define father
  (lambda (dad child)
    (any
      (all!! (== dad 'jon) (== child 'sam))
      (all!! (== dad 'sam) (== child 'rob))
      (all!! (== dad 'sam) (== child 'roz))
      (all!! (== dad 'rob) (== child 'sal))
      (all!! (== dad 'rob) (== child 'pat))
      (all!! (== dad 'jon) (== child 'hal))
      (all!! (== dad 'hal) (== child 'ted))
      (all!! (== dad 'sam) (== child 'jay)))))

(pretty-print
  (run-list (x y) (father x y) (list x y)))



(define ancestor
  (lambda (old young)
    (any
      (father old young)
      (exists (not-so-old)
        (all (father old not-so-old) (ancestor not-so-old young))))))

(pretty-print
  (run-list (x) (ancestor 'jon x) x))



(define common-ancestor
  (lambda (young-a young-b old)
    (all
      (ancestor old young-a)
      (ancestor old young-b))))

(pretty-print
  (run-list (x) (common-ancestor 'pat 'jay x) x))



(define younger-common-ancestor
  (lambda (young-a young-b old not-so-old)
    (all
      (common-ancestor young-a young-b not-so-old)
      (common-ancestor young-a young-b old)
      (ancestor old not-so-old))))

(pretty-print
  (run-once (x y) (younger-common-ancestor 'pat 'jay x y) (list x y)))

(define youngest-common-ancestor
  (lambda (young-a young-b not-so-old)
    (all
      (common-ancestor young-a young-b not-so-old)
      (exists (y)
        (fails (younger-common-ancestor young-a young-b not-so-old y))))))

(pretty-print
  (run-once (x) (youngest-common-ancestor 'pat 'jay x) x))

;;; Test eigen

(pretty-print
  (run-once (x) (eigen (a b) (== x (cons a b))) x))


(pretty-print
  (run-once (z) ((lambda (x) (ef/only (== x 5) (all) (== x 4))) z) z))

(define test
  (lambda ()
    (run-once (x)
      (all (any (begin (write 4) (all)) (begin (write 11) (all)))
	(only/forget ;;; this has a different meaning if once is replaced by forget
	  (any
	    (begin (write 5) (newline) (== x 4))
	    (begin (write 6) (== x 7))
	    (any)))
	(any))
      (newline))))

(test)

(define scouts
  (extend-relation (s)
    (fact () 'rob)
    (fact () 'sue)
    (fact () 'sal)))

(define athletes
  (extend-relation (a)
    (fact () 'roz)
    (fact () 'sue)
    (fact () 'sal)))

(define busy-children
  (intersect-relation (c)
    scouts
    athletes))

(define social-children
  (extend-relation (c)
    scouts
    athletes))

(define test2
  (lambda ()
    (run-once (c) (all (busy-children c) (trace-vars "::" (c)) (any)) #t)
    (display "------------------------------------")
    (newline)
    (run-once (c) (all (social-children c) (trace-vars "::" (c)) (any)) #t)))

(test2)

(define invertible-binary-function->ternary-relation
  (lambda (op inverted-op)
    (extend-relation (a1 a2 a3)
      (relation (x y z)
        (to-show x y z)
        (project (z)
          (if (var? z)
              (project (x y)
                (== z (op x y)))
              (fail))))
      (relation (x y z)
        (to-show x y z)
        (project (y)
          (if (var? y)
              (project (z x)
                (== y (inverted-op z x)))
              (fail))))
      (relation (x y z)
        (to-show x y z)
        (project (x)
          (if (var? x)
              (project (z y)
                (== x (inverted-op z y)))
              (fail)))))))

(define ++ (invertible-binary-function->ternary-relation + -))
(define -- (invertible-binary-function->ternary-relation - +))
(define ** (invertible-binary-function->ternary-relation * /))
(define // (invertible-binary-function->ternary-relation / *))

(test-check 'test-instantiated-1
  (and
    (run-once (x) (++ x 16.0 8) (= -8.0 x))
    (run-once (x) (++ 10 16.0 x) (= 26.0 x))
    (run-once (x) (-- 10 x 3) (= 13 x)))
  #t)

(define symbol->lnum
  (lambda (sym)
    (map char->integer (string->list (symbol->string sym)))))

(define lnum->symbol
  (lambda (lnums)
    (string->symbol (list->string (map integer->char lnums)))))

(define invertible-unary-function->binary-relation
  (lambda (op inverted-op)
    (extend-relation (a1 a2)
      (relation (x y)
        (to-show x y)
        (project (y)
          (if (var? y)
              (project (x)
                (== y (op x)))
              (fail))))
      (relation (x y)
        (to-show x y)
        (project (x)
          (if (var? x)
              (project (y)
                (== x (inverted-op y)))
              (fail))))
      (relation (x y)
        (to-show x y)
        (begin
          (pretty-print "Third rule")
          (project (x)
            (== y (op x))))))))

(define name
  (invertible-unary-function->binary-relation symbol->lnum lnum->symbol))

(test-check 'test-instantiated-2
  (and
    (run-once (x) (name 'sleep x) (equal? '(115 108 101 101 112) x))
    (run-once (x) (name x '(115 108 101 101 112)) (equal? x 'sleep)))
  #t)

