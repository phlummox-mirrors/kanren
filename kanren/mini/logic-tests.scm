(pretty-print
  (run* (x) succeed))

(pretty-print
  (run* (x) fail))

(define appende
  (lambda (l1 l2 out)
    (condo
      ((nullo l1) (== l2 out))
      (else 
        (fresh (a d res)
          (conso a d l1)
          (appende d l2 res)
          (conso a res out))))))

(define nullo
  (lambda (x)
    (== '() x)))

(define conso
  (lambda (a d ls)
    (== (cons a d) ls)))

(pretty-print
  (run 5 (x)
    (fresh (y)
      (appende `(cake and ice . ,y) '(d t) x))))

(define swappende
  (lambda (l1 l2 out)
    (condo
      (succeed
        (fresh (a d res)
          (conso a d l1)
          (conso a res out)
          (swappende d l2 res)))
      (else (nullo l1) (== l2 out)))))

(pretty-print
  (run 2 (q)
    (fresh (x y)
      (swappende x y q))))

(define any*
  (lambda (g)
    (condo
      (g succeed)
      (else (any* g)))))

(define always (any* succeed))

(define never (any* fail))

(pretty-print
  (run 1 (q)                                                                  
    (all                                                                    
      (condo
	((== 'tea q) succeed)
	(else (== 'coffee q)))                    
      always)                                                        
    (== 'coffee q)))

(pretty-print (run 1 (x) fail never))

(pretty-print (run 1 (x) fail always))

(pretty-print (run 1 (x) never fail))

(pretty-print (run 1 (x) always fail))

(define f
  (lambda (ignored)
    fail))

(pretty-print (run 1 (x) always (f x)))

;; (pretty-print (run* (q) never never))  SUPPOSED TO BE INFINITE LOOP

(pretty-print (run* (q) (== q 1) (== q 1)))

(define bar
  (lambda (x)
    (all
      (== 5 x)
      (bar x))))


(test-check "13"
  (run 1 (q) (bar 6))
  '())

(test-check "14"
  (run* (q) (bar 6))
  '())

(define foo
  (lambda (x)
    (all
      (foo x)
      (== 5 x))))

(test-check "11"
  (run 1 (q) (foo 6))
  '())

(test-check "12"
  (run* (q) (foo 6))
  '())

#!eof

(run* (q) (any (== 5 q) (== 6 q)))
(run* (q) (all (any (== 5 q) (== 6 q)) (any (== 6 q) (== 5 q))))
(run* (q) (fresh (x y) (all (any (== 5 x) (== 6 x)) (any (== 10 y) (== 11 y)) (== q (list x y)))))

(define (repeat) (any succeed (repeat)))

(run 5 (q) (repeat))
(run* (q) (all (repeat) (repeat) fail (repeat)))

(run 5 (q) (all (any (repeat) (== q 1)) (repeat)))

(run* (q) (fresh (x y) (all (any (== y x) (== 6 x)) (any (== 10 y) (== 11 y)) (== q (list x y)))))

(run* (q) (fresh (x y) (all (any (== y x) (== 6 x)) (any (== 10 y) (== 11 y)) (== q (list x y)))))


(define (nev1) (any fail (nev1)))
(run 1 (q) (any (== q 1) (nev1)))
(run 1 (q) (any  (nev1) (== q 1)))
(run 1 (q) (any  (nev) (== q 1)))

(run 1 (q) (any (== q 1) (nev)))



(define (nev) (any (all succeed fail) (nev)))
(define (nev1) (any fail (nev1)))

(run 5 (q) (any (== q 1) (nev1)))

(run 5 (q) (all (repeat) fail))

(run 5 (q) (all (repeat) (all succeed fail)))

(run 5 (q) (all (all succeed fail) (repeat) ))

(run 5 (q) (all fail (nev1)))

(run 5 (q) (all (nev1) fail))

(run 5 (q) (all (nev1) (all succeed fail)))


(run 5 (q) (all fail (nev)))

(run 5 (q) (all (nev) fail))

(run 5 (q) (all (nev) (all succeed fail)))


(run 5 (q) (all (repeat) (nev)))

(run 5 (q) (all (nev) (repeat)))


;--------------------

(define (num x)
  (any (== x '()) (fresh (y) (num y) (== x (cons 's y)))))

(run 5 (q) (num q))

(define (num1 x)
  (any  (fresh (y) (num1 y) (== x (cons 's y))) (== x '())))

(run 5 (q) (num1 q))

(define (num2 x)
  (any  (fresh (y) (== x (cons 's y)) (num2 y)) (== x '())))

(run 5 (q) (num2 q))


(define (e x)
  (any (== x '()) (fresh (y) (== x (cons 's (cons 's y))) (e y))))

(run 5 (q) (e q))


(define (o x)
  (any (== x '(s)) (fresh (y) (== x (cons 's (cons 's y))) (o y))))

(run 5 (q) (o q))

(run 1 (q) (num q) (e q) (o q))
(run 1 (q) (num q) (o q) (e q))

(run* (q) (== q 1) (num q))
(run* (q) (== q 1) (num1 q))
(run* (q) (== q 1) (num2 q))

(run* (q) (num q) (== q 1))
(run* (q) (num1 q) (== q 1))
(run* (q) (num2 q) (num2 q) (num2 q) (== q 1))

(run* (q) (== q '()) (o q))
(run* (q) (o q) (== q '()))

(run 1 (q) (num q) (e q)  (== q 1) (o q))

(define (o1 x)
  (any (fresh (y) (== x (cons 's (cons 's y))) (o1 y)) (fresh (y) (== x (cons 's (cons 's y))) (o1 y))))

(run 5 (q) (== q '()) (o1 q))


(define (rev l1 l2 acc)
  (any (all (== l1 '()) (== l2 acc))
       (fresh (y l11 acc1) (== l1 (cons y l11)) (== acc1 (cons y acc))
	      (rev l11 l2 acc1))))

(run* (q) (rev '(1 2 3 4) q '()))

(time (run* (q) (rev '(1 2 3 4) q '())))
(time (run* (q) (rev '(1 2 3 4 5 6 7 8) q '())))
(time (run* (q) (rev '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16) q '())))
(time (run* (q) (rev '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16
		       17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32) q '())))
(time (do ((i 0 (+ 1 i))) ((>= i 100)) (run* (q) (rev '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16
		       17 18 19 20 21 22 23 24 25 26 27 28 29 30) q '()))))



(define (iota n)
  (let loop ((i 1)) (if (= i n) (list n) (cons i (loop (+ 1 i))))))


(time (run* (q) (fresh (y) (rev (iota 4) y '()) (rev y q '()))))
(time (run* (q) (fresh (y) (rev (iota 8) y '()) (rev y q '()))))
(time (run* (q) (fresh (y) (rev (iota 16) y '()) (rev y q '()))))
(time (run* (q) (fresh (y) (rev (iota 32) y '()) (rev y q '()))))
(time (run* (q) (fresh (y) (rev (iota 64) y '()) (rev y q '()))))


(define (rev l1 l2 acc)
  (cond@
    ((== l1 '()) (== l2 acc))
    (else 
      (fresh (y l11 acc1) (== l1 (cons y l11)) (== acc1 (cons y acc))
	      (rev l11 l2 acc1)))))


(define-syntax trace
  (syntax-rules ()
    ((_ title goal)
      (lambda (s)
	(display title)
	(newline)
	(goal s)))))

(let ((s (trace 's succeed)))
  (run* (q) (let ((e (trace '= (== q 1)))) (all s s e s))))

(let ((s (trace 's succeed)))
  (run* (q) (let ((e (trace '= (== q 1)))) (all s s s s s s e s))))

(define (sn x)
  (trace 'sn (any (== x 4) (sn x) (sn x))))

(run* (q) (any (== q 3) (all (== q 4) (sn q))) (all succeed succeed (== q 3) succeed))

(run* (q) (all succeed succeed (== q 3)) (any (== q 3) (all (== q 4) (sn q))) )


(run* (q) (any (== q 3) (all (== q 4) (sn q))) 
  (all succeed succeed (== q 3) succeed))

(run* (q) (any (== q 3) (all (== q 4) (sn q))) 
  (all succeed succeed succeed (== q 3) succeed))

(run* (q) (any (== q 3) (all (== q 4) (sn q))) 
  (all succeed succeed succeed succeed (== q 3) succeed))

(run* (q) (any (== q 3) (all (== q 4) (sn q))) 
  (all succeed succeed succeed succeed succeed (== q 3) succeed))

(run* (q) (any (== q 3) (all (== q 4) (sn q))) 
  (all succeed succeed succeed succeed succeed succeed (== q 3) succeed))

(run* (q)  
  (all succeed succeed (== q 3) succeed)
  (any (== q 3) (all (== q 4)  (sn q)))
)


(run* (q)  
  (all succeed succeed succeed (== q 3) succeed)
  (any (== q 3) (all (== q 4) (sn q)))
)

(run* (q)  
  (all succeed succeed succeed succeed (== q 3) succeed)
  (any (== q 3) (all (== q 4) (sn q)))
)

(run* (q)  
  (all succeed succeed succeed succeed succeed (== q 3) succeed)
  (any succeed succeed)
  (any (== q 3) (all (== q 4) (sn q)))
)

(run* (q)  
  succeed
  (all succeed succeed succeed succeed succeed succeed (== q 3) succeed)
  (any (== q 3) (all (== q 4) (sn q)))
)

(define count 0)
(define tramp
  (letrec ([tramp (lambda (tq-head tq-tail)
		    (set! count (+ 1 count))
		    (cond
		      ((and (null? tq-head) (null? tq-tail)) (empty-stream))
		      ((null? tq-tail) (tramp '() tq-head))
		      (else
			(case-thread (car tq-tail)
			  ((s) (stream-cons s (tramp tq-head (cdr tq-tail))))
			  ((g s) (tramp (append (g s) tq-head)
				   (cdr tq-tail)))))))])
    (lambda (tq)
      (tramp '() tq))))

(define raw-run
  (lambda (filter x f)
    (set! count 0)
    (let ((r (map (lambda (s) (walk* x s))
      (filter (tramp (bounce (f x) empty-s))))))
      (newline) (display count) (newline) r)))

(define (gen x)
  (trace 'gen 
  (any (== x '())
       (fresh (y) (gen y) (== x (list y y y))))))

(define (test x)
  (any (== x '())
       (fresh (y z) (== x (cons z y)) (test y) (test z))))

(run 1 (q) (gen q) (test q))
(run 2 (q) (gen q) (test q))
(run 3 (q) (gen q) (test q))
(run 4 (q) (gen q) (test q))
(run 5 (q) (gen q) (test q))
(run 6 (q) (gen q) (test q))
(run 7 (q) (gen q) (test q))
