(newline)
(display "Testing the algorithmic complexity of top-down inference")
(newline)

; 	p(X,Z) :- e(X,Y), p(Y,Z).
; 	p(n,X) :- t(X).
; 	e(1, 2),...,e(n-1, n).
; 	t(1),....,t(m).
; 	Query: ?-p(1,X).
; This example in more detail is explained in
; 	http://citeseer.nj.nec.com/374977.html

; In a good Prolog implementation, it takes O(n+m) [space and time] to
; find all the answers. In (semi-naive) bottom-up, it takes O(n*m) 
; [space and time]. 
;
; The moment of reflection would reveal some cheating: It's impossible
; to achieve O(n+m) performance unless we assume that solving subgoal
; e(n,m) takes the unit time. In other words, we need to do something better
; than try each e(1,2) ... e(n-1,n) in turn.
; Because the example is a Datalog rather than a Prolog program, and because
; relations e() and t() are both from an extensional database,
; we can indeed assume that the cost of solving either e() or t() is
; constant. We can emulate that in our system, see below.
;
; $Id$

; Here's the first attempt:
; make the disjunction of facts (e 1 2) (e 2 3) ... (e n-1 n) where n>1
(define (make-e n)
  (let loop ((i 2))
    (if (>= i n) (fact () (- i 1) i)
      (extend-relation (a b)
	(fact () (- i 1) i)
	(loop (+ 1 i))))))

; make the disjunction of facts (t 1) ... (t m) where m>=1
(define (make-t m)
  (let loop ((i 1))
    (if (>= i m) (fact () i)
      (extend-relation (a)
	(fact () i)
	(loop (+ 1 i))))))

(define (p-test m n)
  (letrec
    ((e (make-e n))
      (t (make-t m))
      (p
	(extend-relation (x z)
	  (relation (x z)
	    (to-show x z)
	    (exists (y)
	      (all (e x y) (p y z))))
	  (relation (x)
	    (to-show n x)
	    (t x)))))
    (solve (+ m  1) (x) (p 1 x))))

(pretty-print (p-test 4 5))

(time (p-test 32 64))
(time (p-test 64 128))
(time (p-test 96 192))

; Result:
; (((x.0 1)) ((x.0 2)) ((x.0 3)) ((x.0 4)))
; (time (p-test 32 ...))
;     3 collections
;     44 ms elapsed cpu time, including 2 ms collecting
;     49 ms elapsed real time, including 2 ms collecting
;     3241944 bytes allocated, including 3327864 bytes reclaimed
; (time (p-test 64 ...))
;     12 collections
;     170 ms elapsed cpu time, including 2 ms collecting
;     179 ms elapsed real time, including 0 ms collecting
;     12861048 bytes allocated, including 12934472 bytes reclaimed
; (time (p-test 96 ...))
;     26 collections
;     402 ms elapsed cpu time, including 8 ms collecting
;     407 ms elapsed real time, including 7 ms collecting
;     28805320 bytes allocated, including 28338544 bytes reclaimed

; Obviously, the performance is O(m*n) rather than linear as hoped.

; Let us attempt some optimization:
; make the disjunction of facts (e 1 2) (e 2 3) ... (e n-1 n) where n>1
(define (make-e n)
  (lambda (x y)
    (let loop ((i 2))
      (if (>= i n) ((fact () (- i 1) i) x y)
      (any
	((fact () (- i 1) i) x y)
	(loop (+ 1 i)))))))

; make the disjunction of facts (t 1) ... (t m) where m>=1
(define (make-t m)
  (lambda (x)
    (let loop ((i 1))
      (if (>= i m) ((fact () i) x)
	(any
	  ((fact () i) x)
	  (loop (+ 1 i)))))))

(pretty-print (p-test 4 5))

(time (p-test 32 64))
(time (p-test 64 128))
(time (p-test 96 192))

; Hardly anything changed.

; make the disjunction of facts (e 1 2) (e 2 3) ... (e n-1 n) where n>1
(define (make-e n)
  (let ((meta
	  `(extend-relation (x y)
	     ,@(let loop ((i 2))
		 (if (> i n) '()
		   (cons `(fact () ,(- i 1) ,i)
		     (loop (+ 1 i))))))))
    (eval meta (interaction-environment))))

'(pretty-print 
  (expand '(extend-relation (x) (fact () 1) (fact () 2) (fact () 3))))

; make the disjunction of facts (t 1) ... (t m) where m>=1
(define (make-t m)
  (let ((meta
	  `(extend-relation (x)
	     ,@(let loop ((i 1))
		 (if (> i m) '()
		   (cons `(fact () ,i)
		     (loop (+ 1 i))))))))
    (eval meta (interaction-environment))))

(define (p-test m n)
  (letrec
    ((e (make-e n))
      (t (make-t m))
      (p
	(extend-relation (x z)
	  (relation (x z)
	    (to-show x z)
	    (exists (y)
	      (all (e x y) (p y z))))
	  (relation (x)
	    (to-show n x)
	    (t x)))))
    (solve (+ m  1) (x) (p 1 x))))

(pretty-print (p-test 4 5))

(time (p-test 32 64))
(time (p-test 64 128))
(time (p-test 96 192))

; make the disjunction of facts (e 1 2) (e 2 3) ... (e n-1 n) where n>1
(define (make-e n)
  (lambda (x y)
    (let loop ((i 2))
      (if (>= i n) ((fact () (- i 1) i) x y)
      (any
	((fact () (- i 1) i) x y)
	(loop (+ 1 i)))))))

; make the disjunction of facts (t 1) ... (t m) where m>=1
(define (make-t m)
  (lambda (x)
    (let loop ((i 1))
      (if (>= i m) ((fact () i) x)
	(any
	  ((fact () i) x)
	  (loop (+ 1 i)))))))

; Now, let's follow what the paper says: relation e(n,m) with n bound
; has only one answer. So we simulate this by changing all with if-only
; below:

(define (p-test m n)
  (letrec
    ((e (make-e n))
      (t (make-t m))
      (p
	(extend-relation (x z)
	  (relation (x z)
	    (to-show x z)
	    (exists (y)
	      (if-only (e x y) (p y z))))
	  (relation (x)
	    (to-show n x)
	    (t x)))))
    (solve (+ m  1) (x) (p 1 x))))

(pretty-print (p-test 4 5))

(time (p-test 32 64))
(time (p-test 64 128))
(time (p-test 96 192))

; We can try to optimize even further, by simplifying the definition for
; p:

(define (p-test m n)
  (letrec
    ((e (make-e n))
      (t (make-t m))
      (p
	(lambda (x z)
	  (any
	    (exists (y)
	      (if-only (e x y) (p y z)))
	    (if-only (promise-one-answer (== x n))
	      (t z))))))
    (solve (+ m  1) (x) (p 1 x))))

(pretty-print (p-test 4 5))

(time (p-test 32 64))
(time (p-test 64 128))
(time (p-test 96 192))

; (((x.0 1)) ((x.0 2)) ((x.0 3)) ((x.0 4)))
; (time (p-test 32 ...))
;     1 collection
;     19 ms elapsed cpu time, including 0 ms collecting
;     18 ms elapsed real time, including 0 ms collecting
;     1504968 bytes allocated, including 1063024 bytes reclaimed
; (time (p-test 64 ...))
;     6 collections
;     72 ms elapsed cpu time, including 0 ms collecting
;     72 ms elapsed real time, including 1 ms collecting
;     5895648 bytes allocated, including 6483120 bytes reclaimed
; (time (p-test 96 ...))
;     12 collections
;     165 ms elapsed cpu time, including 3 ms collecting
;     166 ms elapsed real time, including 5 ms collecting
;     13170480 bytes allocated, including 13255968 bytes reclaimed

; Things improve, but the complexity is still O(n*m). We really need to
; do something about the e-relation. We need to make the cost of
; answering e-goals constant.

(define (make-e n)
  (lambda (x y)
    (all!!
      (predicate (x) (< x n))
      (let-inject ((t (x) (+ x 1)))
	(== t y)))))

(pretty-print (p-test 4 5))

(time (p-test 32 64))
(time (p-test 64 128))
(time (p-test 96 192))

; (((x.0 1)) ((x.0 2)) ((x.0 3)) ((x.0 4)))
; (time (p-test 32 ...))
;     1 collection
;     12 ms elapsed cpu time, including 0 ms collecting
;     12 ms elapsed real time, including 0 ms collecting
;     977512 bytes allocated, including 1062288 bytes reclaimed
; (time (p-test 64 ...))
;     3 collections
;     43 ms elapsed cpu time, including 0 ms collecting
;     43 ms elapsed real time, including 1 ms collecting
;     3627552 bytes allocated, including 3236752 bytes reclaimed
; (time (p-test 96 ...))
;     8 collections
;     93 ms elapsed cpu time, including 2 ms collecting
;     93 ms elapsed real time, including 1 ms collecting
;     7966912 bytes allocated, including 8641888 bytes reclaimed

; That is an improvement. And yet non-linear -- even more obvious than
; above. We have not only linearity with respect to n*m, we even have
; direct proportionality: Theta(n*m).

; The following gives only 9% improvement
(define (make-e n)
  (lambda (x y)
    (lambda@ (sk fk subst)
      (let ((x (subst-in x subst)))
	(nonvar! x)
	(if (< x n) (@ (== y (+ x 1)) sk fk subst)
	  (fk))))))

(pretty-print (p-test 4 5))

(time (p-test 32 64))
(time (p-test 64 128))
(time (p-test 96 192))

(printf "~nempty prune-subst~n")
(define prune-subst  (lambda (vars in-subst subst) subst))

(pretty-print (p-test 4 5))

(time (p-test 32 64))
(time (p-test 64 128))
(time (p-test 96 192))


(define (p-test m n)
  (letrec
    ((e (make-e n))
      (t (make-t m))
      (p
	(lambda (x z)
	  (any
	    (let-lv (y)
	      (if-only (e x y) (p y z)))
	    (if-only (promise-one-answer (== x n))
	      (t z))))))
    (solve (+ m  1) (x) (p 1 x))))
(pretty-print (p-test 4 5))

(time (p-test 32 64))
(time (p-test 64 128))
(time (p-test 96 192))

; (((x.0 1)) ((x.0 2)) ((x.0 3)) ((x.0 4)))
; (time (p-test 32 ...))
;     no collections
;     1 ms elapsed cpu time
;     1 ms elapsed real time
;     66952 bytes allocated
; (time (p-test 64 ...))
;     no collections
;     2 ms elapsed cpu time
;     2 ms elapsed real time
;     133824 bytes allocated
; (time (p-test 96 ...))
;     no collections
;     4 ms elapsed cpu time
;     4 ms elapsed real time
;     200656 bytes allocated

; Isn't that amazing... The amount of allocated memory shows the
; long-sought linearity: the difference between the third and the first
; tests is twice as much as the difference between the second and the first.

(printf "~ndetailed prune-subst~n")
(define prune-subst
  (lambda (vars in-subst subst)
    (printf "vars ~a in-subst: ~a~nsubst ~a~n" vars in-subst subst)
    subst))
(define prune-subst
  (lambda (vars in-subst subst)
    (printf "vars ~a in-subst: ~a~nsubst ~a~n" vars in-subst subst)
    (if (eq? subst in-subst)
        subst
        (let loop ([current subst] [to-remove '()] [clean '()] [to-subst '()])
          (cond
            [(null? current) (compose-subst/own-survivors to-subst to-remove clean)]
            [(eq? current in-subst)
             (compose-subst/own-survivors to-subst to-remove (append clean current))]
            [(memq (commitment->var (car current)) vars)
             (loop (cdr current) (cons (car current) to-remove) clean to-subst)]
            [(relatively-ground? (commitment->term (car current)) vars)
             (loop (cdr current) to-remove (cons (car current) clean) to-subst)]
            [else (loop (cdr current) to-remove clean (cons (car current) to-subst))])))))

(define (p-test m n)
  (letrec
    ((e (make-e n))
      (t (make-t m))
      (p
	(lambda (x z)
	  (any
	    (exists (y)
	      (if-only (e x y) (p y z)))
	    (if-only (promise-one-answer (== x n))
	      (t z))))))
    (solve (+ m  1) (x) (p 1 x))))
(pretty-print (p-test 4 5))
