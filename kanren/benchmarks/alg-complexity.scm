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
(define make-e
  (lambda (n)
    (let loop ((i 2))
      (if (>= i n) (fact () (- i 1) i)
          (extend-relation (a b)
            (fact () (- i 1) i)
            (loop (+ 1 i)))))))

; make the disjunction of facts (t 1) ... (t m) where m>=1
(define make-t
  (lambda (m)
    (let loop ((i 1))
      (if (>= i m) (fact () i)
          (extend-relation (a)
            (fact () i)
            (loop (+ 1 i)))))))

(define p-test
  (lambda (m n)
    (letrec
        ((e (make-e n))
         (t (make-t m))
         (p
           (extend-relation (x z)
             (relation (head-let x z)
               (exists (y)
                 (all (e x y) (p y z))))
             (relation (head-let `,n x)
               (t x)))))
      (solve (+ m  1) (x) (p 1 x)))))

(pretty-print (p-test 4 5))

(time (p-test 32 64))
(time (p-test 64 128))
(time (p-test 96 192))

; Result:
; (((x.0 1)) ((x.0 2)) ((x.0 3)) ((x.0 4)))
; (time (p-test 32 ...))
;     2 collections
;     35 ms elapsed cpu time, including 1 ms collecting
;     53 ms elapsed real time, including 0 ms collecting
;     2452936 bytes allocated, including 2135552 bytes reclaimed
; (time (p-test 64 ...))
;     9 collections
;     142 ms elapsed cpu time, including 3 ms collecting
;     146 ms elapsed real time, including 0 ms collecting
;     9789840 bytes allocated, including 9770704 bytes reclaimed
; (time (p-test 96 ...))
;     21 collections
;     338 ms elapsed cpu time, including 6 ms collecting
;     385 ms elapsed real time, including 7 ms collecting
;     22011136 bytes allocated, including 22851184 bytes reclaimed

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
	  (relation (head-let x z)
	    (exists (y)
	      (all (e x y) (p y z))))
	  (relation (head-let `,n x)
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
	  (relation (head-let x z)
	    (exists (y)
	      (if-only (e x y) (p y z))))
	  (relation (head-let `,n x)
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
;     2 collections
;     27 ms elapsed cpu time, including 0 ms collecting
;     28 ms elapsed real time, including 0 ms collecting
;     1682288 bytes allocated, including 2144696 bytes reclaimed
; (time (p-test 64 ...))
;     6 collections
;     104 ms elapsed cpu time, including 0 ms collecting
;     107 ms elapsed real time, including 0 ms collecting
;     6609536 bytes allocated, including 6484888 bytes reclaimed
; (time (p-test 96 ...))
;     14 collections
;     240 ms elapsed cpu time, including 2 ms collecting
;     269 ms elapsed real time, including 2 ms collecting
;     14800240 bytes allocated, including 15122192 bytes reclaimed

; Previously, there was an improvement. Not any more. head-let was
; actually quite efficient. The complexity is still O(n*m). We really
; need to do something about the e-relation. We need to make the cost
; of answering e-goals constant.

(define make-e
  (lambda (n)
    (lambda (x y)
      (all!!
        (predicate (x) (< x n))
        (project (x)
          (== y (+ x 1)))))))

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
(define make-e
  (lambda (n)
    (lambda (x y)
      (lambda@ (sk fk subst)
        (let ((x (subst-in x subst)))
          (nonvar! x)
          (if (< x n) (@ (== y (+ x 1)) sk fk subst)
              (fk)))))))

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


(define p-test
  (lambda (m n)
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
      (solve (+ m  1) (x) (p 1 x)))))
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

'(define prune-subst
  (lambda (vars in-subst subst)
    (printf "vars ~a in-subst: ~a~nsubst ~a~n" vars in-subst subst)
    subst))

'(define prune-subst
  (lambda (vars in-subst subst)
    (printf "vars ~a in-subst: ~a~nsubst ~a~n" vars in-subst subst)
    (if (eq? subst in-subst)
      subst
      (let ([var-bindings ; the bindings of truly bound vars
	      (let loop ([vars vars])
		(if (null? vars) vars
		  (let ([binding (assq (car vars) subst)])
		    (if binding
		      (cons binding (loop (cdr vars)))
		      (loop (cdr vars))))))])
	(cond
	  [(null? var-bindings) subst] ; none of vars are bound
	  [(null? (cdr var-bindings))
	    ; only one variable to prune, use the faster version
	   (prune-subst-1 (commitment->var (car var-bindings))
	     in-subst subst)]
	  [(let test ([vb var-bindings]) ; check multiple dependency
	     (and (pair? vb)
	       (or (let ([term (commitment->term (car vb))])
		     (and (var? term) (assq term var-bindings)))
		 (test (cdr vb)))))
	    ; do pruning sequentially
	   (let loop ([var-bindings var-bindings] [subst subst])
	     (if (null? var-bindings) subst
	       (loop (cdr var-bindings)
		 (prune-subst-1 (commitment->var (car var-bindings))
		   in-subst subst))))]
	  [else				; do it in parallel
	    (let loop ([current subst])
	      (cond
		[(null? current) current]
		[(eq? current in-subst) current]
		[(memq (car current) var-bindings)
		 (loop (cdr current))]
		[(assq (commitment->term (car current)) var-bindings) =>
		 (lambda (ct)
		   (cons (commitment (commitment->var (car current)) 
			   (commitment->term ct))
		     (loop (cdr current))))]
		[else (cons (car current) (loop (cdr current)))]))])))))

(define p-test
  (lambda (m n)
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
      (solve (+ m  1) (x) (p 1 x)))))
(pretty-print (p-test 4 5))
