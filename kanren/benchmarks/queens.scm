;;http://www.sics.se/quintus/queens.pl
;;9-queens program

; SWI-Prolog, (Version 5.0.10), Pentium IV, 2GHz:
; ?- time(dobench(10)).
; % 134,676,991 inferences in 60.43 seconds (2228656 Lips)

; $Id$

(define benchmark_count 100)

(define data '(1 2 3 4 5 6 7 8 9))

; queen(Data, Out) :-
; 	qperm(Data, Out),
; 	safe(Out).

; qperm([], []).
; qperm([X|Y], K) :-
; 	qdelete(U, [X|Y], Z),
; 	K = [U|V],
; 	qperm(Z, V).

; qdelete(A, [A|L], L).
; qdelete(X, [A|Z], [A|R]) :-
; 	qdelete(X, Z, R).
;
; safe([]).
; safe([N|L]) :-
; 	nodiag(N, 1, L),
; 	safe(L).

; nodiag(_, _, []).
; nodiag(B, D, [N|L]) :-
; 	D =\= N - B,
; 	D =\= B - N,
; 	D1 is D + 1,
; 	nodiag(B, D1, L).

(define benchmark
  (letrec
    ((queen
       (relation (head-let data out)
	 (all
	   (qperm data out)
	   (safe out))))

     (qperm
       (extend-relation (a b)
	 (fact () '() '())
	 (relation (x y (once k))
	   (to-show `(,x . ,y) k)
	   (exists (z u v)
	     (all
	       (qdelete u `(,x . ,y) z)
	       (== k `(,u . ,v))
	       (qperm z v))))))

      (qdelete
	(extend-relation (a b c)
	  (fact (a l) a `(,a . ,l) l)
	  (relation ((once x) a z r)
	    (to-show x `(,a . ,z) `(,a . ,r))
	    (qdelete x z r))))

     (safe
       (extend-relation (a)
	 (fact () '())
	 (relation (n l)
	   (to-show `(,n . ,l))
	   (all
	     (nodiag n 1 l)
	     (safe l)))))
     (nodiag
       (extend-relation (a b c)
	 (fact () _ _ '())
	 (relation ((once b) (once d) n l)
	   (to-show b d `(,n . ,l))
	   (project (n b d)
	     (all!!
	       (predicate (not (= d (- n b))))
	       (predicate (not (= d (- b n))))
	       (nodiag b (+ d 1) l))))))
      )
    (lambda (data out)
      (queen data out))))

; (time (solve 1000 ...))
;     17895 collections
;     364186 ms elapsed cpu time, including 5151 ms collecting
;     369844 ms elapsed real time, including 5228 ms collecting
;     19362955352 bytes allocated, including 19360894888 bytes reclaimed


(define benchmark
  (letrec
    ((queen
       (relation (head-let data out)
	 (all
	   (qperm data out)
	   (safe out))))

     (qperm
       (extend-relation (a b)
	 (fact () '() '())
	 (relation (head-let l k)
	   (if-only (project (l) (predicate (pair? l)))
	   (exists (z u v)
	     (all
	       (qdelete u l z)
	       (== k `(,u . ,v))
	       (qperm z v)))))))

      (qdelete
	(extend-relation (a b c)
	  (fact (a l) a `(,a . ,l) l)
	  (relation ((once x) a z r)
	    (to-show x `(,a . ,z) `(,a . ,r))
	    (qdelete x z r))))

     (safe
       (extend-relation (a)
	 (fact () '())
	 (relation (n l)
	   (to-show `(,n . ,l))
	   (all
	     (nodiag n 1 l)
	     (safe l)))))
     (nodiag
       (extend-relation (a b c)
	 (fact () _ _ '())
	 (relation ((once b) (once d) n l)
	   (to-show b d `(,n . ,l))
	   (project (n b d)
	     (all!!
	       (predicate (not (= d (- n b))))
	       (predicate (not (= d (- b n))))
	       (nodiag b (+ d 1) l))))))
      )
    (lambda (data out)
      (queen data out))))

(test-check 'queens-benchmark
  (solve 2 (out) (benchmark data out))
  '(((out.0 (1 3 6 8 2 4 9 7 5))) ((out.0 (1 3 7 2 8 5 9 4 6)))))

'(test-check 'queens-benchmark-time
  (length
    (time (solve 1000 (out) (benchmark data out))))
  352)

; kanren.ss version 3.45
; (time (solve 1000 ...))
;     13193 collections
;     265112 ms elapsed cpu time, including 3682 ms collecting
;     270339 ms elapsed real time, including 3657 ms collecting
; kanren.ss version 3.53
; (time (solve 1000 ...))
;     13476 collections
;     263209 ms elapsed cpu time, including 3625 ms collecting
;     266191 ms elapsed real time, including 3609 ms collecting
;
; kanren.ss version 4.0
; (time (solve 1000 ...))
;     6214 collections
;     137652 ms elapsed cpu time, including 1631 ms collecting
;     138948 ms elapsed real time, including 1618 ms collecting
;     6723336032 bytes allocated, including 6722051232 bytes reclaimed
; kanren.ss version 4.1
; (time (solve 1000 ...))
;     6295 collections
;     128446 ms elapsed cpu time, including 1602 ms collecting
;     130004 ms elapsed real time, including 1642 ms collecting
;     6811773760 bytes allocated, including 6810404512 bytes reclaimed
; kanren.ss version 4.11
; (time (solve 1000 ...))
;     6218 collections
;     116317 ms elapsed cpu time, including 1620 ms collecting
;     117676 ms elapsed real time, including 1633 ms collecting
;     6728505992 bytes allocated, including 6726980680 bytes reclaimed


; The following implementation is more functional and less relational
; It deviates from the Prolog implementation.
; First, we note that 'safe' is a deterministic predicate that
; operates on the already instantiated list.

(define benchmark
  (letrec
    ((queen
       (relation (head-let data out)
	 (all
	   (qperm data out)
	   (safe out))))

     (qperm
       (extend-relation (a b)
	 (fact () '() '())
	 (relation (head-let l k)
	   (if-only (project (l) (predicate (pair? l)))
	   (exists (z u v)
	     (all
	       (qdelete u l z)
	       (== k `(,u . ,v))
	       (qperm z v)))))))

      (qdelete
	(extend-relation (a b c)
	  (fact (a l) a `(,a . ,l) l)
	  (relation ((once x) a z r)
	    (to-show x `(,a . ,z) `(,a . ,r))
	    (qdelete x z r))))

     (safe				; a deterministic predicate
       (relation (head-let l)
	 (project (l)
	   (predicate
	     (let safe ((l l))
	       (or (null? l)
		 (and
		   (let nodiag ((b (car l)) (d 1) (lr (cdr l)))
		     (or (null? lr)
		       (let ((n (car lr)) (l (cdr lr)))
			 (and
			   (not (= d (abs (- n b))))
			   (nodiag b (+ 1 d) l)))))
		   (safe (cdr l)))))))))
      )
    (lambda (data out)
      (queen data out))))

; kanren.ss version 4.15 (similar to 4.11)
; (time (solve 1000 ...))
;     3774 collections
;     74406 ms elapsed cpu time, including 825 ms collecting
;     75198 ms elapsed real time, including 782 ms collecting
;     4084184064 bytes allocated, including 4083081312 bytes reclaimed


; Now we take advantage of the fact that the parameter l in qdelete
; is fully instantiated.
; Actually, all of our relations are actually indeterministic functions:
; all their arguments are instantiated, except the last one
; (to which the result is bound to).

(define benchmark
  (letrec
    ((queen
       (relation (head-let data out)
	 (all
	   (qperm data out)
	   (project (out)
	     (safe out)))))

     (qperm
       (lambda (l k)
	 (if (null? l) (== k '())
	   (exists (dr)
	     (all (qdelete l dr)
	       (project (dr)
		 (let ((u (car dr)) (z (cdr dr)))
		   (exists (v)
		     (all
		       (qperm z v)
			 (== k (cons u v)))))))))))
      (qdelete
	(lambda (l l1)
	  (if (null? l)
	    fail
	    (any
	      (== l l1)
	      (exists (u)
		(all
		  (qdelete (cdr l) u)
		  (project (u)
		    (== l1 (cons (car u) (cons (car l) (cdr u)))))))))))

     (safe				; a deterministic predicate
       (lambda (l)
	 (predicate
	   (let safe ((l l))
	     (or (null? l)
	       (and
		 (let nodiag ((b (car l)) (d 1) (lr (cdr l)))
		   (or (null? lr)
		     (let ((n (car lr)) (l (cdr lr)))
		       (and
			 (not (= d (abs (- n b))))
			 (nodiag b (+ 1 d) l)))))
		 (safe (cdr l))))))))
      )
    (lambda (data out)
      (queen data out))))

; kanren.ss version 4.15 (similar to 4.11)
; (time (solve 1000 ...))
;     1738 collections
;     37260 ms elapsed cpu time, including 362 ms collecting
;     37609 ms elapsed real time, including 367 ms collecting
;     1880374592 bytes allocated, including 1880634984 bytes reclaimed

; The following is a closer emulation of non-deterministic functions
; Even notation is better: A-normal form rather than CPS.

(define yield-var (logical-variable '*yield*))
(define (yield val) (== yield-var val))
; The latter is similar to the above, but much faster.
; We take advantage of the fact that yield-var, like `multiple values'
; is ephemeral and so we don't need to scan the substitutions
; and do regular unification tests. It is clear that yield-var is
; `fresh' and unbound.
(define (yield val) 
  (lambda@ (sk fk subst)
    (@ sk fk (extend-subst yield-var val subst))))

(define-syntax let-fr
  (syntax-rules ()
    ((let-fr ((var exp)) body)
      (all exp
	(lambda@ (sk fk subst)
	  (if (not (eq? (commitment->var (car subst)) yield-var))
	    (error "bummer"))
	  (let ((var (commitment->term (car subst))))
	    (@ body sk fk (cdr subst))))))))

(define benchmark
  (letrec
    ((queen
       (relation (head-let data out)
	 (let-fr ((res (qperm data)))
	   (all!! (safe res) (== res out)))))

     (qperm
       (lambda (l)
	 (if (null? l) (yield '())
	   (let-fr ((dr (qdelete l)))
	     (let ((u (car dr)) (z (cdr dr)))
	       (let-fr ((v (qperm z)))
		 (yield (cons u v))))))))

      (qdelete
	(lambda (l)
	  (if (null? l) fail
	    (any
	      (yield l)
	      (let-fr ((u (qdelete (cdr l))))
		(yield (cons (car u) (cons (car l) (cdr u)))))))))

     (safe				; a deterministic predicate
       (lambda (l)
	 (predicate
	   (let safe ((l l))
	     (or (null? l)
	       (and
		 (let nodiag ((b (car l)) (d 1) (lr (cdr l)))
		   (or (null? lr)
		     (let ((n (car lr)) (l (cdr lr)))
		       (and
			 (not (= d (abs (- n b))))
			 (nodiag b (+ 1 d) l)))))
		 (safe (cdr l))))))))
      )
    (lambda (data out)
      (queen data out))))

; kanren.ss version 4.15 (similar to 4.11)
; (time (solve 1000 ...))
;     1333 collections
;     13660 ms elapsed cpu time, including 242 ms collecting
;     13754 ms elapsed real time, including 253 ms collecting
;     1443508328 bytes allocated, including 1443541736 bytes reclaimed

; kanren.ss version 4.17 (similar to 4.11)
; (time (solve 1000 ...))
;     1333 collections
;     13586 ms elapsed cpu time, including 248 ms collecting
;     13762 ms elapsed real time, including 258 ms collecting
;     1443382216 bytes allocated, including 1443524336 bytes reclaimed
