; Missionaries and cannibals based on:
; http://www.cs.berkeley.edu/~russell/code/search/domains/cannibals.lisp
;
; based upon Amr Sabry's implementation
;
; $Id$

;-----------------------------------------------------------------------------
; Given M missionaries, C cannibals, and B boats where each boat 
;   holds at most two people
; Goal: move M+C from one side to the other
; Constraint: cannibals never outnumber missionaries in any place

; (M,C,B) on each side of the river
;type Left  = (Int,Int,Int)
;type Right = (Int,Int,Int)
;type State = (Left,Right)

(define (final? st)
  (fresh (a1 a2)
    (== st `((0 0 ,a1) ,a2))))

;type Action = (Int,Int,Int)
(define legal-actions
  (list
    '(1 0 1)
    '(0 1 1)
    '(2 0 1)
    '(0 2 1)
    '(1 1 1)
    '(-1 0 -1)
    '(0 -1 -1)
    '(-2 0 -1)
    '(0 -2 -1)
    '(-1 -1 -1)
))

(define (legal-action a)
  (fresh (_)
    (reme a legal-actions _)))


; choose an element e from the list lst
;  (choose lst e rest) holds
; if e \in lst and rest = lst \ {e}

(define appendo
  (lambda (l1 l2 l3)
    (conde
      ((== l1 '()) (== l2 l3))
      (else 
        (fresh (x l11 l31)
          (== l1 (cons x l11))
          (== l3 (cons x l31))
          (appendo l11 l2 l31))))))


; common-prefix l l1 l2
; holds iff l is a prefix of both l1 and l2.
(define common-prefix
   (lambda (l l1 l2)
     (conde
        ((== l '()))
        (else
          (fresh (x l* l1* l2*)
            (== l  (cons x l*))
            (== l1 (cons x l1*))
            (== l2 (cons x l2*))
            (common-prefix l* l1* l2*))))))

; A pure rembere: l = lo U {x}
(define reme
  (lambda (x l lo)
    (fresh (l1 l2)
      (common-prefix l1 l lo)
      (appendo l1 (cons x l2) l)
      (appendo l1 l2 lo))))


; (run 6 (q) (fresh (e rest) (reme e '(1 2 3) rest) (== q (list e rest))))
; (run 6 (q) (fresh (e rest) (reme e rest '(1 2 3)) (== q (list e rest))))


; the transmission function...

(define (move st action nextst)
  (fresh (m1 c1 b1 m2 c2 b2 mm cm bm)
    (== st (list (list m1 c1 b1) (list m2 c2 b2)))
    (== action (list mm cm bm))
    (project (m1 c1 b1 m2 c2 b2 mm cm bm)
       (== nextst (list (list (- m1 mm) (- c1 cm) (- b1 bm))
		        (list (+ m2 mm) (+ c2 cm) (+ b2 bm)))))
    (check nextst)))

(define (check st)
   (fresh (m1 c1 b1 m2 c2 b2)
    (== st (list (list m1 c1 b1) (list m2 c2 b2)))
    (project (m1 c1 b1 m2 c2 b2)
      (if (and (>= m1 0) (>= c1 0) (>= b1 0)
	       (>= m2 0) (>= c2 0) (>= b2 0)
	       (or (zero? m1) (<= c1 m1))
	       (or (zero? m2) (<= c2 m2)))
	succeed
	fail))))



; (define (solve left res)
;   (fresh (s)
;     (== s (list left '(0 0 0)))
;     (let loop ((s s))
;       (fresh (s1 a)
; 	(alli
; 	  (legal-action a)
; 	  (move s a s1)
; ; 	  (project (s1 a)
; ; 	    (begin (display "generated: ") (display s1) 
; ; 	           (display " action:" ) (display a) (newline)
; ; 	      succeed))
; 	  (conde
; 	    ((final? s1) (== s1 res))
; 	    ((loop s1))))))))


(run 1 (q)
  (fresh (s a a1 s1 a2 s2 a3 s3 a4 s4) 
    (== s '((2 2 1) (0 0 0)))
    (== a '(1 1 1))
    (move s a s1)
    (== a1 '(-1 0 -1))
    (move s1 a1 s2)
    (== a2 '(2 0 1))
    (move s2 a2 s3)
    (== a3 '(-1 0 -1))
    (move s3 a3 s4)
    (== a4 '(1 1 1))
    (move s4 a4 q)
    (final? q)
))


; frontier is ((frontier-state seen-states actions) ...)
; where actions is the list of actions (the most recent first)
; that lead to frontier-state.
; frontier-state is in seen-states.

(define (solve-dfs left res)
  (define (loop frontier res)
    (fresh (s seen sactions rfrontier a s1 dummy)
      (reme (list s seen sactions) frontier rfrontier)
      (legal-action a)
      (move s a s1)
      (project (s1 a)
	(begin (display "generated: ") (display s1) 
	  (display " action:" ) (display a) (newline)
	  succeed))
      (condu
	((final? s1) (== res `(,s1 ,a . ,sactions)))
	((reme s1 seen dummy) (loop rfrontier res))
	(else
	  (loop (cons (list s1 (cons s1 seen) (cons a sactions)) rfrontier)
	    res)))))
  (let ((s (list left '(0 0 0))))
    (loop (list (list s (list s) '())) res)))

; (run 1 (q) (solve-dfs '(1 1 1) q))
; (run 1 (q) (solve-dfs '(2 2 1) q))
; (run 1 (q) (solve-dfs '(3 3 1) q))
; ((((0 0 0) (3 3 1))
;   (1 1 1)
;   (-1 0 -1)
;   (0 2 1)
;   (0 -1 -1)
;   (2 0 1)
;   (-1 -1 -1)
;   (2 0 1)
;   (0 -1 -1)
;   (0 2 1)
;   (-1 0 -1)
;   (1 1 1)))
; (run 1 (q) (solve-dfs '(4 4 1) q))
; (run 1 (q) (solve-dfs '(4 4 2) q))
; ((((0 0 0) (4 4 2))
;   (1 1 1)
;   (-1 0 -1)
;   (0 2 1)
;   (0 -1 -1)
;   (2 0 1)
;   (2 0 1)
;   (0 -1 -1)
;   (0 -1 -1)
;   (0 2 1)
;   (-2 0 -1)
;   (1 1 1)
;   (1 1 1)))


(define (mapfilter pred neg-guard lst out)
  (conde
    ((== lst '()) (== out '()))
    (else
      (fresh (e e1 rest out1)
	(== lst (cons e rest))
	(conde
	  ((pred e e1)
	    (conde
	      ((neg-guard e1) (mapfilter pred neg-guard rest out))
	      (else
		(== out (cons e1 out1))
		(mapfilter pred neg-guard rest out1))))
	    (else (mapfilter pred neg-guard rest out)))))))

(define (concato l out)
  (conde
    ((== l '()) (== out '()))
    (else
      (fresh (e rest out1)
	(== l (cons e rest))
	(concato rest out1)
	(appendo e out1 out)))))

(define (solve-bfs-pure left res)
  (define (pred-final sa out)
    (fresh (s seen actions)
      (== sa (list s seen actions))
      (final? s)
      (== out (list s actions))
      ))
  (define (grow-frontier sa out)
    (fresh (s seen actions)
      (== sa (list s seen actions))
      (mapfilter 
	(lambda (a sa1)
	  (fresh (s1)
	    (move s a s1)
	    (== sa1 (list s1 (cons s1 seen) (cons a actions)))
	    (project (s1 a)
	      (begin (display "generated: ") (display s1)
		(display " action:" ) (display a) (newline)
		succeed))))
	(lambda (sa) 
	  (fresh (s seen actions seen1 _)
	    (== sa (list s seen actions))
	    (reme s seen seen1)
	    (reme s seen1 _)))
	legal-actions
	out)))
  (define (loop frontier res)
    (conde
      ((fresh (a r)
	 (mapfilter pred-final (lambda (e) fail) frontier (cons a r))
	 (== res (cons a r))))
      (else
	(fresh (seen1 frontier1 lfrontier1)
	  (mapfilter grow-frontier (lambda (e) fail) frontier lfrontier1)
	  (concato lfrontier1 frontier1)
	  (loop frontier1 res)))))
  (let ((s (list left '(0 0 0))))
    (loop (list (list s (list s) '())) res)))


; (run 1 (q) (solve-bfs-pure '(1 1 1) q))
; (run 1 (q) (solve-bfs-pure '(2 2 1) q))
; (run 1 (q) (solve-bfs-pure '(3 3 1) q))
; takes a long time:
; (run 1 (q) (solve-bfs-pure '(4 4 2) q))
