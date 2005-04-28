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
(define (legal-actions a)
  (conde
    ((== a '(1 0 1))) 
    ((== a '(0 1 1)))
    ((== a '(2 0 1)))
    ((== a '(0 2 1)))
    ((== a '(1 1 1)))
    ((== a '(-1 0 -1)))
    ((== a '(0 -1 -1)))
    ((== a '(-2 0 -1)))
    ((== a '(0 -2 -1)))
    ((== a '(-1 -1 -1)))
))

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


; choose an element e from the list lst
;  (choose lst e rest) holds
; if e \in lst and rest = lst \ {e}
(define (choose lst e rest)
  (condi
    ((== lst (cons e rest)))
    (else
      (fresh (e1 lst1 rest1)
	(== lst (cons e1 lst1))
	(== rest (cons e1 rest1))
	(choose lst1 e rest1)))))

; (run 6 (q) (fresh (e rest) (choose '(1 2 3) e rest) (== q (list e rest))))
; (run 6 (q) (fresh (e rest) (choose rest e '(1 2 3)) (== q (list e rest))))

; (define (solve left res)
;   (fresh (s)
;     (== s (list left '(0 0 0)))
;     (let loop ((s s))
;       (fresh (s1 a)
; 	(alli
; 	  (legal-actions a)
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

	
; seen is the list of seen states
; frontier is the list of frontier states together with the actions
; that lead to them.
; Each element of frontier is a list, whose car is the state and the rest
; is the list of actions
; All states in frontier are in seen.

(define (solve-dfs left res)
  (define (loop seen frontier res)
    (fresh (s sactions rfrontier a s1 dummy)
      (choose frontier (cons s sactions) rfrontier)
      (legal-actions a)
      (move s a s1)
      (project (s1 a)
	(begin (display "generated: ") (display s1) 
	  (display " action:" ) (display a) (newline)
	  succeed))
      (condu
	((choose seen s1 dummy) (loop seen rfrontier res))
	((final? s1) (== res `(,s1 ,a . ,sactions)))
	(else
	  (fresh (seen1 frontier1)
	    (== seen1 (cons s1 seen))
	    (== frontier1 (cons `(,s1 ,a . ,sactions) rfrontier))
	    (loop seen1 frontier1 res))))))
  (fresh (s)
    (== s (list left '(0 0 0)))
    (loop (list s) (list (list s)) res)))

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
