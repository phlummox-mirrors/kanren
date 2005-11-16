(load "minikanrensupport.scm")

; An attempt at complete and refutationally complete
; implementation
; The computation is an AND-OR tree, and each node of the tree
; is assuredly visited in finite time.

; data Ans a = Nil | Cons a (Int -> Ans a) | Incomplete (Int -> Ans a)

; a is the substitution;
;
; This implementation uses a ``final algebra'' -- or a threded interpreter
; (aka the one in Forth) rather than an interpreter over a data structure.

; $Id$

(define depth-quantum 5)

; Two-level queue:
; type OR-queue = [And-queue]
; data And-queue = And-queue Subst [Goal]
; type Goal = Limit -> Subst -> ANDqueue -> ORqueue -> Ans a

(define (enq-last  e q) (append q (list e)))
(define (enq-last2 e1 e2 q) (append q (list e1 e2)))

; constructor of a suspension: Limit -> Ans a
(define-syntax lambdaf@
  (syntax-rules ()
    ((_ (n) e) (lambda (n) e))))

; constructor of a goal: Limit -> Subst -> ANDqueue -> ORqueue -> Ans a
(define-syntax lambdag@
  (syntax-rules ()
    ((_ (n s andq orq) e) (lambda (n s andq orq) e))))

(define schedule
  (lambda (orq)				; orq isn't empty
    (lambdaf@ (n)
      (let* ((ande (car orq)) (orq  (cdr orq))
	     (s (car ande))   (andq (cdr ande)))
	((car andq) n s (cdr andq) orq)))))


; Kanren implementation
(define succeed 
  (lambdag@ (n s andq orq)
    (if (null? andq)		; we have the answer
      (if (null? orq) (cons s #f) (cons s (schedule orq)))
      ; Run the rest of the andq
      (let ((h (car andq)) (andq (cdr andq)))
	(h (+ n 1) s andq orq)))))

(define fail 
  (lambdag@ (n s andq orq)
    (if (null? orq) 		   ; we have no alternatives: total failure
      #f
      (schedule orq))))


; ((G1 & G2) & AndQ) | OrQ
(define seq
  (lambda (g1 g2)
    (lambdag@ (n s andq orq)
      (if (positive? n)			; positive balance: run depth-first
	(g1 (- n 1) s (enq-last g2 andq) orq)
	(schedule (enq-last (cons s (enq-last2 g1 g2 andq)) orq))))))

; ((G1 | G2) & AndQ) | OrQ
(define choice
  (lambda (g1 g2)
    (lambdag@ (n s andq orq)
      (if (positive? n)			; positive balance: run depth-first
	(g1 (- n 1) s andq (enq-last (cons s (enq-last g2 andq)) orq))
	(let ((ande1 (cons s (enq-last g1 andq)))
	      (ande2 (cons s (enq-last g2 andq))))
	  (schedule (enq-last2 ande1 ande2 orq)))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (x) g0 g ...)
     (let ((x (var 'x)))
       (rn x (all g0 g ...) prefix*)))))

(define rn
  (lambda (x g filter)
    (map (lambda (s) (reify x s)) 
      (filter (schedule (list (list empty-s g)))))))

; (define run-OR
;   (lambda (and-el or-queue)
;     (let ((s (car and-el))
; 	  (thread (cadr and-el))
; 	  (and-queue (cddr and-el)))
;       (case-ans (thread s)
; 	(schedule or-queue) ; the whole AND thread is terminated
; 	((s^) (if (null? and-queue)
; 		; we found the answer!
; 		(cons s^ (lambda () (schedule or-queue)))
; 		(let ((or-queue (append or-queue (list (cons s^ and-queue)))))
; 		  (schedule or-queue))))
; 	((a f1 f2)			; have to split the AND el
; 	  (let* ((e1 (cons a (append and-queue (list f1))))
; 		 (e2 (cons a (append and-queue (list f2))))
; 		 (or-queue (append or-queue (list e1 e2))))
; 	    (schedule or-queue)))
; 	((b g1 g2)
; 	  (let* ((e (cons b (append and-queue (list g1 g2))))
; 		 (or-queue (append or-queue (list e))))
; 	    (schedule or-queue)))))))


(define-syntax run
  (syntax-rules ()
    ((_ n^ (x) g0 g ...)
     (let ((x (var 'x)) (n n^))
       (cond
         ((zero? n) (quote ()))
         (else
           (rn x (all g0 g ...) (prefix n))))))))

(define-syntax run-1
  (syntax-rules ()
    ((_ n^ depth (x) g0 g ...)
     (let ((x (var 'x)) (n n^))
       (cond
         ((zero? n) (quote ()))
         (else
           (rn x (all g0 g ...) (prefix-1 depth n))))))))



; Converting streams to lists
(define prefix*
  (lambda (r)
    (cond
      ((procedure? r) (prefix* (r depth-quantum)))
      (r (cons (car r) (prefix* (cdr r))))
      (else '()))))

(define prefix                   
  (lambda (n)
    (lambda (r)
      (cond
	((procedure? r) ((prefix n) (r depth-quantum)))
	(r
	  (cons (car r)
	    (cond 
	      ((= n 1) (quote ()))
	      (else 
		((prefix (- n 1)) (cdr r))))))
	(else '())))))

; depth-limited: essentially the engine

(define prefix-1                 
  (lambda (depth n)
    (lambda (r)
      (cond
	((not r) '())
        ((pair? r)
         (cons (car r)
           (cond 
             ((= n 1) (quote ()))
             (else 
               ((prefix-1 depth (- n 1)) (cdr r))))))
	(else
	  (if (positive? depth) ((prefix-1 (- depth 1) n) (r depth-quantum))
           '())) ; out of depth... return something else?
))))

; Kanren combinators

(define-syntax all
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (let ((g^ g0))
       (lambdag@ (n s andq orq) ((seq g^ (all g ...)) n s andq orq))))))

(define ==
  (lambda (v w)
    (lambdag@ (n s a o)
      (cond
        ((unify v w s) => (lambda (s) (succeed n s a o)))
        (else (fail n s a o))))))

(define ==-check
  (lambda (v w)
    (lambdag@ (n s a o)
      (cond
        ((unify-check v w s) => (lambda (s) (succeed n s a o)))
        (else (fail n s a o))))))


(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (n s a o)
       (let ((x (var 'x)) ...)
         ((all g0 g ...) n s a o))))))

(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g0 g ...)  
     (lambdag@ (n s a o)
       (begin (display s) (newline)
       (let ((x (walk* x s)) ...)
         ((all g0 g ...) n s a o)))))))

(define-syntax conde
  (syntax-rules (else)
    ((_) fail)
    ((_ (else g ...)) (all g ...))
    ((_ (g ...) c ...)
     (let ((g^ (all g ...)))
       (lambdag@ (n s a o) ((choice g^ (conde c ...)) n s a o))))))

(define-syntax condi
  (syntax-rules ()
    ((_ c ...) (conde c ...))))

(define-syntax chop1
  (syntax-rules ()
    ((chop1 r s) (succeed s))))

(define-syntax condu
  (syntax-rules ()
    ((_ c ...) (c1 chop1 c ...))))

(define-syntax chopo
  (syntax-rules ()
    ((chopo r s) r)))

(define-syntax conda
  (syntax-rules ()
    ((_ c ...) (c1 chopo c ...))))

; for committed choice, wait until incomplete is completed
(define-syntax c1
  (syntax-rules (else)
    ((_ chop) fail)
    ((_ chop (else g ...)) (all g ...))
    ((_ chop (g0 g ...) c ...)
      (error "not implemented yet"))))

(define-syntax alli
  (syntax-rules ()
    ((_ . args) (all . args))))

; Just the lambda...
(define-syntax lambda-limited
  (syntax-rules ()
    ((_ n formals g)                                          
       (lambda formals g))))

(define once
  (lambda (g)
    (condu (g succeed) (else fail))))


(define (yield) #f)

