(load "minikanrensupport.scm")

; An attempt at complete and refutationally complete
; implementation
; The computation is an AND-OR tree, and each node of the tree
; is assuredly visited in finite time.

; data Ans a = Nil | Cons a (Int -> Ans a) | Incomplete (Int -> Ans a)

; a is the substitution;
;
; This implementation uses a ``final algebra'' -- or a threaded interpreter
; (aka the one in Forth) rather than an interpreter over a data structure.

; $Id$

(define depth-quantum 5)

; Two-level queue:
; type OR-queue = OrQ{backup-slot: [And-queue], anq = [And-queue]}
; data And-queue = And-queue Subst [Goal]
; type Goal = Limit -> Subst -> ANDqueue -> ORqueue -> Ans a
; The backup slot of the OR-queue may be either open or closed.
; The closed slot has #f at the top.
; The backup slot is a high-priority queue. Elements can be added only
; if the slot is open. When the slot is being drained, it is closed.

(define enq-first  cons)
(define (enq-first2 e1 e2 q) (cons e1 (cons e2 q)))
(define (enq-last  e q) (append q (list e)))
(define (enq-last2 e1 e2 q) (append q (list e1 e2)))

; Put an element into the backup slot, if open
(define (enq-prio e orq)
  (let ((backup-slot (car orq))
	(rest (cdr orq)))
    (if (and (pair? backup-slot) (eq? #f (car backup-slot)))
      (cons backup-slot (enq-last e rest))
      (cons (cons e backup-slot) rest)))) ; add to the backup slot


; constructor of a suspension: Limit -> Ans a
(define-syntax lambdaf@
  (syntax-rules ()
    ((_ (n) e) (lambda (n) e))))

; constructor of a goal: Limit -> Subst -> ANDqueue -> ORqueue -> Ans a
(define-syntax lambdag@
  (syntax-rules ()
    ((_ (n s andq orq) e) (lambda (n s andq orq) e))))

; Drain the backup slot if non-empty. If the new element is taken from
; the backup slot, close the slot.

(define (launch n ande orq)
  (let ((s (car ande)) (andq (cdr ande)))
    ((car andq) n s (cdr andq) orq)))


(define schedule
  (lambda (orq)
      ;(display "orq len: ") (display (length orq)) (newline)
    (lambdaf@ (n)
      (let ((backup-slot (car orq))
	    (rest (cdr orq)))
	(cond
	  ((null? backup-slot)
	    (and (pair? rest) (launch n (car rest) (cons '() (cdr rest)))))
	  ((eq? (car backup-slot) #f)	  ; closed slot
	    (if (null? (cdr backup-slot)) ; fully drained
	      (and (pair? rest) (launch n (car rest) (cons '() (cdr rest))))
	      (launch n (cadr backup-slot) ; drain the slot, keeping it closed
		(cons (cons #f (cddr backup-slot)) rest))))
	  (else
	    (launch n (car backup-slot)
	      (cons (cons #f (cdr backup-slot)) rest))))))))



; Kanren implementation
(define succeed 
  (lambdag@ (n s andq orq)
    (if (null? andq)		; we have the answer
      (cons s (schedule orq))
      ; Run the rest of the andq
      (let ((h (car andq)) (andq (cdr andq)))
	(h (+ n 1) s andq orq)))))

(define fail 
  (lambdag@ (n s andq orq)
    (schedule orq))) 		   ; schedule an alternative, if any


; ((G1 & G2) & AndQ) | OrQ
(define seq
  (lambda (g1 g2)
    (lambdag@ (n s andq orq)
      (if (positive? n)			; positive balance: run depth-first
	(g1 (- n 1) s (enq-last g2 andq) orq)
	(schedule (enq-last (cons s (enq-last2 g1 g2 andq)) orq))))))

; ((G1 | G2) & AndQ) | OrQ
; neither g1 nor g2 can split right away, so we enqueue them first
(define choice*
  (lambda (g1 g2)
    (lambdag@ (n s andq orq)
      (if (positive? n)			; positive balance: run depth-first
	(g1 (- n 1) s andq (enq-prio (cons s (enq-last g2 andq)) orq))
	(let ((ande1 (cons s (enq-first g1 andq)))
	      (ande2 (cons s (enq-first g2 andq))))
	  (schedule (enq-prio ande2 (enq-last ande1 orq))))))))

; The first time around, don't execute the choice, merely suspend it.
; Let other AND threads to run, if any.
(define choice
  (lambda (g1 g2)
    (lambdag@ (n s andq orq)
      (if (null? andq) ((choice* g1 g2) n s andq orq)
	(let ((ande1 (car andq))
	      (andq 			; enque the suspended choice point
		(enq-last 
		  (lambdag@ (n s andq orq) ((choice* g1 g2) n s andq orq))
		  (cdr andq))))
	  (ande1 n s andq orq))))))


(define-syntax run*
  (syntax-rules ()
    ((_ (x) g0 g ...)
     (let ((x (var 'x)))
       (rn x (all g0 g ...) prefix*)))))

(define rn
  (lambda (x g filter)
    (map (lambda (s) (reify x s)) 
      (filter (schedule (list '() (list empty-s g)))))))

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

