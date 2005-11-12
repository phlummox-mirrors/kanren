(load "minikanrensupport.scm")

; An attempt at complete and refutationally complete
; implementation
; The computation is an AND-OR tree, and each node of the tree
; is assuredly visited in finite time.

; data Ans a = Zero | Unit a | Choice a (a -> Ans a) (a -> Ans a)
;                   | Seq  a (a -> Ans a) (a -> Ans a)
; a is the substitution;
; The two branches of Choice and Seq are the body of the corresponding
; OR (resp AND) nodes
;
; $Id$

; Constructors
(define-syntax mzero
  (syntax-rules ()
    ((_) #f)))

(define-syntax unit                        ; just the identity
  (syntax-rules ()
    ((_ a) a)))

(define-syntax choice
  (syntax-rules ()
    ((_ a f1 f2) (cons #f (cons a (cons f1 f2))))))

(define-syntax seq
  (syntax-rules ()
    ((_ a f1 f2) (cons #t (cons a (cons f1 f2))))))

; Deconstructor
(define-syntax case-ans
  (syntax-rules ()
    ((_ e on-zero 
       ((a^) on-one)
       ((a f1 f2) on-choice)
       ((b g1 g2) on-seq))
     (let ((r e))
       (cond
         ((not r) on-zero)
	 ((not (and (pair? r) (boolean? (car r))))
	   (let ((a^ r)) on-one))
	 ((car r)
	   (let ((b (cadr r)) (g1 (caddr r)) (g2 (cdddr r))) on-seq))
	 (else
	   (let ((a (cadr r)) (f1 (caddr r)) (f2 (cdddr r))) on-choice)))))))


; constructor of a suspension: () -> Ans a
(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

; constructor of a goal: Subst -> Ans a
(define-syntax lambdag@
  (syntax-rules ()
    ((_ (s) e) (lambda (s) e))))

; Kanren implementation
(define succeed (lambdag@ (s) (unit s)))
(define fail (lambdag@ (s) (mzero)))

(define-syntax run*
  (syntax-rules ()
    ((_ (x) g0 g ...)
     (let ((x (var 'x)))
       (rn x (all g0 g ...) prefix*)))))

(define rn
  (lambda (x g filter)
    (map (lambda (s) (reify x s)) 
      (filter (schedule (list (list empty-s g)))))))

; Two-level queue:
; type OR-queue = [And-queue]
; data And-queue = And-queue Subst [Goal]
; type Goal = Subst -> Ans Subst


(define schedule
  (lambda (or-queue)
    (and (pair? or-queue) (run-OR (car or-queue) (cdr or-queue)))))

(define run-OR
  (lambda (and-el or-queue)
    (let ((s (car and-el))
	  (thread (cadr and-el))
	  (and-queue (cddr and-el)))
      (case-ans (thread s)
	(schedule or-queue) ; the whole AND thread is terminated
	((s^) (if (null? and-queue)
		; we found the answer!
		(cons s^ (lambda () (schedule or-queue)))
		(let ((or-queue (append or-queue (list (cons s^ and-queue)))))
		  (schedule or-queue))))
	((a f1 f2)			; have to split the AND el
	  (let* ((e1 (cons a (append and-queue (list f1))))
		 (e2 (cons a (append and-queue (list f2))))
		 (or-queue (append or-queue (list e1 e2))))
	    (schedule or-queue)))
	((b g1 g2)
	  (let* ((e (cons b (append and-queue (list g1 g2))))
		 (or-queue (append or-queue (list e))))
	    (schedule or-queue)))))))


(define-syntax run
  (syntax-rules ()
    ((_ n^ (x) g0 g ...)
     (let ((x (var 'x)) (n n^))
       (cond
         ((zero? n) (quote ()))
         (else
           (rn x (all g0 g ...) (prefix n))))))))

; Converting streams to lists
(define prefix*
  (lambda (r)
    (if r
      (cons (car r) (prefix* ((cdr r))))
      '())))

(define prefix                   
  (lambda (n)
    (lambda (r)
      (if r
	(cons (car r)
	  (cond 
	    ((= n 1) (quote ()))
	    (else 
	      ((prefix (- n 1)) ((cdr r))))))
	'()))))

; Kanren combinators

(define-syntax all
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (let ((g^ g0))
       (lambdag@ (s) (seq s g^ (all g ...)))))))

(define ==
  (lambda (v w)
    (lambdag@ (s)
      (cond
        ((unify v w s) => succeed)
        (else (fail s))))))

(define ==-check
  (lambda (v w)
    (lambdag@ (s)
      (cond
        ((unify-check v w s) => succeed)
        (else (fail s))))))


(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (s)
       (let ((x (var 'x)) ...)
         ((all g0 g ...) s))))))

(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g0 g ...)  
     (lambdag@ (s)
       (begin (display s) (newline)
       (let ((x (walk* x s)) ...)
         ((all g0 g ...) s)))))))

(define-syntax conde
  (syntax-rules ()
    ((_ c ...) (c@ mplus c ...))))

(define-syntax condi
  (syntax-rules ()
    ((_ c ...) (c@ interleave c ...))))

(define-syntax c@
  (syntax-rules (else)
    ((_ combine) fail)
    ((_ combine (else g ...)) (all g ...))
    ((_ combine (g ...) c ...)
     (let ((g^ (all g ...)))
       (lambdag@ (s) (choice s g^ (c@ combine c ...)))))))

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

