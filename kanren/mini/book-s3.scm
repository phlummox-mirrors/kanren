(load "minikanrensupport.scm")

; Stream implementation

; data Ans a = Zero | One a | Choice a a (a->Ans a)
; Here, in (Choice x s f): x is the current answer,
; (f s) will give further answers

(define mzero (vector 'mzero)) ; with an eye for many cuts

(define mzero? vector?)

(define-syntax one			; just the identity
  (syntax-rules ()
    ((one x) x)))

(define-syntax choice
  (syntax-rules ()
    ((choice x s f) (cons f (cons x s)))))

; Deconstructor
(define-syntax case-ans
  (syntax-rules ()
    ((case-ans e on-zero ((r) on-one) ((x s f) on-choice))
     (let ((r e))
       (cond
	 ((mzero? r) on-zero)
	 ((and (pair? r) (procedure? (car r)))
	  (let ((f (car r)) (x (cadr r)) (s (cddr r))) on-choice))
	 (else on-one))))))


(define unit
  (lambda (x) (one x)))

; bind m k = case m of
;              Zero -> Zero
;              One s -> k s
;              Choice a s k' -> mplus s (k a) (\s. (k' s) `bind` k)

(define bind
  (lambda (m k)
    (case-ans m
      mzero
      ((r) (k r))
      ((a s k1) (mplus s (k a) (lambda (s) (bind (k1 s) k)))))))

; mplus:: a -> Ans a -> (a-> Ans a)
; mplus s sg g =
;     case sg1 of
;              Zero -> g s
;              One s' -> Choice s' s g
;              Choice a s' k' -> Choice a s' (\s'. mplus s (k' s') g)
; The last step is the rotation of the tree

(define mplus
  (lambda (s sg1 g)
    (case-ans sg1
      (g s)
      ((r) (choice r s g))
      ((a s1 k1) (choice a s1 (lambda (s1) (mplus s (k1 s1) g)))))))

; mplus':: a -> Ans a -> (a-> Ans a)
; mplus' s sg g =
;     case sg1 of
;              Zero -> g s
;              One s' -> Choice s' s g
;              Choice a s' k' -> Choice a s (\s. mplus' s' (g s) k')
; The last step is the rotation of the tree

(define interleave
  (lambda (s sg1 g)
    (case-ans sg1
      (g s)
      ((r) (choice r s g))
      ((a s1 k1) (choice a s (lambda (s) (interleave s1 (g s) k1)))))))


; Kanren implementation
(define succeed unit)
(define fail (lambda (s) mzero))

(define-syntax run
  (syntax-rules ()
    ((_ (x) g0 g ...)
     (let ((x (var 'x)))
       (rn x empty-s (all g0 g ...))))))

(define (rn x s g)
  (case-ans (g s)
    '()
    ((r) (list (reify x r)))
    ((a s f) (cons (reify x a) (lambda () (rn x s f))))))

(define-syntax all
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (let ((g^ g0))
       (lambda (s) (bind (g^ s) (lambda (s) ((all g ...) s))))))))

(define ==
  (lambda (v w)
    (lambda (s)
      (cond
        ((unify v w s) => unit)
        (else (fail s))))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (let ((x (var 'x)) ...)
       (all g0 g ...)))))

(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g0 g ...)  
     (lambda (s)
       (let ((x (reify-nonfresh x s)) ...)
         ((all g0 g ...) s))))))

(define-syntax cond@
  (syntax-rules ()
    ((_ c ...) (c@ mplus c ...))))

(define-syntax condi
  (syntax-rules ()
    ((_ c ...) (c@ interleave c ...))))

(define-syntax c@
  (syntax-rules (else)
    ((_ combine) fail)
    ((_ combine (else g ...)) (all g ...))
    ((_ combine (g ...)) (all g ...))
    ((_ combine (g ...) c ...)
     (let ((g^ (all g ...)))
       (lambda (s) (combine s (g^ s) (c@ combine c ...)))))))

(define-syntax cond1
  (syntax-rules ()
    ((_ c ...)
     (let-syntax ((chop (syntax-rules ()
                          ((chop a s r k) (k a)))))
       (c1 chop c ...)))))

(define-syntax condo
  (syntax-rules ()
    ((_ c ...)
     (let-syntax ((chop (syntax-rules ()
                          ((chop a s r k) 
			    (bind (mplus s (unit a) r) k)))))		   
       (c1 chop c ...)))))

(define-syntax c1
  (syntax-rules (else)
    ((_ chop) fail)
    ((_ chop (else g ...)) (all g ...))
    ((_ chop (g0 g ...))
     (let ((g^ g0))
       (lambda (s)
	 (case-ans (g^ s)
	   mzero                 ; g0 failed
	   ((r) ((all g ...) r)) ; g0 is deterministic
	   ((a s f)		 ; at least one answer from g0
	     (chop a s f (all g ...)))))))
    ((_ chop (g0 g ...) c ...)
     (let ((g^ g0))
       (lambda (s)
	 (case-ans (g^ s)
	   ((c1 chop c ...) s)   ; g0 failed
	   ((r) ((all g ...) r)) ; g0 is deterministic
	   ((a s f)		 ; at least one answer from g0
	     (chop a s f (all g ...)))))))))

(define-syntax alli
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (let ((g^ g0))
       (lambda (s)
         (ai s g^
             (lambda (s) ((alli g ...) s))))))))

(define ai
  (lambda (s g1 g)
    (case-ans (g1 s)
      mzero
      ((s1) (g s1))
      ((a s2 f)
	(interleave s2 (g a) (lambda (s) (ai s f g)))))))

(define-syntax lambda-limited
  (syntax-rules ()
    ((_ n formals g)                                          
     (let ((x (var 'x)))                                                      
       (lambda formals (ll n x g))))))

(define ll
  (lambda (n x g)
    (lambda (s)
      (let ((v (walk-var x s)))
        (cond
          ((var? v) (g (ext-s x 1 s)))
          ((< v n)  (g (ext-s x (+ v 1) s)))
          (else (fail s)))))))

; Converting streams to lists

(define prefix*
  (lambda (r)
    (cond
      ((null? r) r)
      ((null? (cdr r)) r)
      (else (cons (car r) (prefix* ((cdr r))))))))


(define prefix
  (lambda (n r)
    (cond
      ((zero? n) '())
      ((null? r) '())
      ((procedure? r) (prefix n (r)))
      ((null? (cdr r)) r)
      (else 
	(cons (car r)
	  (prefix (- n 1) (cdr r)))))))
