(load "minikanrensupport.scm")

; Stream implementation

; data Ans a = Zero | Unit a | Choice a (() -> Ans a)
; In (Choice a f): a is the current answer; (f) will give further answers

; Constructors
(define-syntax mzero
  (syntax-rules ()
    ((_) #f)))

(define-syntax unit                        ; just the identity
  (syntax-rules ()
    ((_ a) a)))

(define-syntax choice
  (syntax-rules ()
    ((_ a f) (cons a f))))

; Deconstructor
(define-syntax case-ans
  (syntax-rules ()
    ((_ e on-zero ((a^) on-one) ((a f) on-choice))
     (let ((r e))
       (cond
         ((not r) on-zero)
         ((and (pair? r) (procedure? (cdr r)))
          (let ((a (car r)) (f (cdr r)))
            on-choice))
         (else (let ((a^ r)) on-one)))))))


; constructor of a suspension: () -> Ans a
(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

; constructor of a goal: Subst -> Ans a
(define-syntax lambdag@
  (syntax-rules ()
    ((_ (s) e) (lambda (s) e))))

; bind r k = case r of
;              Zero -> Zero
;              Unit a -> k a
;              Choice a f -> mplus (k a) (\() -> bind (f ()) k)

(define bind
  (lambda (r k)
    (case-ans r
      (mzero)
      ((a) (k a))
      ((a f) (mplus (k a) (lambdaf@ () (bind (f) k)))))))

; mplus:: Ans a -> (() -> Ans a) -> Ans a
; mplus r f =
;     case r of
;              Zero -> f ()
;              Unit a -> Choice a f
;              Choice a f' -> Choice a (\() -> mplus (f' ()) f)
; The last step is the rotation of the tree

(define mplus
  (lambda (r f)
    (case-ans r
      (f)
      ((a) (choice a f))
      ((a f^) (choice a
                (lambdaf@ () (mplus (f^) f)))))))


; interleave :: Ans a -> (() -> Ans a) -> Ans a
; interleave r f =
;     case r of
;              Zero -> f ()
;              Unit a -> Choice a f
;              Choice a f' -> Choice a (\() -> interleave (f ()) f')
; The last step is the rotation of the tree

(define interleave
  (lambda (r f)
    (case-ans r
      (f)
      ((a) (choice a f))
      ((a f^) (choice a
                (lambdaf@ () (interleave (f) f^)))))))


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
      (filter (g (ext-s x x empty-s))))))

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
    (case-ans r
      (quote ())
      ((v) (cons v (quote ())))
      ((v f) (cons v (prefix* (f)))))))

(define prefix                   
  (lambda (n)
    (lambda (r)
      (case-ans r                       
        (quote ())
        ((s) (cons s (quote ())))
        ((s f)
         (cons s
           (cond 
             ((= n 1) (quote ()))
             (else 
               ((prefix (- n 1)) (f))))))))))

; Kanren combinators

(define-syntax all
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (let ((g^ g0))
       (lambdag@ (s) (bind (g^ s) (lambdag@ (s) ((all g ...) s))))))))

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
	 (let* ((s (ext-s x x s)) ...)
	   ((all g0 g ...) s)))))))

(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g0 g ...)  
     (lambdag@ (s)
       (let ((x (walk* x s)) ...)
         ((all g0 g ...) s))))))

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
       (lambdag@ (s) (combine (g^ s) (lambdaf@ () ((c@ combine c ...) s))))))))

(define-syntax chop1
  (syntax-rules ()
    ((chop1 r s) (succeed s))))

(define-syntax condu
  (syntax-rules ()
    ((_ c ...) (c1 chop1 c ...))))

(define-syntax chopo
  (syntax-rules ()
    ((chopo r s) r)))

(define-syntax condo
  (syntax-rules ()
    ((_ c ...) (c1 chopo c ...))))

(define check-groundness
  (lambda (s)
    (lambda (s1)
      (if (eq? s s1) (unit s)
	(begin
	  (display "possible violation of safety in conda/condu")
	  (newline)
	  (unit s1))))))
  
(define-syntax c1
  (syntax-rules (else)
    ((_ chop) fail)
    ((_ chop (else g ...)) (all g ...))
    ((_ chop (g0 g ...) c ...)
     (let ((g^ g0))
       (lambdag@ (s)
         (let ((r (g^ s)) (checker (check-groundness s)))
           (case-ans r
             ((c1 chop c ...) s)   ; g0 failed
             ((s) (bind (checker s) (all g ...))) ; g0 is deterministic
             ((s f)                ; at least one answer from g0
              (bind (chop r s)
		(lambdag@ (s)
		  (bind (checker s)
		    (lambdag@ (s) ((all g ...) s)))))))))))))

(define-syntax alli
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (let ((g^ g0))
       (lambdag@ (s) (bindi (g^ s) (lambdag@ (s) ((alli g ...) s))))))))

(define bindi
  (lambda (r k)
    (case-ans r
      (mzero)
      ((a) (k a))
      ((a f) (interleave (k a)
               (lambdaf@ () (bindi (f) k)))))))

(define-syntax lambda-limited
  (syntax-rules ()
    ((_ n formals g)                                          
     (let ((x (var 'x)))                                                      
       (lambda formals (ll n x g))))))

(define ll
  (lambda (n x g)
    (lambdag@ (s)
      (let ((v (walk x s)))
        (cond
          ((var? v) (g (ext-s x 1 s)))
          ((< v n)  (g (ext-s x (+ v 1) s)))
          (else (fail s)))))))


; The following implementation of eigen critically depends on:
;  -- the presence of birth records for logical variables in substitution 's'
;  -- unification with the occurs check but which
;     does eq? check of its arguments first.
; These conditions and the following implementation guarantee:
;   an eigen variable is equal (unifiable) to itself
;   an eigen variable cannot be unified with a fresh variable
;     created _before_ the eigen variable. This is because the birth
;     record of the logical variable will be in 's', which is the part of
;     the eigen value. So, unification triggers the occurs check.
;   an eigen variable is unifiable with a fresh variable created after
;     eigen.
;   an eigen variable is not unifiable with anything else [but see below].
;
; The idea of this implementation has been suggested by Chung-chieh Shan.
;
; An alternative implementation for eigen will use death records --
; or delayed occurs check.


; Alas, there is a drawback:
;   (run 1 (q) (eigen (x) (fresh (u v) (==-check x (cons u v)))))
; succeeds, and so does
;   (run 1 (q) (eigen (x) (fresh (v) (==-check x (cons q v)))))
;
; They mean, logically,
; 	forall x. exists u v. x = (u . v)
; 	exists u. forall x. exists v. x = (u . v)
;
; which isn't particularly meaningful. It seems that any solution that
; relies on the occurs check must have this unfortunate
; property. Indeed, in order to trigger the occurs check, the
; representation of an eigen variable must be traversable by the
; unifier. That means, it can be unified with another traversable value
; of the similar structure.

; (define-syntax eigen
;   (syntax-rules ()
;     ((_ (x ...) g0 g ...)
;      (lambdag@ (s)
;        (let ((x (cons (gensym) s)) ...)
; 	   ((all g0 g ...) s))))))


; The following implementation realizes an eigen variable as a non-traversable
; value. In that case, we don't need to change the unifier, and we don't need
; to rely on the occurs check. I could have used a string, e.g.,
; (symbol->string (gensym)) or 
; (string-append "varname" (number->string (length s)))
; In the latter case, eigen must extend the substitution, just to change
; its length.
; Instead, we use a procedure, which is a truly opaque value.
; The following implementation is also lazy in its check: we catch an attempt
; to bind an eigenvariable to a logical variable of the outer scope not
; at the place of unification but at the exit from the eigen form: when
; the eigen variable is about to escape.
; Does lambda-prolog do something similar?
;
; The check scans all bindings that are made after the entrance to
; eigen.  If we found an assoctiation xi -> ti such that ti contains
; the eigen variable but xi's birth record is in the part of the
; substitution before eigen, we fail.

(define-syntax eigen
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (s)
       (let ((x (lambda () (list 'x))) ...) ; A unique value ...
	 (bind ((all g0 g ...) s)
	   (lambda (s1) (check-eigen s s1 (list x ...)))))))))

; Test that all bindings within substitution prefix [s0..s1] are proper
; with respect to each of the eigenvariables x0 ... 
; We rely on the fact that any binding to a logical
; variable may only occur after that variable's birth record.

(define check-eigen
  (lambda (s0 s1 eigens)
    (let ((local-vars (find-created-vars s0 s1)))
      (let loop ((sc s1))
	(if (eq? sc s0) (succeed s1)
	  (let ((binding (car sc)) (sc (cdr sc)))
	    (cond
	      ((memq (lhs binding) local-vars) (loop sc))
	      ((occur? eigens (rhs binding)) (fail s1))
	      (else (loop sc)))))))))


; Scan the substitution prefix [s0..s1] and find all logical variables
; (by their birth record) that were created within that prefix.
; Return them in a list

(define find-created-vars
  (lambda (s0 s1)
    (cond 
      ((eq? s0 s1) '())
      ((unbound-binding? (car s1))
	(cons (lhs (car s1)) (find-created-vars s0 (cdr s1))))
      (else (find-created-vars s0 (cdr s1))))))



; check to see if any of the terms in patterns occur within `term'
(define occur?
  (lambda (patterns term)
    (or (memq term patterns)
      (and (pair? term) (or (occur? patterns (car term))
			    (occur? patterns (cdr term)))))))
