(load "minikanrensupport.scm")

; Stream implementation, with incomplete

; data Ans a = Zero | Unit a | Choice a (() -> Ans a)
;                   | Incomplete (() -> Ans)
; In (Choice a f): a is the current answer; (f) will give further
; answers

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

(define-syntax incomplete
  (syntax-rules ()
    ((_ e) (lambdaf@ () e))))

(define-syntax incomplete-f		; if already a suspension
  (syntax-rules ()
    ((_ f) f)))

; Deconstructor
(define-syntax case-ans
  (syntax-rules ()
    ((_ e on-zero ((a^) on-one) ((a f) on-choice)
       ((i) on-incomplete))
     (let ((r e))
       (cond
         ((not r) on-zero)
	  ((procedure? r) (let ((i r)) on-incomplete))
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
; actually, should try r one more time...
;              Incomplete r -> Incomplete $ \() -> (bind (r ()) k)

(define bind
  (lambda (r k)
    (case-ans r
      (mzero)
      ((a) (k a))
      ((a f) (mplus (k a) (lambdaf@ () (bind (f) k))))
      ((i) (incomplete (bind (i) k)))
      )))

; mplus:: Ans a -> (() -> Ans a) -> Ans a
; mplus r f =
;     case r of
;              Zero -> Incomplete f
;              Unit a -> Choice a f
;              Choice a f' -> Choice a (\() -> mplus (f' ()) f)
;              Incomplete i -> Incomplete $ \() -> mplus (i ()) f
; The last but one step is the rotation of the tree

(define mplus
  (lambda (r f)
    (case-ans r
      (incomplete-f f)
      ((a) (choice a f))
      ((a f^) (choice a
                (lambdaf@ () (mplus (f^) f))))
      ((i) (incomplete (mplus (i) f)))
)))


; interleave :: Ans a -> (() -> Ans a) -> Ans a
; interleave r f =
;     case r of
;              Zero -> Incomplete f
;              Unit a -> Choice a f
;              Choice a f' -> Choice a (\() -> interleave (f ()) f')
; The last step is the rotation of the tree
;
; The algebra of incomplete: from SRIReif.hs
;     compose_trees' HZero r = return $ Incomplete r
;     compose_trees' (HOne a) r = return $ HChoice a r
;			      -- Note that we do interleave here!
;     compose_trees' (HChoice a r') r =
;     return $ HChoice a (compose_trees r r')
;		       -- t1 was incomplete. Now try t2
;     compose_trees' (Incomplete r) t2 = 
;     do { t2v <- t2; return $ compose_trees'' r t2v }

;     compose_trees'' r HZero    = Incomplete r
;     compose_trees'' r (HOne a)  = HChoice a r
;			      -- Note that we do interleave here!
;     compose_trees'' r (HChoice a r') = HChoice a (compose_trees r' r)
;				 -- Both tree are incomplete. Suspend
;     compose_trees'' r (Incomplete t2) = Incomplete (compose_trees r
;     t2)

; aka interleave-reset
(define interleave-reset
  (lambda (r f)
    (case-ans r
      (incomplete-f f)
      ((a) (choice a f))
      ((a f^) (choice a
                (lambdaf@ () (interleave (f) f^))))
      ((i)
      (case-ans (f)
        (incomplete-f i)
	  ((b) (choice b i))
;	    ((b f^^) (incomplete (interleave (i) f)))
;	      ((b f^^)
;	          (case-ans (i)
;		        (choice b f^^)
;			      ((a1) (choice a1 (lambdaf@ ()
;					 (choice b f^^))))
;					    ((a1 f^1) (choice a1 (lambdaf@ ()
;			     (choice b
;				   (lambdaf@ () (interleave (f^1) f^^))))))
;	          ((i1) (choice b (lambdaf@ () (interleave (i1) f^^))))))
	  ((b f^^) (choice b (lambdaf@ () (interleave (i) f^^))))
;	    ((b f^^) (choice b (lambdaf@ () (interleave (f^^) i))))
	      ((j) (incomplete (interleave (i) j)))))
)))


(define interleave ;-shift
  (lambda (r f)
    (case-ans r
      (incomplete-f f)
      ((a) (choice a f))
      ((a f^) (choice a
                (lambdaf@ () (interleave (f) f^))))
      ((i)
      (case-ans (f)
        (incomplete-f i)
	  ((b) (choice b i))
	    ((b f^^) (incomplete (interleave (choice b f^^) i)))
	      ((j) (incomplete (interleave (i) j)))))
)))

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
      (filter (g empty-s)))))

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
    (case-ans r
      (quote ())
      ((v) (cons v (quote ())))
      ((v f) (cons v (prefix* (f))))
      ((i) (prefix* (i)))
      )))

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
               ((prefix (- n 1)) (f))))))
      ((i) ((prefix n) (i)))
))))

; depth-limited: essentially the engine

(define prefix-1                 
  (lambda (depth n)
    (lambda (r)
      (case-ans r                       
        (quote ())
        ((s) (cons s (quote ())))
        ((s f)
         (cons s
           (cond 
             ((= n 1) (quote ()))
             (else 
               ((prefix-1 depth (- n 1)) (f))))))
      ((i) (if (positive? depth) ((prefix-1 (- depth 1) n) (i))
           '())) ; out of depth... return something else?
))))

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
       (lambdag@ (s) (combine (g^ s) (lambdaf@ () ((c@ combine c ...)
  s))))))))

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
     (let ((g^ g0))
       (lambdag@ (s)
         (let loop ((r (g^ s)))
           (case-ans r
             (incomplete ((c1 chop c ...) s))   ; g0 failed
             ((s) ((all g ...) s)) ; g0 is deterministic
             ((s f)                ; at least one answer from g0
              (bind (chop r s) (lambdag@ (s) ((all g ...) s))))
	           ((i) (incomplete (loop (i))))
)))))))

(define-syntax alli
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (let ((g^ g0))
       (lambdag@ (s) (bindi (g^ s) (lambdag@ (s) ((alli1 g ...)
  s))))))))

(define-syntax alli1
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (let ((g^ g0))
       (lambdag@ (s) (bindi1 (g^ s) (lambdag@ (s) ((alli1 g ...)
  s))))))))

(define bindi
  (lambda (r k)
    (case-ans r
      (mzero)
      ((a) (k a))
      ((a f) (interleave-reset (k a)
               (lambdaf@ () (bindi (f) k))))
      ((i) (incomplete (bindi (i) k)))
)))

(define bindi1
  (lambda (r k)
    (case-ans r
      (mzero)
      ((a) (k a))
      ((a f) (interleave (k a)
               (lambdaf@ () (bindi1 (f) k))))
      ((i) (incomplete (bindi1 (i) k)))
)))


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

(define-syntax allw
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g1 g2) (allw-1 g1 g2))
    ((_ g0 g1 g2 ...) (allw (allw g0 g1) g2 ...))))

(define allw-1
  (lambda (g1 g2)
    (fresh (choice failed)                                                   
      (all
        (oracle g1 g2 failed choice)
        (condu
          ((== #t failed) fail)
          ((== #t choice) (alli g1 g2))                                      
          ((== #f choice) (alli g2 g1)))))))                    

;;; If 'g' succeeds or fails, then (terminates failed g) succeeds,
;;; and in the process sets failed to #t if g fails and sets failed
;;; to #f if g succeeds, but without extending the substitution.
;;; If 'g' diverges, (terminates failed g) diverges.

(define oracle
  (lambda (g1 g2 failed choice)
    (once
      (condi
        ((terminates failed (alli g1 g2)) (== #t choice))              
        ((terminates failed (alli g2 g1)) (== #f choice))))))

(define terminates
  (lambda (failed g)
    (condu
      ((succeeds
         (condu
           [g succeed]
           [else fail]))
       (== #f failed))
      (else (== #t failed)))))

(define succeeds
  (lambda (g)
    (fails (fails g))))

(define fails
  (lambda (g)
    (condu [g fail] [else succeed])))

(define once
  (lambda (g)
    (condu [g succeed] [else fail])))

