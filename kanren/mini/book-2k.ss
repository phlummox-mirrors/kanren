(load "minikanrensupport.scm")

(define-syntax lambda@ 
  (syntax-rules () 
    ((_ () e) (lambda () e)) 
    ((_ (x) e) (lambda (x) e)) 
    ((_ (x0 x ...) e) 
     (lambda (x0) (lambda@ (x ...) e)))))

(define-syntax @  
  (syntax-rules () 
    ((_ h) (h)) 
    ((_ h e) (h e)) 
    ((_ h e0 e ...) 
     (@ (h e0) e ...))))

; Type representation
; Type constants
;  'subst
;  'sk
;  'fk
;  'answer
;  'unit
;  'goal
;  'semi-goal
; Arrow type: a->b is represented as (a b)
; Types are associated with lambdas and checked by applications

(define (tag-tag) tag-tag)
(define (make-tag tag body)
  (vector tag-tag tag body))
(define (assert-tag v expected-tag)
  (if (not
	(and (vector? v) (= 3 (vector-length v))
	  (eq? (vector-ref v 0) tag-tag)))
    (error 'untagged "~s, expected ~s" v expected-tag)))

(define (remove-tag tag expr)
  (assert-tag expr tag)
  (if (equal? (vector-ref expr 1) tag) (vector-ref expr 2)
    (error 'tag-mismatch "expected ~a, found ~a" tag (vector-ref expr 1))))

; Replace the following two macros tag+ and tag- to remove
; all run-time tag checking
(define-syntax tag+
  (syntax-rules (answer)
    ((_ (answer) body) body)
    ((_ tag body) (make-tag 'tag body))))

(define-syntax tag-
  (syntax-rules (answer)
    ((_ (answer) body) body)
    ((_ tag body) (remove-tag 'tag body))))

; The following two macros do essentially implication introduction
; and elimination.
; To be more precise, a _series_ of implication introductions,
; or a series of implication eliminations.

(define-syntax lambda-tagged
  (syntax-rules (answer unit)
    ((_ "rem" (answer) () body) body)
    ((_ "rem" (unit tags ...) () body)
      (lambda () (lambda-tagged "rem"  (tags ...) () body)))
    ((_ "rem" (tag tags ...) () body)
      (tag- (tag tags ...) body))
    ((_ "rem" (tag tags ...) (arg args ...) body)
      (lambda (arg) (lambda-tagged "rem"  (tags ...) (args ...) body)))
    ((_ (tag tags ...) (args ...) body)
      (tag+ (tag tags ...)
	(lambda-tagged "rem" (tag tags ...) (args ...) body)))
))

(define-syntax app-tagged
  (syntax-rules (answer unit)
    ((_ "rem" (answer) () body) body)
    ((_ "rem" (unit tags ...) () body)
      (app-tagged "rem"  (tags ...) () (body)))
    ((_ "rem" (tag tags ...) () body)
      (tag+ (tag tags ...) body))
    ((_ "rem" (tag tags ...) (arg args ...) body)
     (app-tagged "rem" (tags ...) (args ...) (body arg)))
    ((_ (tag tags ...) body args ...)
      (app-tagged "rem" (tag tags ...) (args ...) 
	(tag- (tag tags ...) body)))
))


(define-syntax lambdag@
  (syntax-rules ()
    ((_ args body) (lambda-tagged (subst sk fk answer) args body))))

(define-syntax g@
  (syntax-rules ()
    ((_ body args ...) (app-tagged (subst sk fk answer) body args ...))))


(define-syntax lambdar@
  (syntax-rules ()
    ((_ args body) (lambda-tagged (sk fk answer) args body))))

(define-syntax r@ 
  (syntax-rules ()
    ((_ body args ...) (app-tagged (sk fk answer) body args ...))))

(define-syntax lambdaa@
  (syntax-rules ()
    ((_ args body) (lambda-tagged (fk answer) args body))))

(define-syntax a@ 
  (syntax-rules ()
    ((_ body args ...) (app-tagged (fk answer) body args ...))))


(define-syntax lambdak@
  (syntax-rules ()
    ((_ args body) (lambda-tagged (subst fk answer) args body))))

(define-syntax k@
  (syntax-rules ()
    ((_ body args ...) (app-tagged (subst fk answer) body args ...))))

(define-syntax lambdaf@
  (syntax-rules ()
    ((_ args body) (lambda-tagged (unit answer) args body))))

(define-syntax ff@ 
  (syntax-rules ()
    ((_ body args ...) (app-tagged (unit answer) body args ...))))


(define-syntax lambdap@
  (syntax-rules ()
    ((_ args body) (lambda-tagged (goal fk answer) args body))))

(define-syntax p@ 
  (syntax-rules ()
    ((_ body args ...) (app-tagged (goal fk answer) body args ...))))

(define-syntax lambda-sr@
  (syntax-rules ()
    ((_ args body) (lambda-tagged (subst semi-goal answer) args body))))

(define-syntax sr@ 
  (syntax-rules ()
    ((_ body args ...) (app-tagged (subst semi-goal answer) body args ...))))


(define prefix
  (lambda (n v*)
    (cond
      ((null? v*) '())
      (else
        (cons (car v*)
          (cond
            ((= n 1) '())
            (else
              (prefix (- n 1)
                (a@ invoke-thunk (cdr v*))))))))))

(define prefix*
  (lambda (v*)
    (cond
      ((null? v*) '())
      (else
        (cons (car v*)
          (prefix* (a@ invoke-thunk (cdr v*))))))))


;;; This is the code exactly as it appears in the appnedix.
  
(define succeed (lambdag@ (s k) (k@ k s)))

(define fail (lambdag@ (s) r-invoke-thunk))

(define r-invoke-thunk (lambdar@ (k) invoke-thunk))

(define invoke-thunk (lambdaa@ (f) (ff@ f)))

(define-syntax run
  (syntax-rules ()
    ((_ (x) g0 g ...)
     (let ((x (var 'x)))
       (g@ (all g0 g ...) empty-s
         (lambdak@ (s f) (cons (reify x s) f))
         (lambdaf@ () '()))))))

(define-syntax all
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g ...) (lambdag@ (s k) (all-aux s k g ...)))))

(define-syntax all-aux
  (syntax-rules ()
    ((_ s k g) (g@ g s k))
    ((_ s k g0 g ...)
     (g@ g0 s (lambdak@ (s) (all-aux s k g ...))))))

(define-syntax ==
  (syntax-rules ()
    ((_ v w)
     (lambdag@ (s)
       (let ((s (unify v w s)))
         (cond
           ((not s) r-invoke-thunk)
           (else (lambdar@ (k) (k@ k s)))))))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g ...)
     (lambdag@ (s)
       (let ((x (var 'x)) ...)
         (g@ (all g ...) s))))))

(define-syntax project
  (syntax-rules ()                                                              
    ((_ (x ...) g ...)  
     (lambdag@ (s)
       (let ((x (reify-nonfresh x s)) ...)
         (g@ (all g ...) s))))))

(define-syntax condo
  (syntax-rules ()
    ((_ c0 c ...) 
     (lambdag@ (s k f) (co s k f c0 c ...)))))

(define-syntax co
  (syntax-rules (else)
    ((_ s k f (else g ...)) (g@ (all g ...) s k f))
    ((_ s k f (g ...)) (g@ (all g ...) s k f))
    ((_ s k w (g0 g ...) c0 c ...)
     (a@ (g@ g0 s
              (lambdak@ (s f^)
                (lambdaa@ (w^)
                  (g@ (all g ...) s k
                    (lambdaf@ () (a@ (ff@ f^) w)))))
              (lambdaf@ () invoke-thunk))
       (lambdaf@ () (co s k w c0 c ...))))))

(define-syntax once
  (syntax-rules ()
    ((_ g)
     (lambdag@ (s k f)
       (g@ g s (lambdak@ (s^ f^) (k@ k s^ f)) f)))))

(define-syntax cond@
  (syntax-rules ()
   ((_ c0 c ...) (lambdag@ (s k f) (c@ s k f c0 c ...)))))

(define-syntax c@
  (syntax-rules (else)
    ((_ s k f (else g ...)) (g@ (all g ...) s k f))
    ((_ s k f (g ...)) (g@ (all g ...) s k f))
    ((_ s k f (g ...) c ...)
     (g@ (all g ...) s k 
       (lambdaf@ () (c@ s k f c ...))))))

(define-syntax condi
  (syntax-rules ()
   ((_ c0 c ...) (lambdag@ (s) (ci s c0 c ...)))))

(define-syntax ci
  (syntax-rules (else)
    ((_ s (else g ...)) (g@ (all g ...) s))
    ((_ s (g ...)) (g@ (all g ...) s))
    ((_ s (g ...) c ...)
     (interleave (g@ (all g ...) s) (ci s c ...)))))

(define interleave
  (lambda (r1 r2)
    (lambdar@ (k f)
      (p@ 
	(r@ r1 anyi-k anyi-f)
        (lambda-sr@ (s r1)
          (k@ k s
            (lambdaf@ ()
              (r@ (interleave r2 r1) k f))))
        (lambdaf@ () (r@ r2 k f))))))

(define anyi-k
  (lambdak@ (s f)
    (lambdap@ (sg _)
      (sr@ sg s
        (lambdar@ (k1 f1)
          (p@ (ff@ f)
            (lambda-sr@ (s r)
              (k@ k1 s (lambdaf@ () (r@ r k1 f1))))
            f1))))))

(define anyi-f (lambdaf@ () (lambdap@ (_) invoke-thunk)))

(define-syntax alli
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (lambdag@ (s) (ai (g@ g0 s) (alli g ...))))))

(define ai
  (lambda (r g)
    (lambdar@ (k f)
      (p@ (r@ r anyi-k anyi-f)
        (lambda-sr@ (s r)
          (r@ (interleave (g@ g s) (ai r g))
            k f))
        f))))

(define-syntax lambda-limited
  (syntax-rules ()                                                              
    ((_ n formals g)                                          
     (let ((x (var 'x)))                                                      
       (lambda formals (ll n x g))))))

(define ll
  (lambda (n x g)
    (lambdag@ (s)
      (let ((v (walk-var x s)))
        (cond
          ((var? v) (g@ g (ext-s x 1 s)))
          ((< v n)  (g@ g (ext-s x (+ v 1) s)))
          (else r-invoke-thunk))))))

(define with-cut
  (lambda (fn)
    (lambdag@ (s k f)
      (g@ (fn (wc (lambdag@ (s^ k^ f^) (ff@ f)))) s k f))))
