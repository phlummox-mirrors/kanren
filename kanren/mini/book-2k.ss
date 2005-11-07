; Hello!

; 	I have re-written all of your tagging, in, hopefully a
; principled way. My tagging is stronger -- I found a type error in your
; tagging (in alli and condi). The `type system' so to speak keeps track
; of what is applied to what and how many times. To be more precise, the
; type system keeps track of partial applications and repeated
; abstractions. In logical terms, it handles a series of implication
; elimination and introduction rules. Although tags are checked at
; run-times, there is a compile-time aspect of the system (e.g., dealing
; with 'unit and 'answer types). I'm including the whole
; appendcode.ss. Hopefully you keep all of that versioned? The s.scm
; test passed.

; 	Happy Holiday!
; 	Oleg

(load "minikanrensupport.scm")

(define prefix
  (lambda (n v*)
    (cond
      ((null? v*) '())
      (else
        (cons (car v*)
          (cond
            ((= n 1) '())
            (else
              (prefix (- n 1) ((cdr v*))))))))))

(define prefix*
  (lambda (v*)
    (cond
      ((null? v*) '())
      (else
        (cons (car v*)
          (prefix* ((cdr v*))))))))

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
;; This is with all run-time tag-checking removed.
'(define-syntax tag+
  (syntax-rules (answer)
    ((_ (answer) body) body)
    ((_ tag body) body)))

'(define-syntax tag-
  (syntax-rules (answer)
    ((_ (answer) body) body)
    ((_ tag body) body)))

; The following two macros do essentially implication introduction and
; elimination.  To be more precise, a _series_ of implication
; introductions, or a series of implication eliminations.

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
    	(lambda-tagged "rem" (tag tags ...) (args ...) body)))))

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
    	(tag- (tag tags ...) body)))))

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

(define-syntax lambdaj@
  (syntax-rules ()
    ((_ args body) (lambda-tagged (subst semi-goal answer) args body))))

(define-syntax j@ 
  (syntax-rules ()
    ((_ body args ...) (app-tagged (subst semi-goal answer) body args ...))))

;;; This is the code exactly as it appears in the appnedix.
  
(define succeed (lambdag@ (s k) (k@ k s)))

(define fail (lambdag@ (s k f) (ff@ f)))

(define-syntax run
  (syntax-rules ()
    ((_ (x) g0 g ...)
     (let ((x (var 'x)))
       (rn x (g@ (all g0 g ...) empty-s))))))

(define rn
  (lambda (x r)
    (p@ (r@ r metak metaf)
      (lambdaj@ (s r)
        (cons (reify x s)
	  (lambda () (rn x r))))
      (lambdaf@ () '()))))

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
           (s (lambdar@ (k) (k@ k s)))
           (else
             (lambdar@ (k f) (ff@ f)))))))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (s)
       (let ((x (var 'x)) ...)
         (g@ (all g0 g ...) s))))))

(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g0 g ...)  
     (lambdag@ (s)
       (let ((x (reify-nonfresh x s)) ...)
         (g@ (all g0 g ...) s))))))

(define-syntax condo
  (syntax-rules ()
    ((_ c0 c ...) 
     (lambdag@ (s k f)
       (co s k f (lambda (r k f) (r@ r k f)) c0 c ...)))))

(define-syntax cond1
  (syntax-rules ()
    ((_ c0 c ...) 
     (lambdag@ (s k f)
       (co s k f (lambda (r k f) (ff@ f)) c0 c ...)))))

(define-syntax co
  (syntax-rules (else)
    ((_ s k f l (else g ...)) (g@ (all g ...) s k f))
    ((_ s k f l (g ...)) (g@ (all g ...) s k f))
    ((_ s k f l (g0 g ...) c0 c ...)
     (let ((f^ (lambdaf@ () (co s k f l c0 c ...)))
	   (g^ (all g ...)))
       (p@ (r@ (g@ g0 s) metak metaf)
         (lambdaj@ (s r)
	   (g@ g^ s k
	     (lambdaf@ () (l r (lambdak@ (s) (g@ g^ s k)) f))))
         f^)))))

(define once
  (lambda (g)
    (cond1
      [g]
      [else fail])))

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
  (lambda (r r^)
    (lambdar@ (k f)
      (p@ (r@ r metak metaf)
        (lambdaj@ (s r)
          (k@ k s
            (lambdaf@ ()
              (r@ (interleave r^ r) k f))))
        (lambdaf@ () (r@ r^ k f))))))

(define metak
  (lambdak@ (s f)
    (lambdap@ (j _f)
      (j@ j s
        (lambdar@ (k^ f^)
          (p@ (ff@ f)
            (lambdaj@ (s r)
              (k@ k^ s (lambdaf@ () (r@ r k^ f^))))
            f^))))))

(define metaf 
  (lambdaf@ ()
    (lambdap@ (_j f)
      (ff@ f))))

(define-syntax alli
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (lambdag@ (s) (ai (g@ g0 s) (alli g ...))))))

(define ai
  (lambda (r g)
    (lambdar@ (k f)
      (p@ (r@ r metak metaf)
        (lambdaj@ (s r)
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
          (else (lambdar@ (k f) (ff@ f))))))))

(define-syntax with-cut
  (syntax-rules ()
    ((_ fn) 
     (lambdag@ (s k f)
       (g@ (fn (wc (lambdag@ (_s _k _f) (ff@ f)))) s k f)))))

(define wc
  (lambda (g)
    (cond@
      (succeed)
      (g))))
