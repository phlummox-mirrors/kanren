(load "minikanrensupport.scm")

; Stream implementation

(define mzero '())

(define mzero? null?)

(define-syntax thaw ; internal
  (syntax-rules ()
    ((_ r)
     (let ((r^ r))
       (cond
         ((mzero? r^) #f)
         (else (r^ mzero)))))
    ((_ r f)
     (let ((r^ r) (f^ f))
       (cond
         ((mzero? r^) (thaw f^))
         (else (r^ f^)))))))

(define-syntax open
  (syntax-rules ()
    ((_ e ((s r) e1) e2)
     (let ((p (thaw e)))
       (cond
         (p (let ((s (car p))
                  (r (cdr p)))
              e1))
         (else e2))))))

(define-syntax freeze
  (syntax-rules ()
    ((_ e) (lambda (f) (thaw e f)))))

(define mplus
  (lambda (r r^)
    (cond
      ((mzero? r) r^)
      ((mzero? r^) r)
      (else
        (lambda (f)
          (r (mplus r^ f)))))))

;;; (+= (cons a b) r) = (cons a (++ b r)), only in functional style.

(define unit
  (lambda (s)
    (lambda (f)
      (cons s f))))

(define bind
  (lambda (r k)
    (cond
      ((mzero? r) mzero)
      (else
        (lambda (f)
          (let ((p (r mzero)))
            (cond
              (p (thaw (mplus (k (car p))
                              (bind (cdr p) k))
                       f))
              (else (thaw f)))))))))

; Kanren implementation

(define interleave
  (lambda (r r^)
    (cond
      ((mzero? r) r^)
      ((mzero? r^) r)
      (else
        (lambda (f)
          (let ((p (r mzero)))
            (cond
              (p (thaw (mplus (unit (car p))
                              (interleave r^ (cdr p)))
                       f))
              (else (thaw r^ f)))))))))

(define succeed unit)
(define fail (lambda (s) mzero))

(define-syntax run
  (syntax-rules ()
    ((_ (x) g0 g ...)
     (let ((x (var 'x)))
       (bind ((all g0 g ...) empty-s)
         (lambda (s) (unit (reify x s))))))))

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
        (else mzero)))))

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
       (lambda (s) (combine (g^ s) (freeze ((c@ combine c ...) s))))))))

(define-syntax chop1
  (syntax-rules ()
    ((chop s r k) (k s))))

(define-syntax cond1
  (syntax-rules ()
    ((_ c ...) (c1 chop1 c ...))))

(define-syntax chopo
  (syntax-rules ()
    ((chop s r k) (bind (mplus (unit s) r) k))))

(define-syntax condo
  (syntax-rules ()
    ((_ c ...) (c1 chopo c ...))))

(define-syntax c1
  (syntax-rules (else)
    ((_ chop) fail)
    ((_ chop (else g ...)) (all g ...))
    ((_ chop (g0 g ...))
     (let ((g^ g0))
       (lambda (s)
         (open (g^ s)
           ((s r) (chop s r (all g ...)))
           mzero))))
    ((_ chop (g0 g ...) c ...)
     (let ((g^ g0))
       (lambda (s)
         (open (g^ s)
           ((s r) (chop s r (all g ...)))
           ((c1 chop c ...) s)))))))

(define-syntax alli
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (let ((g^ g0))
       (lambda (s) (ai (g^ s) (lambda (s) ((alli g ...) s))))))))

(define ai
  (lambda (r g)
    (open r
      ((s r) (interleave (g s) (freeze (ai r g))))
      mzero)))

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
          (else mzero))))))

; Converting streams to lists

(define prefix*
  (lambda (r)
    (open r
      ((s r) (cons s (prefix* r)))
      '())))

(define prefix* ; inlined
  (lambda (r)
    (cond
      ((null? r) '())
      (else
        (let ((p (r '())))
          (cond
            ((not p) '())
            (else
              (cons (car p)
                (prefix* (cdr p))))))))))

(define prefix
  (lambda (n r)
    (cond
      ((zero? n) '())
      (else
       (open r
         ((s r) (cons s
                  (prefix (- n 1) r)))
         '())))))

(define prefix ; inlined
  (lambda (n r)
    (cond
      ((zero? n) '())
      ((null? r) '())
      (else
        (let ((p (r '())))
          (cond
            ((not p) '())
            (else
             (cons (car p)
               (prefix (- n 1) (cdr p))))))))))
