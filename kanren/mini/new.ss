(load "minikanrensupport.ss")

; Stream implementation

(define-syntax open
  (syntax-rules ()
    ((_ e e1 ((s r) e2))
     (let ((r^ e))
       (let ((p (cond
                  ((mzero? r^) #f)
                  (else (r^ mzero)))))
         (cond
           ((not p) e1)
           (else (let ((s (car p))
                       (r (cdr p)))
                   e2))))))))

(define-syntax freeze
  (syntax-rules ()
    ((_ e)
     (lambda (f)
       (let ((r e))
         (cond
           ((not (mzero? r)) (r f))
           ((not (mzero? f)) (f mzero))
           (else #f)))))))

(define mzero '())

(define mzero? null?)

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
        (freeze
          (open r mzero ((s r) (mplus (k s) (bind r k)))))))))

; Kanren implementation

(define interleave
  (lambda (r r^)
    (cond
      ((mzero? r) r^)
      ((mzero? r^) r)
      (else
        (freeze
          (open r r^ ((s r) (mplus (unit s) (interleave r^ r)))))))))

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

(define-syntax cond1
  (syntax-rules ()
    ((_ c ...)
     (let-syntax ((chop (syntax-rules ()
                          ((chop s r k) (k s)))))
       (c1 chop c ...)))))

(define-syntax condo
  (syntax-rules ()
    ((_ c ...)
     (let-syntax ((chop (syntax-rules ()
                          ((chop s r k) (bind (mplus (unit s) r) k)))))
       (c1 chop c ...)))))

(define-syntax c1
  (syntax-rules (else)
    ((_ chop) fail)
    ((_ chop (else g ...)) (all g ...))
    ((_ chop (g0 g ...))
     (let ((g^ g0))
       (lambda (s)
         (open (g^ s) mzero
           ((s r) (chop s r (all g ...)))))))
    ((_ chop (g0 g ...) c ...)
     (let ((g^ g0))
       (lambda (s)
         (open (g^ s) ((c1 chop c ...) s)
           ((s r) (chop s r (all g ...)))))))))

(define-syntax alli
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g ...)
     (let ((g^ g0))
       (lambda (s)
         (ai (g^ s)
             (lambda (s) ((alli g ...) s))))))))

(define ai
  (lambda (r g)
    (open r mzero
      ((s r) (interleave (g s) (freeze (ai r g)))))))

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
    (open r '()
      ((s r) (cons s (prefix* r))))))

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
       (open r '()
         ((s r) (cons s
                  (prefix (- n 1) r))))))))

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
