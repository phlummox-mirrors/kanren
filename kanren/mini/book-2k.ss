(load "minikanrensupport.ss")

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

(define-syntax lambdap@
  (syntax-rules ()
    ((_ (g) body) (ppp (lambda@ (g) body)))
    ((_ (g f) body) (ppp (lambda@ (g) (lambdaa@ (f) body))))))

(define-syntax p@ 
  (syntax-rules ()
    ((_ p g) (@ (ppp-of p) g))
    ((_ p g f) (a@ (@ (ppp-of p) g) f))))

(define ppp
  (lambda (p)
    (cons 'awaiting-g-and-f p)))

(define ppp-of
  (lambda (p)
    (cond
      ((pair? p) (if (eq? (car p) 'awaiting-g-and-f) 
                   (cdr p)
                   (error 'ppp-of "~s" p)))
      (else (error 'ppp-of2 "~s" p)))))

(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () body) (fff (lambda@ () body)))))

(define-syntax ff@ 
  (syntax-rules ()
    ((_ f) (@ (fff-of f)))))

(define fff
  (lambda (f)
    (cons 'awaiting-nothing f)))

(define fff-of
  (lambda (f)
    (cond
      ((pair? f) (if (eq? (car f) 'awaiting-nothing) 
                   (cdr f)
                   (error 'fff-of "~s" f)))
      (else (error 'fff-of2 "~s" f)))))

(define-syntax lambdak@
  (syntax-rules ()
    ((_ (s) body) (kkk (lambda@ (s) body)))
    ((_ (s f) body) (kkk (lambda@ (s) (lambdaa@ (f) body))))))

(define-syntax k@ 
  (syntax-rules ()
    ((_ k s) (@ (kkk-of k) s))
    ((_ k s f) (a@ (@ (kkk-of k) s) f))))

(define kkk
  (lambda (k)
    (cons 'awaiting-s-and-f k)))

(define kkk-of
  (lambda (k)
    (cond
      ((pair? k) (if (eq? (car k) 'awaiting-s-and-f) 
                   (cdr k)
                   (error 'kkk-of "~s" k)))
      (else (error 'kkk-of2 "~s" k)))))

(define-syntax lambdaa@
  (syntax-rules ()
    ((_ (f) body) (aaa (lambda@ (f) body)))))

(define-syntax a@ 
  (syntax-rules ()
    ((_ a f) (@ (aaa-of a) f))))

(define aaa
  (lambda (a)
    (cons 'awaiting-f a)))

(define aaa-of
  (lambda (a)
    (cond
      ((pair? a) (if (eq? (car a) 'awaiting-f) 
                   (cdr a)
                   (error 'aaa-of "~s" a)))
      (else (error 'aaa-of2 "~s" a)))))

(define-syntax lambdar@
  (syntax-rules ()
    ((_ (k) body) (rrr (lambda@ (k) body)))
    ((_ (k f) body) (rrr (lambda@ (k) (lambdaa@ (f) body))))))

(define-syntax r@ 
  (syntax-rules ()
    ((_ r k) (@ (rrr-of r) k))
    ((_ r k f) (a@ (@ (rrr-of r) k) f))))

(define rrr
  (lambda (r)
    (cons 'awaiting-k-and-f r)))

(define rrr-of
  (lambda (r)
    (cond
      ((pair? r) (if (eq? (car r) 'awaiting-k-and-f) 
                   (cdr r)
                   (error 'rrr-of "~s" r)))
      (else (error 'rrr-of2 "~s" r)))))

(define-syntax lambdag@
  (syntax-rules ()
    ((_ (s) body) (ggg (lambda@ (s) body)))
    ((_ (s k) body) (ggg (lambda@ (s) (lambdar@ (k) body))))
    ((_ (s k f) body) (ggg (lambda@ (s) (lambdar@ (k f) body))))))

(define-syntax g@ 
  (syntax-rules ()
    ((_ g s) (@ (ggg-of g) s))
    ((_ g s k) (r@ (@ (ggg-of g) s) k))
    ((_ g s k f) (r@ (@ (ggg-of g) s) k f))))

(define ggg
  (lambda (g)
    (cons 'awaiting-s-k-f g)))

(define ggg-of
  (lambda (g)
    (cond
      ((pair? g) (if (eq? (car g) 'awaiting-s-k-f) 
                   (cdr g)
                   (error 'ggg-of "~s" g)))
      (else (error 'ggg-of2 "~s" g)))))

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
      (p@ (r@ r1 anyi-k anyi-f)
        (lambdag@ (s r1)
          (k@ k s 
            (lambdaf@ ()
              (r@ (interleave r2 r1) k f))))
        (lambdaf@ () (r@ r2 k f))))))

(define anyi-k
  (lambdak@ (s f)
    (lambdap@ (g _)
      (g@ g s 
        (lambdar@ (k1 f1)
          (p@ (ff@ f)
            (lambdag@ (s r)
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
        (lambdag@ (s r)
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
