(load "minikanrensupport.scm")

;;; working version
(define with-k
  (lambda (fun)
    (lambda@ (s k f)
      (@ (fun (lambda@ (s^ k^ f^) (@ k s^ f^))) s k f))))

(define with-f
  (lambda (fun)
    (lambda@ (s k f)
      (@ (fun (lambda@ (s^ k^ f^) (@ f))) s k f))))

(define with-substitution
  (lambda (fun)
    (lambda@ (s)
      (@ fun (lambda@ (s^ k^) (@ k^ s)) s))))

(define-syntax ==
  (syntax-rules ()
    [(_ t u)
     (lambda@ (s)
       (cond
         [(unify t u s) => succeed]
         [else (@ fail s)]))]))

(define-syntax all
  (syntax-rules ()
    ((_) succeed)
    ((_ a) a)
    ((_ a a* ...)
     (lambda@ (s k) (all-aux s k a a* ...)))))

(define-syntax all-aux
  (syntax-rules ()
    ((_ s k a) (@ a s k))
    ((_ s k a a* ...) (@ a s (lambda@ (s) (all-aux s k a* ...))))))

;;; all, any

;;; any_2, fail

(define-syntax cond@
  (syntax-rules ()
   ((_ c c* ...)
     (lambda@ (s k f) (cond@-aux s k f c c* ...)))))

(define-syntax cond@-aux
  (syntax-rules (else)
    ((_ s k f (else a* ...)) (@ (all a* ...) s k f))
    ((_ s k f (a* ...)) (@ (all a* ...) s k f))
    ((_ s k f (a* ...) c c* ...)
     (@ (all a* ...) s k (lambda@ () (cond@-aux s k f c c* ...))))))

(define-syntax any ;;; okay
  (syntax-rules ()
    ((_) fail)
    ((_ a) a)
    ((_ a a* ...)
     (cond@ (a) (a*) ...))))

;;; all, ef

(define-syntax condo
  (syntax-rules ()
   ((_ c c* ...)
     (lambda@ (s k f) (condo-aux s k f c c* ...)))))

(define-syntax condo-aux
  (syntax-rules (else)
    ((_ s k f (else a* ...)) (@ (all a* ...) s k f))
    ((_ s k f (a* ...)) (@ (all a* ...) s k f))
    ((_ s k f (q a* ...) c c* ...)
     (@ q s
       (lambda@ (s f1)
	 (lambda@ (_w)
	   (@ (all a* ...) s k (lambda@ () (@ (@ f1) f)))))
       absorb-and-invoke
       (lambda@ () (condo-aux s k f c c* ...))))))

(define absorb-and-invoke
  (lambda@ () (lambda@ (w) (@ w))))

;;; all, anyi

(define-syntax condi
  (syntax-rules ()
   ((_ c c* ...)
     (lambda@ (s) (condi-aux s c c* ...)))))

(define-syntax condi-aux
  (syntax-rules (else)
    ((_ s (else a* ...)) (@ (all a* ...) s))
    ((_ s (a* ...)) (@ (all a* ...) s))
    ((_ s (a* ...) c c* ...)
     (@ interleave 
        (@ (all a* ...) s)
        (condi-aux s c c* ...)))))

(define bi-anyi
  (lambda@ (a1 a2)
    (lambda@ (s)
      (@ interleave
	(@ a1 s)
        (@ a2 s)))))

'(define-syntax condi 
  (syntax-rules (else)
    ((_ (else a* ...)) (all a* ...))
    ((_ (a* ...)) (all a* ...))
    ((_ (a* ...) c c* ...) (@ bi-anyi (all a* ...) (condi c c* ...)))))

(define anyi-k
  (lambda@ (s f)
    (lambda@ (a b) ;a = subst -> sant --> ans and b is an f 
      (@ a
         s 
         (lambda@ (k1 f1) ;;; this is a sant
           (@ (@ f)
              (lambda@ (s^ r) ; new a
                (@ k1 s^ (lambda@ () (@ r k1 f1)))) ; new b
              f1))))))

(define anyi-f
  (lambda@ ()
    (lambda@ (a b) (@ b))))

(define-syntax alli
  (syntax-rules ()
    [(_) (all)]
    [(_ a) a]
    [(_ a a* ...)
     (lambda@ (s)
       (@ bi-alli
         (@ a s)
         (alli a* ...)))]))

(define bi-alli
  (lambda@ (r1 a2 k f)
    (@ r1 anyi-k anyi-f
      (lambda@ (s r)
        (@ interleave
          (@ a2 s)
          (@ bi-alli r a2)
          k f))
      f)))

(define interleave
  (lambda@ (r1 r2 k f)
    (@ r1 anyi-k anyi-f
      (lambda@ (s r1)
        (@ k s
          (lambda@ ()
            (@ interleave r2 r1 k f))))
      (lambda@ () (@ r2 k f)))))

(define-syntax once
  (syntax-rules ()
    ((_ a) (lambda@ (s k f) (@ a s (lambda@ (s^ f^) (@ k s^ f)) f)))))

; Equivalent of Kanren's if-only
;   (if-only COND THEN ELSE) ==> (any (all (all! COND) THEN)
;                                     (all (fails COND) ELSE))
; or
; (conde
;   (q1 g ...)
;   (q2 g ...)
;   (q3 g ...)
;   (else g ...))
; ==>
; (condo
;   ((once q1) g ...)
;   ((once q2) g ...)
;   ((once q3) g ...)
;   (else g ...))


(define-syntax conde
  (syntax-rules ()
    ((_ c1 c2* ...) (conde-aux () (c1 c2* ...)))))

(define-syntax conde-aux
  (syntax-rules (else)
    ((_ (c0 c ...) ()) (condo c0 c ...))
    ((_ (c ...) ((else a ...)))
     (condo c ... (else a ...)))
    ((_ (c ...) ((a0 a ...) c2 ...))
     (conde-aux (c ... ((once a0) a ...)) (c2 ...)))))

;;; This does not change


;;; relies on all.

;;; recursive macros.

(define-syntax project  ;;; okay
  (syntax-rules ()
    ((_ (x* ...) a* ...)
     (lambda@ (s)
       (let ([x* (reify-nonfresh x* s)] ...)
         (@ (all a* ...) s))))))

(define-syntax fresh   ;;; okay
  (syntax-rules ()
    [(_ (x* ...) a* ...)
     (lambda@ (s)
       (let ((x* (var 'x*)) ...)
         (@ (all a* ...) s)))]))

;;; run

(define-syntax run1
  (syntax-rules ()
    ((_ (x) a* ...) 
     (prefix 1 (run (x) a* ...)))))

(define-syntax run
  (syntax-rules ()
    ((_ (x) a* ...)
     (let ((x (var (quote x))))
       (@ (all a* ...)
          empty-s
          (lambda@ (s f) (cons (reify x s) f))
          (lambda@ () (quote ())))))))

(define-syntax run-stream ;;; okay
  (syntax-rules ()
    ((_ (x) a* ...)
     (prefix 0 (run (x) a* ...)))))

(define prefix
  (lambda (n v*)
    (cond
      ((null? v*) (quote ()))
      (else
        (cons (car v*)
          (cond
            ((= n 0) (prefix 0 (@ (cdr v*))))
            ((= n 1) (quote ()))
            (else 
              (prefix (- n 1)
                (@ (cdr v*))))))))))

(define-syntax run$ ;;; okay
  (syntax-rules ()
    ((_ (x) a ...) (prefix 10 (run (x) (all a ...))))))

;;; a stream is either empty or a pair whose cdr is 
                ;;; a function of no arguments that returns a stream.

(define succeed (lambda@ (s k) (@ k s)))

(define fail (lambda@ (s k f) (@ f))) ;;; part of the interface

(define-syntax trace-vars
  (syntax-rules ()
    [(_ title ())
     (lambda@ (s k)
       (printf "~s~n" title)
       (@ k s))]
    [(_ title (x ...))
     (lambda@ (s k)
       (for-each (lambda (x_ t) (printf "~s ~a ~s~n" x_ title t))
         '(x ...) (reify-fresh `(,(reify-nonfresh x s) ...)))
       (newline)
       (@ k s))]))

;;; ----------------------------------------------

(define twice
  (lambda (a)
    (lambda@ (k s f)
      (let ((like-k (lambda@ (s^ f^)
                       (lambda (w)
                         (@ k
                            s^
                            (cond
                              [w f]
                              [else (lambda () (@ (f^) #t))])))))
            (like-f (lambda ()
                       (lambda (w)
                         (@ f)))))
        (@ a like-k s like-f #f)))))

(define at-most
  (lambda (n)
    (lambda (a)
      (lambda@ (k s f)
        (let ((like-k (lambda@ (s^ f^)
                          (lambda (w)
                            (@ k
                              s^
                              (cond
                               [(= w 0) f]
                               [else (lambda () (@ (f^) (- w 1)))])))))
              (like-f (lambda ()
                         (lambda (w)
                           (f)))))
          (@ a like-k s like-f (- n 1)))))))

(define handy
  (lambda (x y q)
    (project (x y) (== (+ x y) q))))

;;; 
(define test-0 ;;; tests with-k
  (prefix 2
    (run (q)
      (fresh (x y)
        (all
          (any
            (with-k
              (lambda (k)
                (all
                  (== 8 x)
                  (all (== 9 y) k (== 9 x)))))
            (all (== 2 x) (== 3 y)))
          (handy x y q))))))

(pretty-print `(,test-0
                = (17 5)))

(define test-1 ;;; tests with-f
  (prefix 4
    (run (q)
      (any
        (with-f
          (lambda (f)
            (any (== 2 q)
              (any (== 3 q) f (== 4 q)))))
        (any (== 5 q) (== 6 q))))))

(pretty-print `(,test-1
                = (2 3 5 6)))

(define test-2 ;;; tests with-substitution
  (prefix 0
    (run (q)
      (fresh (x y)
        (with-substitution
          (lambda (s)
            (any
              (all
                (all (== 2 x) s (== 3 x))
                (with-substitution
                  (lambda (t)
                    (all (== 5 y)
                      (all
                        t (== 6 y)
                        (handy x y q))))))
              (== 20 q))))))))

(pretty-print `(,test-2 = (9 20)))

;;; mini-test

(define test-3
  (prefix 2 (run (q)
              (fresh (x y)
                (all
                  (any (== y 3) (== y 4))
                  (all (== x 4)
                    (all
                      (once (any (== x 4) (== x 5)))
                      (handy x y q))))))))

(pretty-print `(,test-3 = (7 8)))


'(define test-4
  (prefix 2
    (run (q)
      (fresh (x y)
        (all
          (@ ef (any
                (== 3 y)
                (all
                  (== 4 y)
                  (== x 3)))
            (any
              (== 5 x)
              (== 4 y))
            (== 5 y))
          (handy x y q))))))

'(pretty-print `(,test-4
                = (8 7)))

'(define test-5 ;;; twice
  (prefix 2
    (run (q)
      (fresh (x y)
        (twice
          (all
            (any
              (all (== x 3) (== y 4))
              (any
                (all (== x 6) (== y 10))
                (all (== x 7) (== y 14))))
            (handy x y q)))))))

'(pretty-print `(,test-5
                = (7 16)))
          
'(define test-6 ;;; (at-most 2)
  (prefix 2
    (run (q)
      (fresh (x y)
        ((at-most 2)
         (all
           (any
             (all (== x 3) (== y 4))
             (any
               (all (== x 6) (== y 10))
               (all (== x 7) (== y 14))))
           (handy x y q)))))))

'(pretty-print `(,test-6
                = (7 16)))

(define test-7  ;;; tests anyi
  (prefix 9
    (run (x)
      (@ bi-anyi
        (any (== x 3)
          (any
            (@ bi-anyi
              (any (== x 20) (== x 21))
              (any (== x 30) (== x 31)))
            (== x 5)))
        (any (== x 13)
          (any (== x 14) (== x 15)))))))

(pretty-print
  `(,test-7
    = (3 13 20 14 30 15 21 31 5)))

#!eof
(define get-s
  (lambda (fun)
    (lambda@ (k s f)
      (@ (fun s) k s f))))

(define-syntax ==+
  (syntax-rules ()
    [(_ fv old-s)
     (lambda@ (k s f)
       (@ k (multi-extend fv old-s s) f))]))

(define multi-extend
  (lambda (fv old-s s)
    (cond
      [(assq fv old-s) =>
       (lambda (pr)
         (let ([p (walk-pr pr old-s)])
           (cond
             [(eq? (car p) fv)
              (cond
                [(var? (cdr p)) s]
                [(pair? (cdr p))
                 (ext-s* (cdr p) old-s
                   (ext-s?! fv (cdr p) s))]
                [else (ext-s?! fv (cdr p) s)])]
             [else (ext-s* (cdr p) old-s
                     (ext-s?! fv (cdr p) s))])))]
      [else s])))

(define multi-extend
  (lambda (fv old-s s)
    (cond
      [(assq fv old-s) =>
       (lambda (pr)
         (let ([p (walk-pr pr old-s)])
           (cond
             [(eq? (car p) fv)
              (cond
                [(var? (cdr p)) s]
                [(pair? (cdr p))
                 (ext-s* (cdr p) old-s
                   (ext-s?! fv (cdr p) s))]
                [else (ext-s?! fv (cdr p) s)])]
             [else (ext-s* (cdr p) old-s
                     (ext-s?! fv (cdr p) s))])))]
      [else s])))

(define ext-s?!
  (lambda (x v s)
    (cond
      [(eq? (walk x s) v) s]
      [else (ext-s x v s)])))

(define ext-s*
  (lambda (x old-s s)
    (cond
      [(and (var? x) (assq x s)) s]
      [(and (var? x) (assq x old-s)) =>
       (lambda (pr)
         (let ([final-pr (walk-pr pr old-s)])
           (let ([x (car final-pr)]
                 [v (cdr final-pr)])
             (cond
               [(var? v) s]
               [else (ext-s* v old-s (ext-s?! x v s))]))))]
      [(pair? x) (ext-s* (cdr x) old-s (ext-s* (car x) old-s s))]
      [else s])))

(define test-stuff
  (lambda ()
    (run1 (a)
      (fresh (u v w x y z q r)
        (with-substitution
          (lambda (s)
            (all
              (== x y)
              (== z 3)
              (== y `(5 ,z))
              (== v w)
              (== u `(,v))
              (== q r)
              (get-s
                (trace-lambda empty (s^)
                  (all
                    s
                    (==+ x s^)
                    (==+ y s^)
                    (==+ z s^)
                    (==+ u s^)
                    (lambda@ (k s f)
                      (write s)
                      (newline)
                      (@ k s f))))))))))))

(define test2
  (lambda ()
    (run1 (a)
      (fresh (u v w x y z q r)
        (with-substitution
          (lambda (s)
            (all
              (== x `(,y ,z))
              (== z `(3 ,y ,z ,z ,x))
              (== y `(5 ,z ,x ,y))
              (== v w)
              (== u `(,v))
              (== q r)
              (get-s
                (lambda (s^)
                  (all
                    s
                    (==+ x s^)
                    (==+ y s^)
                    (==+ x s^)
                    (==+ u s^)
                    (lambda@ (k f s)
                      (write s)
                      (newline)
                      (@ k s f))))))))))))

(define-syntax forget-me-not
  (syntax-rules ()
    [(_ (x* ...) a* ...)
     (with-substitution
       (lambda (s)
         (all a* ...
           (get-s
             (lambda (s^)
               (all s (==+ x* s^) ...))))))]))

(define test3
  (lambda ()
    (run1 (a)
      (fresh (u v w x y z q r)
        (forget-me-not (x y u v)
          (== x `(,y ,z))
          (== z `(3 ,y ,z ,z ,x))
          (== y `(5 ,z ,x ,y))
          (== v w)
          (== u `(,v))
          (== q r))))))

(define-syntax fails 
   (syntax-rules () 
     ((_ a* ...)
      (lambda@ (k s f) 
        (@ (all a* ...)
          (lambda@ (_s _f) (@ f)) 
          (lambda@ () (@ k s f)) 
          s)))))

(define-syntax condi$ 
  (syntax-rules (else)
    ((_ (else a* ...)) (alli a* ...))
    ((_ (a* ...) c* ...) (@ bi-anyi (alli a* ...) (condi$ c* ...)))))

(define-syntax cond@$
  (syntax-rules (else)
    ((_ (else a* ...)) (alli a* ...))
    ((_ (a* ...) c* ...) (any (alli a* ...) (cond@$ c* ...)))))



; testing alli
(test-check 'alli-1
  (prefix 100
    (run (q)
      (fresh (x y z)
        (alli
          (any (== x 1) (== x 2))
          (any (== y 3) (== y 4))
          (any (== z 5) (== z 6) (== z 7)))
        (== `(,x ,y ,z) q))))
  '((1 3 5)
    (2 3 5)
    (1 4 5)
    (2 4 5)
    (1 3 6)
    (2 3 6)
    (1 4 6)
    (2 4 6)
    (1 3 7)
    (2 3 7)
    (1 4 7)
    (2 4 7)))


(test-check 'alli-2
  (prefix 100
    (run (q)
      (fresh (x y z)
        (cond@$
          [(any (== x 1) (== x 2)) (any (== y 3) (== y 4)) (any (== z 5) (== z
6) (== z 7))]
          [else fail])
        (== `(,x ,y ,z) q))))
  '((1 3 5)
    (2 3 5)
    (1 4 5)
    (2 4 5)
    (1 3 6)
    (2 3 6)
    (1 4 6)
    (2 4 6)
    (1 3 7)
    (2 3 7)
    (1 4 7)
    (2 4 7)))

(test-check 'alli-3
  (prefix 100
    (run (q)
      (fresh (x y z)
        (condi$
          [(any (== x 1) (== x 2)) (any (== y 3) (== y 4)) (any (== z 5) (== z
6) (== z 7))]
          [else fail])
        (== `(,x ,y ,z) q))))
  '((1 3 5)
    (2 3 5)
    (1 4 5)
    (2 4 5)
    (1 3 6)
    (2 3 6)
    (1 4 6)
    (2 4 6)
    (1 3 7)
    (2 3 7)
    (1 4 7)
    (2 4 7)))

(test-check 'alli-4
  (prefix 100
    (run (q)
      (fresh (x y z)
        (cond@$
         [(any (== x 1) (== x 2)) (any (== y 3) (== y 4)) (any (== z 5) (== z 6)
(== z 7))]
         [(any (== x 1) (== x 2)) (any (== y 3) (== y 4)) (any (== z 5) (== z 6)
(== z 7))]
         [else fail])
        (== `(,x ,y ,z) q))))
  '((1 3 5)
    (2 3 5)
    (1 4 5)
    (2 4 5)
    (1 3 6)
    (2 3 6)
    (1 4 6)
    (2 4 6)
    (1 3 7)
    (2 3 7)
    (1 4 7)
    (2 4 7)
    (1 3 5)
    (2 3 5)
    (1 4 5)
    (2 4 5)
    (1 3 6)
    (2 3 6)
    (1 4 6)
    (2 4 6)
    (1 3 7)
    (2 3 7)
    (1 4 7)
    (2 4 7)))

(test-check 'alli-5
  (prefix 100
    (run (q)
      (fresh (x y z)
        (condi$
         [(any (== x 1) (== x 2)) (any (== y 3) (== y 4)) (any (== z 5) (== z 6)
(== z 7))]
         [(any (== x 1) (== x 2)) (any (== y 3) (== y 4)) (any (== z 5) (== z 6)
(== z 7))]
         [else fail])
        (== `(,x ,y ,z) q))))
  '((1 3 5)
    (1 3 5)
    (2 3 5)
    (2 3 5)
    (1 4 5)
    (1 4 5)
    (2 4 5)
    (2 4 5)
    (1 3 6)
    (1 3 6)
    (2 3 6)
    (2 3 6)
    (1 4 6)
    (1 4 6)
    (2 4 6)
    (2 4 6)
    (1 3 7)
    (1 3 7)
    (2 3 7)
    (2 3 7)
    (1 4 7)
    (1 4 7)
    (2 4 7)
    (2 4 7)))

(test-check 'alli-6
  (prefix 100
    (run (q)
      (fresh (x y z)
        (condi$
         [(any (== x 1) (== x 2)) (any (== y 3) (== y 4)) (any (== z 5) (== z 6)
(== z 7))]
         [(any (== x 8) (== x 9)) (any (== y 10) (== y 11)) (any (== z 12) (== z
13) (== z 14))]
         [else fail])
        (== `(,x ,y ,z) q))))
  '((1 3 5)
    (8 10 12)
    (2 3 5)
    (9 10 12)
    (1 4 5)
    (8 11 12)
    (2 4 5)
    (9 11 12)
    (1 3 6)
    (8 10 13)
    (2 3 6)
    (9 10 13)
    (1 4 6)
    (8 11 13)
    (2 4 6)
    (9 11 13)
    (1 3 7)
    (8 10 14)
    (2 3 7)
    (9 10 14)
    (1 4 7)
    (8 11 14)
    (2 4 7)
    (9 11 14)))

'(test-check 'alli-7
  (prefix 100
    (run (q)
      (fresh (x y z)
        (condi$
         [(anyi (== x 1) (== x 2)) (anyi (== y 3) (== y 4)) (anyi (== z 5) (== z
6) (== z 7))]
         [(anyi (== x 8) (== x 9)) (anyi (== y 10) (== y 11)) (anyi (== z 12)
(== z 13) (== z 14))]
         [else fail])
        (== `(,x ,y ,z) q))))
  '((1 3 5)
    (8 10 12)
    (2 3 5)
    (9 10 12)
    (1 4 5)
    (8 11 12)
    (2 4 5)
    (9 11 12)
    (1 3 6)
    (8 10 13)
    (2 3 6)
    (9 10 13)
    (1 4 6)
    (8 11 13)
    (2 4 6)
    (9 11 13)
    (1 3 7)
    (8 10 14)
    (2 3 7)
    (9 10 14)
    (1 4 7)
    (8 11 14)
    (2 4 7)
    (9 11 14)))


'(test-check 'alli-8
  (prefix 100
    (run (q)
      (fresh (x y z)
        (condi$
         [(any (== x 1) (== x 2) (== x 3))
          (any (== y 4) (== y 5) (== y 6))
          (any (== z 7) (== z 8) (== z 9))]
         [else fail])
        (== `(,x ,y ,z) q))))
  '((1 4 7)
    (8 10 12)
    (2 3 5)
    (9 10 12)
    (1 4 5)
    (8 11 12)
    (2 4 5)
    (9 11 12)
    (1 3 6)
    (8 10 13)
    (2 3 6)
    (9 10 13)
    (1 4 6)
    (8 11 13)
    (2 4 6)
    (9 11 13)
    (1 3 7)
    (8 10 14)
    (2 3 7)
    (9 10 14)
    (1 4 7)
    (8 11 14)
    (2 4 7)
    (9 11 14)))


; Extending relations in truly mathematical sense.
; First, why do we need this.

(define fact1
  (lambda (x y)
    (all
      (== 'x1 x)
      (== 'y1 y))))

(define fact2
  (lambda (x y)
    (all
      (== 'x2 x)
      (== 'y2 y))))

(define fact3
  (lambda (x y)
    (all
      (== 'x3 x)
      (== 'y3 y))))

(define fact4
  (lambda (x y)
    (all
      (== 'x4 x)
      (== 'y4 y))))

; R1/2 and R3/4 are overlapping
(define R1/2
  (lambda (a1 a2)
    (cond@
      [(fact1 a1 a2) succeed]
      [(fact2 a1 a2) succeed]
      [else fail])))

(define R3/4
  (lambda (a1 a2)
    (cond@
      [(fact3 a1 a2) succeed]
      [(fact4 a1 a2) succeed]
      [else fail])))

(cout nl "R1/2:" nl)
(pretty-print
  (prefix 10
    (run (q) 
      (fresh (x y)
        (R1/2 x y)
        (== `(,x ,y) q)))))
(cout nl "R3/4" nl)
(pretty-print
  (prefix 10
    (run (q) 
      (fresh (x y)
        (R3/4 x y)
        (== `(,x ,y) q)))))

(cout nl "R1/2+R3/4:" nl)
(pretty-print 
  (prefix 10
    (run (q)
      (fresh (x y)
        ((lambda (a1 a2)
           (cond@
             [(R1/2 a1 a2) succeed]
             [(R3/4 a1 a2) succeed]
             [else fail]))
         x y)
       (== `(,x ,y) q)))))

; Infinitary relation
; r(z,z).
; r(s(X),s(Y)) :- r(X,Y).

(define Rinf
  (lambda (a1 a2)
    (cond@
      [(== 'z a1) (== 'z a2)]
      [else (fresh (x y)
              (== `(s ,x) a1)
              (== `(s ,y) a2)
              (Rinf x y))])))

(cout nl "Rinf:" nl)
(time 
  (pretty-print
    (prefix 5
      (run (q)
        (fresh (x y)
          (Rinf x y)
          (== `(,x ,y) q))))))
(cout nl "Rinf+R1/2: Rinf starves R1/2:" nl)
(time
  (pretty-print 
    (prefix 5
      (run (q)
        (fresh (x y)
          ((lambda (a1 a2)
             (cond@
               [(Rinf a1 a2) succeed]
               [(R1/2 a1 a2) succeed]
               [else fail]))
           x y)
          (== `(,x ,y) q))))))

(test-check "R1/2 * Rinf: clearly starvation"
  (prefix 5
    (run (q)
      (fresh (x y u v)
        (all (R1/2 x y) (Rinf u v))
        (== `(,x ,y ,u ,v) q))))
  ; indeed, only the first choice of R1/2 is apparent
  '((x1 y1 z z)
    (x1 y1 (s z) (s z))
    (x1 y1 (s (s z)) (s (s z)))
    (x1 y1 (s (s (s z))) (s (s (s z))))
    (x1 y1 (s (s (s (s z)))) (s (s (s (s z)))))))

(test-check "R1/2 * Rinf: interleaving"
  (prefix 10
    (run (q)
      (fresh (x y u v)
        (alli (R1/2 x y) (Rinf u v))
        (== `(,x ,y ,u ,v) q))))
  ; both choices of R1 are apparent
  '((x1 y1 z z)
    (x2 y2 z z)
    (x1 y1 (s z) (s z))
    (x2 y2 (s z) (s z))
    (x1 y1 (s (s z)) (s (s z)))
    (x2 y2 (s (s z)) (s (s z)))
    (x1 y1 (s (s (s z))) (s (s (s z))))
    (x2 y2 (s (s (s z))) (s (s (s z))))
    (x1 y1 (s (s (s (s z)))) (s (s (s (s z)))))
    (x2 y2 (s (s (s (s z)))) (s (s (s (s z)))))))


(test-check "R1/2 * Rinf: interleaving"
  (prefix 10
    (run (q)
      (fresh (x y u v)
        (alli (Rinf x y) (Rinf u v))
        (== `(,x ,y ,u ,v) q))))
  '((z z z z)
    ((s z) (s z) z z)
    (z z (s z) (s z))
    ((s (s z)) (s (s z)) z z)
    (z z (s (s z)) (s (s z)))
    ((s z) (s z) (s z) (s z))
    (z z (s (s (s z))) (s (s (s z))))
    ((s (s (s z))) (s (s (s z))) z z)
    (z z (s (s (s (s z)))) (s (s (s (s z)))))
    ((s z) (s z) (s (s z)) (s (s z)))))

(define-syntax kmatch
  (syntax-rules (else)
    [(_ t (line* ...) cl* ...)
     (let ([temp t])
       (run1 (q) (kmatch-aux q temp (line* ...) cl* ...)))]))

(define-syntax kmatch-aux
  (syntax-rules (else guard)
    [(_ q t) (error 'kmatch "Unmatched datum: ~s" t)]
    [(_ q t (else e e* ...))
     (== (begin e e* ...) q)]
    [(_ q t ((x* ...) lhs (guard g) rhs rhs* ...) cl* ...)
     (condo
       ((fresh (x* ...)
          (== t (quasiquote lhs))
          (project (x* ...)
            (if g (== (begin rhs rhs* ...) q) fail))))
       (else (kmatch-aux q t cl* ...)))]
    [(_ q t ((x* ...) lhs rhs rhs* ...) cl* ...)
     (condo
       ((fresh (x* ...)
          (== t (quasiquote lhs))
          (project (x* ...)
            (== (begin rhs rhs* ...) q))))
       (else (kmatch-aux q t cl* ...)))]))

(define interp
  (lambda (e)
    (kmatch e
      [(a) ,a (symbol? a) (list a)]
      [(id* e) (lambda ,id* ,e) (list id* e)]
      [(t c a) (if ,t ,c ,a) (list t c a)]
      [(a a*) (,a . ,a*) (list a a*)]
      [else #t])))
       
(define-syntax once-again
  (syntax-rules ()
    ((_ a)
     (call/cc
       (lambda (k)
         (all a (any succeed 
                  (lambda@ (k s f)
                    (k (lambda@ (k s^ f)
                         (@ k s f)))))))))))



(test-check 'conde-1
  (prefix 10
    (run (q)
      (fresh (x y)
	(conde
	  ((any (== x 1) (== x 2)) (any (== y 1) (== y 2)))
	  (else (any (== y 3) (== y 4))))
	(== q (cons x y)))))
  '((1 . 1) (1 . 2)))

(test-check 'conde-2
  (prefix 10
    (run (q)
      (fresh (x y)
	(== x 3)
	(conde
	  ((any (== x 1) (== x 2)) (any (== y 1) (== y 2)))
	  (else (any (== y 3) (== y 4))))
	(== q (cons x y)))))
  '((3 . 3) (3 . 4)))


(test-check 'conde-3
  (prefix 10
    (run (q)
      (fresh (x y)
	(== y 3)
	(conde
	  ((any (== x 1) (== x 2)) (any (== y 1) (== y 2)))
	  (else (any (== y 3) (== y 4))))
	(== q (cons x y)))))
  '())

(test-check 'conde-4
  (prefix 10
    (run (q)
      (fresh (x y)
	(== x 5) (== y 3)
	(conde
	  ((any (== x 1) (== x 2)) (any (== y 1) (== y 2)))
	  (else (any (== y 3) (== y 4))))
	(== q (cons x y)))))
  '((5 . 3)))

