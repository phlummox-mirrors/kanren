;;; all_2 succeed
(load "minikanrensupport.scm")

;;; working version
(define with-sk
  (lambda (f)
    (lambda@ (sk fk s)
      (@ (f (lambda@ (sk^ fk^ s^) (@ sk fk^ s^))) sk fk s))))

(define with-fk
  (lambda (f)
    (lambda@ (sk fk s)
      (@ (f (lambda@ (sk^ fk^ s^) (fk))) sk fk s))))

(define with-substitution
  (lambda (f)
    (lambda@ (sk fk s)
      (@ (f (lambda@ (a sk^ fk^ s^) (@ a sk^ fk^ s))) sk fk s))))

(define with-substitution
  (lambda (f)
    (lambda@ (sk fk s)
      (@ (f (lambda@ (sk^ fk^ s^) (@ sk^ fk^ s))) sk fk s))))

(define-syntax ==
  (syntax-rules ()
    [(_ t u)
     (lambda@ (sk fk s)
       (cond
         [(unify t u s) => (@ sk fk)]
         [else (fk)]))]))

(define-syntax all
  (syntax-rules ()
    ((_) (lambda@ (sk) sk))
    ((_ a) a)
    ((_ a a* ...)
     (lambda (sk) (all-aux sk a a* ...)))))

(define-syntax all-aux
  (syntax-rules ()
    ((_ sk a) (a sk))
    ((_ sk a a* ...) (@ a (all-aux sk a* ...)))))

;;; all, any

(define-syntax cond@  ;;; okay
  (syntax-rules (else)
    ((_ (else a* ...)) (all a* ...))
    ((_ (a* ...) c* ...) (any (all a* ...) (cond@ c* ...)))))

;;; any_2, fail

(define-syntax any ;;; okay
  (syntax-rules ()
    ((_) fail)
    ((_ a) a)
    ((_ a a* ...)
     (lambda@ (sk fk s)
       (any-aux sk fk s a a* ...)))))

(define-syntax any-aux
  (syntax-rules ()
    ((_ sk fk s a) (@ a sk fk s))
    ((_ sk fk s a a* ...)
     (@ a sk (lambda () (any-aux sk fk s a* ...)) s))))

;;; all, ef

(define-syntax condo ;;; okay
  (syntax-rules (else)
    ((_ (else a* ...)) (all a* ...))
    ((_ (a a* ...) c  ...) (ef a (all a* ...) (condo c ...)))))

(define-syntax conde ;;; okay
  (syntax-rules (else)
    ((_ (else a* ...)) (all a* ...))
    ((_ (a a* ...) c  ...) (ef (once a) (all a* ...) (conde c ...)))))

(define-syntax ef
  (syntax-rules ()
    [(_ t c a)
     (lambda@ (sk fk s)
       (@ t
         (@ ef-like-sk-maker (@ c sk) fk)
         ef-like-fk
         s
         (lambda@ () (@ a sk fk s))))]))

(define ef-like-fk
  (lambda@ ()
    (lambda@ (w)
      (printf "called from ef-like-fk\n")
      (w))))

(define ef-like-sk-maker
  (lambda@ (sk fk)
    (lambda@ (like-fk s)
      (lambda@ (w^)
        (@ sk (lambda@ () (@ (like-fk) fk)) s)))))

'(define-syntax ef ;;; old definition
  (syntax-rules ()
    [(_ a b c)
     (lambda@ (sk fk s)
       (let ([a-res (@ a (lambda@ (fk s) (cons s fk)) (lambda () #f) s)])
         (if a-res
             (let loop ([a-res a-res])
               (cond
                 [a-res (@ b sk (lambda () (loop ((cdr a-res)))) (car a-res))]
                 [else (fk)]))
             (@ c sk fk s))))]))

;;; all, anyi

(define-syntax condi 
  (syntax-rules (else)
    ((_ (else a* ...)) (all a* ...))
    ((_ (a* ...) c* ...) (bi-anyi (all a* ...) (condi c* ...)))))

(define-syntax bi-anyi
  (syntax-rules ()
    [(_ a1 a2)
     (lambda@ (sk fk s)
       (@ interleave sk fk
         (lambda@ (sk fk) (@ a1 sk fk s))
         (lambda@ (sk fk) (@ a2 sk fk s))))]))

(define interleave
  (lambda@ (sk fk sant1 sant2)
    (@ (@ sant1 bi-anyi-like-sk bi-anyi-like-fk)
       (cons
         (lambda@ (s residual1)
           (@ sk
             (lambda@ ()
               (@ interleave sk fk sant2 residual1))
             s))
         (lambda@ () (@ sant2 sk fk))))))

(define bi-anyi-like-sk
  (lambda@ (fk s)
    (lambda@ (w) ;a = subst -> sant --> ans and b is an fk 
      (@ (car w)
         s 
         (lambda@ (sk1 fk1) ;;; this is a sant
           (@ (@ fk)
              (cons
                (lambda@ (s^ residual) ; new a
                  (@ sk1 (lambda@ () (@ residual sk1 fk1)) s^)) ; new b
                fk1)))))))

(define bi-anyi-like-fk
  (lambda@ ()
    (lambda@ (w) (@ (cdr w)))))

(define-syntax once
  (syntax-rules ()
    ((_) succeed)
    ((_ a) (lambda@ (sk fk) (@ a (lambda (fk^) (@ sk fk)) fk)))
    ((_ a a* ...) (lambda@ (sk fk) (once-aux sk fk a a* ...)))))

(define-syntax once-aux
  (syntax-rules ()
    ((_ sk fk a) (@ a (lambda (fk^) (sk fk)) fk))
    ((_ sk fk a a* ...) (@ a (lambda (fk^) (once-aux sk fk a* ...)) fk))))
       
;;; This does not change


;;; relies on all.

;;; recursive macros.

(define-syntax project  ;;; okay
  (syntax-rules ()
    ((_ (x* ...) a* ...)
     (projectf (x* ...)
       (lambda (x* ...) (all a* ...))))))

(define-syntax project  ;;; okay
  (syntax-rules ()
    ((_ (x* ...) a* ...)
     (lambda@ (sk fk s)
       (let ([x* (reify-nonfresh x* s)] ...)
         (@ (all a* ...) sk fk s))))))

(define-syntax projectf
  (syntax-rules ()
    [(_ (x* ...) f)
     (lambda@ (sk fk s)
       (@ (f (reify-nonfresh x* s) ...) sk fk s))]))

(define-syntax fresh   ;;; okay
  (syntax-rules ()
    [(_ (x* ...) a* ...)
     (lambda@ (sk fk s)
       (let ((x* (var 'x*)) ...)
         (@ (all a* ...) sk fk s)))]))

;;; run-stream

(define-syntax run  ;;; okay  (with new reify)
  (syntax-rules ()
    ((_ (x) a a* ...)
     (at-most-one (run-stream (x) a a* ...)))))

(define at-most-one
  (lambda (strm)
    (cond
      ((null? strm) #f)
      (else (reify-answer (car strm))))))

(define-syntax run-stream ;;; okay
  (syntax-rules ()
    ((_ (x) a* ...)
     (let ((x (var 'x)))
       (@ (all a* ...)
          (lambda@ (fk s)
            (cons (answer x s) fk))
          (lambda@ () '())
          empty-s)))))

(define answer
  (lambda (x s)
    (cons x s)))

;;; run-stream

(define-syntax run* ;;; okay
  (syntax-rules ()
    ((_ (x) a a* ...)
     (prefix* (run-stream (x) a a* ...)))))

(define-syntax run$ ;;; okay
  (syntax-rules ()
    ((_ (x) a a* ...)
     (prefix 10 (run-stream (x) (all a a* ...))))))

;;; a stream is either empty or a pair whose cdr is 
                ;;; a function of no arguments that returns a stream.

(define succeed (lambda@ (sk) sk))  

(define fail (lambda@ (sk fk s) (fk))) ;;; part of the interface

(define-syntax trace-vars
  (syntax-rules ()
    [(_ title ())
     (lambda@ (sk fk subst)
       (printf "~s~n" title)
       (@ sk fk subst))]
    [(_ title (x ...))
     (lambda@ (sk fk subst)
       (for-each (lambda (x_ t) (printf "~s ~a ~s~n" x_ title t))
         '(x ...) (reify-fresh `(,(reify-nonfresh x subst) ...)))
       (newline)
       (@ sk fk subst))]))

;;; ----------------------------------------------

(define twice
  (lambda (a)
    (lambda@ (sk fk s)
      (let ((like-sk (lambda@ (fk^ s^)
                       (lambda (w)
                         (@ sk
                            (cond
                              [w fk]
                              [else (lambda () (@ (fk^) #t))])
                            s^))))
            (like-fk (lambda ()
                       (lambda (w)
                         (fk)))))
        (@ a like-sk like-fk s #f)))))

(define at-most
  (lambda (n)
    (lambda (a)
      (lambda@ (sk fk s)
        (let ((like-sk (lambda@ (fk^ s^)
                          (lambda (w)
                            (@ sk
                              (cond
                               [(= w 0) fk]
                               [else (lambda () (@ (fk^) (- w 1)))])
                              s^))))
              (like-fk (lambda ()
                         (lambda (w)
                           (fk)))))
          (@ a like-sk like-fk s (- n 1)))))))

(define handy
  (lambda (x y q)
    (project (x y) (== (+ x y) q))))

(define test-0 ;;; tests with-sk
  (prefix 2
    (run-stream (q)
      (fresh (x y)
        (all
          (any
            (with-sk
              (lambda (sk)
                (all
                  (== 8 x)
                  (all (== 9 y) sk (== 9 x)))))
            (all (== 2 x) (== 3 y)))
          (handy x y q))))))

(pretty-print `(,test-0
                = (17 5)))

(define test-1 ;;; tests with-fk
  (prefix 4
    (run-stream (q)
      (any
        (with-fk
          (lambda (fk)
            (any (== 2 q)
              (any (== 3 q) fk (== 4 q)))))
        (any (== 5 q) (== 6 q))))))

(pretty-print `(,test-1
                = (2 3 5 6)))

(define test-2 ;;; tests with-substitution
  (run* (q)
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
            (== 20 q)))))))

(pretty-print `(,test-2 = (9 20)))

;;; mini-test

(define test-3
  (prefix 2 (run-stream (q)
              (fresh (x y)
                (all
                  (any (== y 3) (== y 4))
                  (all (== x 4)
                    (all
                      (once (any (== x 4) (== x 5)))
                      (handy x y q))))))))

(pretty-print `(,test-3 = (7 8)))


(define test-4
  (prefix 2
    (run-stream (q)
      (fresh (x y)
        (all
          (ef (any
                (== 3 y)
                (all
                  (== 4 y)
                  (== x 3)))
            (any
              (== 5 x)
              (== 4 y))
            (== 5 y))
          (handy x y q))))))

(pretty-print `(,test-4
                = (8 7)))

(define test-5 ;;; twice
  (prefix 2
    (run-stream (q)
      (fresh (x y)
        (twice
          (all
            (any
              (all (== x 3) (== y 4))
              (any
                (all (== x 6) (== y 10))
                (all (== x 7) (== y 14))))
            (handy x y q)))))))

(pretty-print `(,test-5
                = (7 16)))
          
(define test-6 ;;; (at-most 2)
  (prefix 2
    (run-stream (q)
      (fresh (x y)
        ((at-most 2)
         (all
           (any
             (all (== x 3) (== y 4))
             (any
               (all (== x 6) (== y 10))
               (all (== x 7) (== y 14))))
           (handy x y q)))))))

(pretty-print `(,test-6
                = (7 16)))

(define test-7  ;;; tests bi-anyi
  (prefix 9
    (run-stream (x)
      (bi-anyi
        (any (== x 3)
          (any
            (bi-anyi
              (any (== x 20) (== x 21))
              (any (== x 30) (== x 31)))
            (== x 5)))
        (any (== x 13)
          (any (== x 14) (== x 15)))))))

(pretty-print
  `(,test-7
    = (3 13 20 14 30 15 21 31 5)))

(define-syntax forget-me-not
  (syntax-rules ()
    [(_ (x* ...) a* ...)
     (forget-me-not-aux () (x* ...) (x* ...) a* ...)]))

(define-syntax forget-me-not-aux
  (syntax-rules ()
    [(_ (g* ...) () (x* ...) a* ...)
     (with-substitution
       (lambda (s)
         (fresh ()
           a* ...
           (projectf (x* ...) (lambda (g* ...) (all s (== g* x*) ...))))))]
    [(_ (g* ...) (y y* ...) (x* ...) a* ...)
     (forget-me-not-aux (g* ... h) (y* ...) (x* ...) a* ...)]))
       
(define get-s
  (lambda (f)
    (lambda@ (sk fk s)
      (@ (f s) sk fk s))))

(define-syntax ==+
  (syntax-rules ()
    [(_ fv old-s)
     (lambda@ (sk fk s)
       (@ sk fk (multi-extend fv old-s s)))]))

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
    (run (a)
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
                    (lambda@ (sk fk s)
                      (write s)
                      (newline)
                      (@ sk fk s))))))))))))

(define test2
  (lambda ()
    (run (a)
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
                    (lambda@ (sk fk s)
                      (write s)
                      (newline)
                      (@ sk fk s))))))))))))

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
    (run (a)
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
     (lambda@ (sk fk s) 
       (@ (all a* ...) 
          (lambda@ (_fk _s) (@ fk)) 
           (lambda@ () (@ sk fk s)) 
          s)))))


(define alli-like-sk
  (lambda@ (fk s)
    (lambda@ (w)
      (@ (car w) s 
         (lambda@ (sk1 fk1)
           (@ (@ fk) 
              (cons
                (lambda@ (s x)
                  (@ sk1 (lambda () (@ x sk1 fk1)) s))
                fk1)))))))

(define alli-like-fk
  (lambda@ ()
    (lambda@ (w) (@ (cdr w)))))
  
(define-syntax alli
  (syntax-rules ()
    [(_) (all)]
    [(_ a) a]
    [(_ a a* ...)
      (lambda@ (sk fk s)
	(bi-alli sk fk (lambda@ (sk fk) (@ a sk fk s)) (alli a* ...)))]))

(define bi-alli
  (lambda (sk fk sa1 a2)
    (@ (lambda@ (sa) (@ sa alli-like-sk alli-like-fk)) sa1
       (cons
         (lambda@ (s resid)
	   (@ interleave sk fk
              (lambda@ (sk fk) (@ a2 sk fk s))
              (lambda@ (sk fk) (bi-alli sk fk resid a2))))
           fk))))

(define-syntax condi$ 
  (syntax-rules (else)
    ((_ (else a* ...)) (alli a* ...))
    ((_ (a* ...) c* ...) (bi-anyi (alli a* ...) (condi$ c* ...)))))

(define-syntax cond@$
  (syntax-rules (else)
    ((_ (else a* ...)) (alli a* ...))
    ((_ (a* ...) c* ...) (any (alli a* ...) (cond@$ c* ...)))))



; testing alli
(test-check 'alli-1
  (prefix 100
    (run-stream (q)
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
    (run-stream (q)
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
    (run-stream (q)
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
    (run-stream (q)
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
    (run-stream (q)
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
    (run-stream (q)
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
    (run-stream (q)
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
    (run-stream (q)
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
    (run-stream (q) 
      (fresh (x y)
        (R1/2 x y)
        (== `(,x ,y) q)))))
(cout nl "R3/4" nl)
(pretty-print
  (prefix 10
    (run-stream (q) 
      (fresh (x y)
        (R3/4 x y)
        (== `(,x ,y) q)))))

(cout nl "R1/2+R3/4:" nl)
(pretty-print 
  (prefix 10
    (run-stream (q)
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
      (run-stream (q)
        (fresh (x y)
          (Rinf x y)
          (== `(,x ,y) q))))))
(cout nl "Rinf+R1/2: Rinf starves R1/2:" nl)
(time
  (pretty-print 
    (prefix 5
      (run-stream (q)
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
    (run-stream (q)
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
    (run-stream (q)
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
    (run-stream (q)
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

