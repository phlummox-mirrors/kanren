;;; This was developed by Steve Ganz, Dan Friedman, and Ken Shan from Feb. 12-15th, 2005.
;;; It is based on ideas from "Trampolined Style" and dual-inverted deMorgan Laws.

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (cout "Testing " title nl)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(define nl (string #\newline))

(define (cout . args)
  (for-each (lambda (x)
              (if (procedure? x) (x) (display x)))
            args))

(define errorf
  (lambda (tag . args)
    (printf "Failed: ~s: ~%" tag)
    (apply printf args)
    (error 'WiljaCodeTester "That's all, folks!")))

; T S = S + (G S * S)
; G S = S -> M S
; M S = List (T S)


(define-syntax lambdag@
  (syntax-rules ()
    ((_ (s) e) (lambda (s) e))))

(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

(define rhs cdr)
(define lhs car)
(define var vector)
(define var? vector?)

(define var                                                                    
  (lambda (name)                                                        
    (vector name)))

(define var?
  (lambda (v)
    (vector? v)))
  
 (define empty-s '())
 
(define walk
  (Lambda (x s)
    (cond
      ((assq x s) =>
       (lambda (a)
         (let ((v (rhs a)))
           (cond
             ((var? v) (walk v s))
             (else v)))))
      (else x))))

(define ext-s
  (lambda (x v s)
    (cons `(,x . ,v) s)))
 
(define unify
  (lambda (v w s)
    (let ((v (if (var? v) (walk v s) v))
          (w (if (var? w) (walk w s) w)))
      (cond
        ((eq? v w) s)
        ((var? v) (ext-s v w s))
        ((var? w) (ext-s w v s))
        ((and (pair? v) (pair? w))
         (cond
           ((unify (car v) (car w) s) =>
            (lambda (s)
              (unify (cdr v) (cdr w) s)))
           (else #f)))
        ((equal? v w) s)
        (else #f)))))

(define ext-s-check
  (lambda (x v s)
    (cond
      ((occurs? x v s) #f)
      (else (ext-s x v s)))))

(define occurs?
  (lambda (x v s)
    (cond
      ((var? v)
       (let ((v (walk v s)))
         (cond
           ((var? v) (eq? v x))
           (else (occurs? x v s)))))
      ((pair? v) 
       (or 
         (occurs? x (car v) s)
         (occurs? x (cdr v) s)))
      (else #f))))

(define unify-check
  (lambda (v w s)
    (let ((v (if (var? v) (walk v s) v))
          (w (if (var? w) (walk w s) w)))
      (cond
        ((eq? v w) s)
        ((var? v) (ext-s-check v w s))
        ((var? w) (ext-s-check w v s))
        ((and (pair? v) (pair? w))
         (cond
           ((unify-check (car v) (car w) s) =>
            (lambda (s)
              (unify-check (cdr v) (cdr w) s)))
           (else #f)))
        ((equal? v w) s)
        (else #f)))))

(define walk*
  (lambda (v s)
    (cond
      ((var? v)
       (let ((v (walk v s)))
         (cond
           ((var? v) v)
           (else (walk* v s)))))
      ((pair? v)
       (cons 
         (walk* (car v) s)
         (walk* (cdr v) s)))
      (else v))))

(define reify
  (lambda (v)
    (let ((fx (fresh-vars v)))
      (let ((fn (fresh-names fx)))
        (walk* v (zip-s fx fn))))))
 
(define zip-s
  (lambda (fx fn)
    (cond
      ((null? fx) empty-s)
      (else 
        (ext-s (car fx) (car fn)
          (zip-s (cdr fx) (cdr fn)))))))

(define fresh-vars
  (lambda (v)
    (reverse (fv v '()))))

(define fv
  (lambda (v acc)
    (cond
      ((var? v) 
       (cond
         ((memq v acc) acc)
         (else (cons v acc))))
      ((pair? v) 
       (fv (cdr v) (fv (car v) acc)))
      (else acc))))

(define fresh-names
  (lambda (fx)
    (fn fx 0)))

(define fn
  (lambda (fx c)
    (cond
      ((null? fx) '())
      (else
        (cons (reify-id c)
          (fn (cdr fx) (+ c 1)))))))

(define reify-id
  (lambda (c)
    (string->symbol
      (string-append
        "_."
        (number->string c)))))

(define g-close
  (lambda (g s)
    (cons g s)))

(define-syntax case-thread
  (syntax-rules ()
    ((_ e ((s^) on-done) ((g s) on-doing))
     (let ((t e))
       (cond
         ((or (null? t) (and (pair? (car t)) (var? (caar t))))
	  (let ((s^ t)) on-done))
         (else
	   (let ((g (car t)) 
		 (s (cdr t)))
	     on-doing)))))))

(define succeed (lambdag@ (s) (unit s)))

(define fail (lambdag@ (s) '()))

(define unit (lambdag@ (s) (list s)))

(define bounce
  (lambda (g s)
    (list (g-close g s))))

(define bind
  (lambda (m g)
    (map
      (lambda (t)
	(case-thread t
	  ((s) (g-close g s))
	  ((g2 s) (g-close (lambdag@ (s) (bind (g s) g2)) s))))
      m)))

(define-syntax all
  (syntax-rules ()
    ((_) succeed)
    ((_ g) g)
    ((_ g0 g1 g2 ...)
     (lambdag@ (s1)
       (bind (bounce g0 s1) (all g1 g2 ...))))))

(define-syntax any
  (syntax-rules ()
    ((_) fail)
    ((_ g) g)
    ((_ g1 g2) (lambdag@ (s) (append (g1 s) (bounce g2 s))))
    ((_ g0 g1 g2 ...)
     (any (any g0 g1) g2 ...))))


(define-syntax condo
  (syntax-rules (else)
    ((_) fail)
    ((_ (else g ...)) (all g ...))
    ((_ (g ...) c ...)
     (any (all g ...) (condo c ...)))))

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
	 ((all g0 g ...) s))))))

(define-syntax empty-stream
  (syntax-rules ()
    ((_) #f)))

(define-syntax stream-cons
  (syntax-rules ()
    ((_ s e) (cons s (lambdaf@ () e)))))

(define prefix                   
  (lambda (n)
    (lambda (strm)
      (cond
	((not strm) (quote ()))
	(else
	  (cons (car strm)
	    (cond
	      ((= n 1) (quote ()))
	      (else
		((prefix (- n 1)) ((cdr strm)))))))))))

(define prefix*
  (lambda (strm)
    (cond
      ((not strm) (quote ()))
      (else
	(cons (car strm) (prefix* ((cdr strm))))))))

(define tramp
  (letrec ([tramp (lambda (tq-head tq-tail)
		    (cond
		      ((and (null? tq-head) (null? tq-tail)) (empty-stream))
		      ((null? tq-tail) (tramp '() tq-head))
		      (else
			(case-thread (car tq-tail)
			  ((s) (stream-cons s (tramp tq-head (cdr tq-tail))))
			  ((g s) (tramp (append (g s) tq-head)
				   (cdr tq-tail)))))))])
    (lambda (tq)
      (tramp '() tq))))

(define-syntax run*  
  (syntax-rules ()
    ((_ (x) g0 g ...)
     (let ((y (var 'x)))
       (map reify
	 (raw-run prefix* (var 'x)
	   (lambda (x) (all g0 g ...))))))))

(define raw-run
  (lambda (filter x f)
    (map (lambda (s) (walk* x s))
      (filter (tramp (bounce (f x) empty-s))))))

(define-syntax run 
  (syntax-rules ()
    ((_ n^ (x) g0 g ...)
     (map reify 
       (let ((n n^))
         (cond
           ((zero? n) (quote ()))
           (else
             (raw-run (prefix n) (var 'x)
               (lambda (x)
                 (all g0 g ...))))))))))

(load "logic-tests.scm")
