;			CPS as a relation
;
; $Id$

(load "book-si.scm")			; Our complete evaluator
(define unify unify-check)		; If we don't want recursive types

; The Unit testing framework
(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (test-check title tested-expression expected-result #t))
    ((_ title tested-expression expected-result show-flag)
     (begin
       (cout title "...")
       (let* ((expected expected-result)
              (produced tested-expression))
         (if (equal? expected produced)
             (cout  " works!" nl)
             (error 'test-check
                     "Failed ~s: ~a~%Expected: ~a~%Computed: ~a~%"
                     title 'tested-expression expected produced)))))))

; the syntax of the terms is as follows
;  Var   ::= symbol
;  Value ::= (var Var) | (lambda (Var) Exp) | call/cc
;  Exp   ::= Value | (app Exp Exp) | (reset Exp) | (shift Exp)




; the syntax of CPS terms is a bit different, to emphasize
; administrative lambda (which we call kappa) and full beta.
; CVar   ::= Logic-Var
; CValue ::= CVar | Exp | (kappa CVar CExp)
; CExp   ::= CValue
; By the property of CPS, all kappa-abstractions are linear.

; Evaluator of kappa-terms. It is the full-beta evaluator. Also,
; all terms to evaluate must be LINEAR kappa-terms. That's why we
; can use logic variables for CVar. In a more general case, we ought
; to use deBruin indices.
; The evaluator is pure, and so it can do beta-expansion as well.
; The function is written without any regard to its terminating properties

(define (kappa-free term result)
  (fresh (v e e2)
    (conde
      ((== term `(var ,v)) (== result #t))
      ((== term 'call/cc)  (== result #t))
      ((== term `(reset ,e)) (== result #t)) ; assume no kappas in reset...
      ((== term `(shift ,e)) (== result #t)) ; it isn't in the CPS image...
      ((== term `(lambda (,v) ,e)) (kappa-free e result))
      ((== term `(app ,e ,e2))
       (fresh (re re2)
	 (kappa-free e re)
	 (kappa-free e2 re2)
	 (land re re2 result)))
      ((== term `(kappa ,v ,e)) (== result #f))
)))


(define (land e1 e2 e3)
  (conde
    ((== e1 #t) (== e2 e3))
    ((== e1 #f) (== e3 #f))))

(define (eval-kappa-linear term out)
  (fresh (var body e e2)
   (conde
    ((kappa-free term #t) (== term out)) ; nothing to do
    ((== term `(kappa ,var ,body))	 ; Don't eval under kappa
     (== out term))			 ; (so we never have a naked var)
    ((== term `(app ,e ,e2))		
     (eval-kappa-linear e `(kappa ,var ,body))  ; redex
      (== var e2)
      (eval-kappa-linear body out))
    ((== term `(lambda (,var) ,body))	; Do eval under lambda
      (kappa-free body #f)
      (eval-kappa-linear body e)
      (== out `(lambda (,var) ,e)))
    ((== term `(app ,e ,e2))
      (fresh (re re2)
	(kappa-free e re) (kappa-free e2 re2) (land re re2 #f))
      (fresh (e* e2*)
	(eval-kappa-linear e e*)
	(conde ((kappa-free e* #t)) ((kappa-free e* #f)
	                              (fresh (e1 e2) (== e* `(app ,e1 ,e2)))))
	(eval-kappa-linear e2 e2*)
	(== `(app ,e* ,e2*) out))))))

(test-check 'eval-1
  (run 10 (q) (fresh (x) (eval-kappa-linear '(var x) q)))
  '((var x)))

(test-check 'eval-2
  (run 10 (q) (fresh (x) (eval-kappa-linear `(kappa ,x ,x) q)))
  '((kappa _.0 _.0)))

(test-check 'eval-expansion
  (run 5 (q) (fresh (x) (eval-kappa-linear q `(kappa ,x ,x))))
  '((kappa _.0 _.0)
 (app (kappa _.0 (kappa _.1 _.1)) _.0)
 (app (app (kappa _.0 (kappa _.1 (kappa _.2 _.2))) _.0) _.1)
 (app (kappa _.0 (app (kappa _.1 (kappa _.2 _.2)) _.1)) _.0)
 (app (app (kappa
             _.0
             (kappa _.1 (app (kappa _.2 (kappa _.3 _.3)) _.2)))
           _.0)
      _.1)))

(test-check 'eval-3
  (run 10 (q) (fresh (x y) 
	       (eval-kappa-linear `(app (kappa ,x ,x) (kappa ,y ,y)) q)))
  '((kappa _.0 _.0)))

(test-check 'eval-4
  (run 10 (q) (fresh (x) 
	       (eval-kappa-linear `(app (kappa ,x (app ,x (var x))) (var kk))
		 q)))
  '((app (var kk) (var x))))


(test-check 'eval-5
  (run 1 (q)
    (fresh (x y z)
      (eval-kappa-linear
	`(app
	   (kappa
	     ,x
	     (app ,x
	       (app (kappa ,y (app ,y (var x))) (kappa ,z ,z))))
	   (var kk))
	q)))
  '((app (var kk) (var x))))


; Basic CPS Transform: Fischer

(define (fischer-cps term cps)
  (fresh (v k k1 e e* e2)
    (conde
      ((== term `(var ,v))
       (== cps  `(kappa ,k (app ,k ,term))))
      ((== term `(lambda (,v) ,e))
       (fischer-cps e e*)
       (== cps 
	 `(kappa ,k (app ,k (lambda (,v) ,e*)))))
      ((== term `(app ,e ,e2))
       (fresh (e2* f n)
       (fischer-cps e e*)
       (fischer-cps e2 e2*)
       (== cps 
	 `(kappa ,k
	    (app ,e* (kappa ,f (app ,e2* 
				  (kappa ,n (app (app ,f ,n) ,k)))))))))
      ((== term 'call/cc)
       (fresh (f v k2)
	 (== cps 
	   `(kappa ,k
	      (app ,k
		(kappa ,f
		  (kappa ,k1
		    (app
		      (app ,f (kappa ,v (kappa ,k2 (app ,k1 ,v)))) ,k1))))))))
      ((== term `(reset ,e))
       (fresh (v)
	 (fischer-cps e e*)
	 (== cps
	   `(kappa ,k
	      (app ,k
		(app ,e* (kappa ,v ,v)))))))
		       
      ((== term `(shift ,e))
       (fresh (v x k2)
	 (fischer-cps e e*)
	 (== cps
	   `(kappa ,k
	      (app (app ,e* 
		     (kappa ,x (kappa ,k2 (app ,k2 (app ,k ,x)))))
		(kappa ,v ,v))))))
      )))


(test-check 'cps-simple-1
  (run 10 (q) (fischer-cps '(lambda (x) (var x)) q))
  '((kappa _.0 (app _.0 (lambda (x) (kappa _.1 (app _.1 (var x))))))))


; CPS with some reductions: Sabry and Felleisen's F2 transform
; We use '(var KK) as the initial continuation

(define (f2-cps term cps)
  (fresh (cps1)
    (fischer-cps term cps1)
    (eval-kappa-linear `(app ,cps1 (var KK)) cps)))

; (expand `(CPS (lambda (x) (x x))))
; (lambda (#:k)
;   (#:k (lambda (#:x) (lambda (#:k) (#:x #:x #:k)))))
; CPS transform of ((lambda (x) (x x)) p) is (lambda (k) (pv pv k))


(test-check 'cps-1
  (run 10 (q) (f2-cps '(app (var x) (var x)) q))
  '((app (app (var x) (var x)) (var kk))))

'(test-check 'cps-2
  (run 1 (q) (f2-cps '(lambda (x) (app (var x) (var x))) q))
  '((app (app (var x) (var kk)) (var x))))

(test-check 'cps-call/cc
  (run 1 (q) (f2-cps '(app call/cc call/cc) q))
  '((app (var kk) (kappa _.0 (kappa _.1 (app (var kk) _.0))))))

; CPS transform of (call/cc (call/cc call/cc)) is the same as
; that of (call/cc call/cc).
; CPS transform of (call/cc (call/cc id)) is the same as
; that of (call/cc call/cc).

(test-check 'cps-reset
  (run 10 (q) (f2-cps '(reset (var x)) q))
  '((app (var kk) (var x))))


'(test-check 'cps-3
  (run 10 (q) (f2-cps '(shift (lambda (f) (app (var f) (var x)))) q))
  '((app (var kk) (var x))))



'(run 1 (q) (fischer-cps '(app call/cc call/cc) q))
'(run 4 (q) (f2-cps q '(app (var kk) (var x))))
