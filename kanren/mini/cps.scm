;			CPS as a relation
;
; $Id$

(load "book-si.scm")			; Our complete evaluator
(define unify unify-check)		; We don't want cyclic terms

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
; CVar   ::= symbol
; CValue ::= (kv CVar) | Exp | (kappa CVar CExp)
; CExp   ::= CValue
; By the property of CPS, all kappa-abstractions are linear.
; Because we will evaluate only terms in the image of the CPS transform
; (which contain no shift, reset, call/cc), we elide the latter.

; Evaluator of kappa-terms. It is the full-beta evaluator. 
; We presume that the input terms are kappa-linear and all CVars are
; unique. That's why we don't have to worry about the hygien
; and we are guaranteed that within the environment, each variable
; occurs only once. 
; The evaluator is pure, and so it can do beta-expansion as well.

(define (kappa-free term result)
  (fresh (v e e2)
    (conde
      ((== term `(var ,v)) (== result #t))
      ((== term `(kv ,v))  (== result #f))
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


; pure lookup relation: find out the  association
; for a given variable in an associative list
; (lookup var lst out) holds if the pair (var . out) occurs in lst.

(define (lookup var lst out)
  (fresh (h t)
    (== lst (cons h t))
    (conde
      ((== h (cons var out)))
      ((lookup var t out)))))


(define (eval-kappa-linear term out)
  (eval-kappa-env term out '() '()))

; See the algorithm in ...
; It is extended here to handle `constants' and non-reducible lambdas
; It is the general evaluator. The only requirement is that
; the term must be closed with respect to kv/kappa.

(define (eval-kappa-env term out env stack)
  (fresh (var body e e2 kff)
   (kappa-free term kff)
   (conde
     ((== kff #t) 		; non-reducible further, no redex
       (eval-unroll term out stack))
     ((== term `(lambda (,var) ,body))	; Do eval under lambda. No redex
       (== kff #f)
       (eval-kappa-env body e env '())
       (eval-unroll `(lambda (,var) ,e) out stack))
     ((== stack '())
      (== term `(kappa ,var ,body))	; Do eval under naked kappa
       (let ((newvar var)) ; (genvar var))) -- don't worry about hygiene...
	 (fresh ()
	 (eval-kappa-env body e (cons (list var '() `(kv ,newvar)) env) '())
	 (== out `(kappa ,newvar ,e)))))
     ((== term `(kappa ,var ,body))	; Redex; kappa with non-empty stack
       (fresh (se newstack)
	 (== stack (cons se newstack))
	 (eval-kappa-env body out
	   (cons (cons var se) env) newstack)))
     ((== env '()) (== term `(kv ,var)) ; variable intr when diving under kappa
       (eval-unroll term out stack))
     ((== term `(kv ,var))		; variable lookup
       (fresh (newenv newterm)
	 (lookup var env (list newenv newterm))
	 (eval-kappa-env newterm out newenv stack)))
    ((== term `(app ,e ,e2))
     (== kff #f)		; the #t case is covered already
     (eval-kappa-env e out env (cons (list env e2) stack)))
     )))

; unroll the stack of applications. We know that there will be
; no redex at the term
(define (eval-unroll term out stack)
  (conde
    ((== stack '()) (== term out))
    (else
      (fresh (env newterm newstack e)
	(== stack (cons (list env newterm) newstack))
	(eval-kappa-env newterm e env '())
	(eval-unroll `(app ,term ,e) out newstack)))))


(test-check 'eval-1
  (run 10 (q) (fresh (x) (eval-kappa-linear '(var x) q)))
  '((var x)))

(test-check 'eval-2
  (run 10 (q) (eval-kappa-linear '(kappa x (kv x)) q))
  '((kappa x (kv x))))

(test-check 'eval-expansion
  (run 3 (q) (fresh (x) (eval-kappa-linear q '(var x))))
  '((var x)
 (app (kappa _.0 (var x)) (var _.1))
 (app (kappa _.0 (kv _.0)) (var x))))

(test-check 'eval-3
  (run 10 (q) (eval-kappa-linear 
		 `(app (kappa x (kv x)) (kappa y (kv y))) q))
  '((kappa y (kv y))))

(test-check 'eval-4
  (run 10 (q) (eval-kappa-linear `(app (kappa x (app (kv x) (var x))) 
				     (var kk))
		 q))
  '((app (var kk) (var x))))


(test-check 'eval-5
  (run 10 (q)
      (eval-kappa-linear
	`(app
	   (kappa
	     x
	     (app (kv x)
	       (app (kappa y (app (kv y) (var x))) (kappa z (kv z)))))
	   (var kk))
	q))
  '((app (var kk) (var x))))


; Basic CPS Transform: Fischer

(define (fischer-cps term cps)
  (fresh (v e e* e2)
    (conde
      ((== term `(var ,v))
       (== cps  `(kappa k (app (kv k) ,term))))
      ((== term `(lambda (,v) ,e))
       (fischer-cps e e*)
       (== cps 
	 `(kappa k (app (kv k) (lambda (,v) ,e*)))))
      ((== term `(app ,e ,e2))
       (fresh (e2*)
       (fischer-cps e e*)
       (fischer-cps e2 e2*)
       (== cps 
	 `(kappa k
	    (app ,e* (kappa f
		       (app ,e2* 
			 (kappa n (app (app (kv f) (kv n)) (kv k))))))))))
      ((== term 'call/cc)
	(== cps 
	  '(kappa k
	     (app (kv k)
	       (kappa f
		 (kappa k1
		   (app
		     (app (kv f) (kappa v (kappa k2 (app (kv k1) (kv v)))))
		     (kv k1))))))))
      ((== term `(reset ,e))
	(fischer-cps e e*)
	 (== cps
	   `(kappa k
	      (app (kv k)
		(app ,e* (kappa v (kv v)))))))
		       
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
  '((kappa
   k
   (app (kv k) (lambda (x) (kappa k (app (kv k) (var x))))))))

#!eof

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
