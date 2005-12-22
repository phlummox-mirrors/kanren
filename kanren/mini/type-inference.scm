; Hindley-Milner type inference and type population (generating a type
; for a term)
; This code is a re-write in mini-Kanren of the type checker in the full
; Kanren: ../examples/type-inference.scm (version 4.50 2005/02/12)
; We use only the second approach from that file.
;
; Future plans: make sure that in the generation phase, all given
; variables are used (or used only once, etc). So, we can generate
; _or_ typecheck terms using uniqueness, linearity, etc. constraints.
; Regarding linearity: the `if' form has to be handled carefully,
; as its two branches are `parallel'.
; Add call/cc or abort as a primitive, and try to generate some formulas
; from classical logic.

; $Id$


(load "book-si.scm")			; Our complete evaluator
(define unify unify-check)		; If we don't want recursive types

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


; We use a subset of Scheme itself as the source language
; The following two functions translate between the source language
; and intermediate one.
; NB: the function parse should actually alpha-convert all lambda-forms
; so that the names of all bound variables are unique. We use this fact later
; in the code. The function 'parse' is somewhat similar to the syntax-rule
; processor in that both produce AST from a surafce language -- and both
; annotate identifiers so that the names of all bound identifiers are unique.

(define parse
  (lambda (e)
    (cond
      ((symbol? e) `(var ,e))
      ((number? e) `(intc ,e))
      ((boolean? e) `(boolc ,e))
      (else 
	(case (car e)
	  ((zero?) `(zero? ,(parse (cadr e))))
	  ((sub1) `(sub1 ,(parse (cadr e))))
	  ((+) `(+ ,(parse (cadr e)) ,(parse (caddr e))))
	  ((if) `(if ,(parse (cadr e)) ,(parse (caddr e)) ,(parse (cadddr e))))
	  ((fix) `(fix ,(parse (cadr e))))
	  ((lambda) `(lambda ,(cadr e) ,(parse (caddr e))))
	  ((let) `(let ((,(car (car (cadr e))) ,(parse (cadr (car (cadr e))))))
		    ,(parse (caddr e))))
	  (else `(app ,(parse (car e)) ,(parse (cadr e)))))))))

(define unparse
  (lambda (e)
    (case (car e)
      ((var) (cadr e))
      ((intc) (cadr e))
      ((boolc) (cadr e))
      ((zero?) `(zero? ,(unparse (cadr e))))
      ((sub1) `(sub1 ,(unparse (cadr e))))
      ((+) `(+ ,(unparse (cadr e)) ,(unparse (caddr e))))
      ((if) `(if ,(unparse (cadr e)) 
	       ,(unparse (caddr e)) ,(unparse (cadddr e))))
      ((fix) `(fix ,(unparse (cadr e))))
      ((lambda) `(lambda (,(car (cadr e))) ,(unparse (caddr e))))
      ((let) 
       `(let ((,(car (car (cadr e)))
               ,(unparse (cadr (car (cadr e))))))
          ,(unparse (caddr e))))
      ((app) `(,(unparse (cadr e)) ,(unparse (caddr e)))))))


; We define a first-class (and recursive) relation !-
; so that (!- `(var ,v) t) holds iff the source term variable v has a type
; t. 
; This variant is close to the `natural deduction' scheme.
; It also has an OO flavor: we need open recursion.

; The following are the separate components of which the relation
; !- will be built. All these components nevertheless receive the full
; !- as the argument. Actually, they will receive the 'self'-like
; argument. We need to explicitly find the fixpoint.

; Integer and boolean constants
(define int-rel
  (lambda (s!-)
    (lambda (e t)
      (fresh (x)
	(== e `(intc ,x))
	(== t 'int)))))

(define bool-rel
  (lambda (s!-)
    (lambda (e t)
      (fresh (x)
	(== e `(boolc ,x))
	(== t 'bool)))))


; types of primitive operations

; (zero? x)

(define zero?-rel
  (lambda (s!-)
    (let ((!- (s!- s!-)))
      (lambda (e t)
	(fresh (x)
	  (== e `(zero? ,x))		; the term
	  (== t 'bool)			; the type
	  (!- x 'int))))))		; provided that x is int

(define sub1-rel
  (lambda (s!-)
    (let ((!- (s!- s!-)))
      (lambda (e t)
	(fresh (x)
	  (== e `(sub1 ,x))		; the term
	  (== t 'int)			; the type
	  (!- x 'int))))))		; provided that x is int

(define +-rel
  (lambda (s!-)
    (let ((!- (s!- s!-)))
      (lambda (e t)
	(fresh (x y)
	  (== e `(+ ,x ,y))		; the term
	  (== t 'int)			; the type
	  (!- x 'int)  (!- y 'int))))))	; provided that x,y are int


(define if-rel
  (lambda (s!-)
    (let ((!- (s!- s!-)))
      (lambda (e t)
	(fresh (test conseq alt)
	  (== e `(if ,test ,conseq ,alt))		; the term
	  (!- test 'bool)		; provided that test is bool
	  (!- conseq t)
	  (!- alt t))))))		; and conseq, alt are of the same type


; Abstraction, application, fixpoint

; Here we extend !- with an additional assumption that v has the type
; type-v. This extension corresponds to a non-generic, regular type.
(define lambda-rel
  (lambda (s!-)
    (lambda (e t)
      (fresh (v tb body type-v)
	(== e `(lambda (,v) ,body))
	(== t `(--> ,type-v ,tb))
	(let* ((snew-!-
		 (lambda (self)
		   (lambda (e t)
		     (conde ; lexically-scoped relation
		       ((== e `(var ,v)) (== t type-v))
		       (else ((s!- self) e t))))))
		(!- (snew-!- snew-!-)))
	  (!- body tb))))))		; check body in so extended env


(define app-rel
  (lambda (s!-)
    (let ((!- (s!- s!-)))
      (lambda (e t)
	(fresh (t-rand rand rator)
	  (== e `(app ,rator ,rand))
	  (!- rator `(--> ,t-rand ,t))
	  (!- rand t-rand))))))

(define fix-rel
  (lambda (s!-)
     (let ((!- (s!- s!-)))
      (lambda (e t)
	(fresh (rand)
	  (== e `(fix ,rand))
	  (!- rand `(--> ,t ,t)))))))

; Let with let-polymorphism
; The reason to test `(!- g rand some-type)' at the very beginning is
; to make sure that `rand' itself is well-typed. As Ken pointed out,
; we must outlaw expressions such as (let ((x (z z))) y) where 'x'
; does not occur in the body. The variable 'x' still must have some
; type.

(define polylet-rel
  (lambda (s!-)
    (let ((!- (s!- s!-)))
      (lambda (e t)
	(fresh (v rand body)
	  (== e `(let ((,v ,rand)) ,body))
	  (fresh (some-type) (!- rand some-type))
	  (let* ((snew-!-
		   (lambda (self)
		     (lambda (e t)
		       (conde
			 ((== e `(var ,v)) (!- rand t))
			 (else ((s!- self) e t))))))
		  (!- (snew-!- snew-!-)))
	    (!- body t)))))))

; Now we build the recursive !- relation, as a fixpoint

(define s!-
  (lambda (self)
    (lambda (e t)
      (conde
	(((int-rel self) e t))
	(((bool-rel self) e t))
	(((zero?-rel self) e t))
	(((sub1-rel self) e t))
	(((+-rel self) e t))
	(((if-rel self) e t))
	(((lambda-rel self) e t))
	(((app-rel self) e t))
	(((fix-rel self) e t))
	(((polylet-rel self) e t))
	))))
	
(define !- (s!- s!-))


;------------------------------------------------------------------------
;			tests


(test-check 'test-!-1
  (run* (q) (!- '(intc 17) 'int))
  '(_.0))

(test-check 'test-!-2
  (run* (q) (!- '(intc 17) q))
  '(int))

(test-check 'test-primitives
  (run* (q) (!- '(zero? (intc 24)) q))
  '(bool))

(test-check 'test-sub1
  (run* (q) (!- '(zero? (sub1 (intc 24))) q))
  '(bool))

(test-check 'test-+
  (run* (q) (!- '(zero? (sub1 (+ (intc 18) (+ (intc 24) (intc 50))))) q))
  '(bool))

(test-check 'test-if
  (run* (q) (!- '(if (zero? (intc 24)) (zero? (intc 3)) (zero? (intc 4))) q))
  '(bool))

(test-check 'test-if-2
  (run* (q) 
    (!- '(if (if (zero? (intc 1)) (boolc #t) (boolc #f))
                     (intc 0)
                     (+ (intc 1) (intc 2)))
      q))
  '(int))


(test-check 'variables-4a
  (run* (q) (!- '(lambda (x) (+ (var x) (intc 5))) q))
  '((--> int int)))


(test-check 'variables-4c
  (run* (q) (!- '(lambda (a) (lambda (x) (+ (var x) (var a)))) q))
  '((--> int (--> int int))))

(test-check 'everything-but-polymorphic-let-1
  (run* (q) 
    (!- (parse
	  '(lambda (f)
	     (lambda (x)
	       ((f x) x))))
      q))
  '((--> (--> _.0 (--> _.0 _.1)) (--> _.0 _.1))))


(test-check 'everything-but-polymorphic-let-2
  (run* (q) 
    (!- (parse
          '((fix (lambda (sum)
                   (lambda (n)
                     (+ n (sum (sub1 n))))))
            10))
      q))
  '(int))

; The following should not typecheck because lambda-binding is not polymorphic
(test-check 'everything-but-polymorphic-let-3
  (run* (q) 
    (!- (parse '((lambda (f)
                   (if (f (zero? 5))
                       (+ (f 4) 8)
                       (+ (f 3) 7)))
                 (lambda (x) x)))
      q))
  '())

; But if we use let, with its let-polymorphis, it works.
(test-check 'polymorphic-let-1
  (run* (q) 
    (!- (parse
          '(let ((f (lambda (x) x)))
             (if (f (zero? 5))
                 (+ (f 4) 8)
                 (+ (f 3) 7))))
      q))
  '(int))


(test-check 'with-robust-syntax
  (run* (q) 
    (!- '(app
           (fix
             (lambda (sum)
               (lambda (n)
                 (if (if (zero? (var n)) (boolc #t) (boolc #f))
                     (intc 0)
                     (+ (var n) (app (var sum) (sub1 (var n))))))))
           (intc 10))
      q))
  '(int))

(test-check "test19"
  (run* (q)
    (!- (parse '((fix (lambda (sum)
                            (lambda (n)
                              (+ n (sum (sub1 n))))))
                     10))
        q))
  '(int))


; Generating a term for a type
(test-check 'type-habitation-1
  (run 5 (q) (!- q 'int))
  '((intc _.0)
    (sub1 (intc _.0))
    (+ (intc _.0) (intc _.1))
    (sub1 (sub1 (intc _.0)))
    (if (boolc _.0) (intc _.1) (intc _.2)))
)

(test-check 'type-habitation-2
  (run 5 (q) (!- q '(--> int int)))
  '((lambda (_.0) (var _.0))
     (if (boolc _.0)
     (lambda (_.1) (var _.1))
       (lambda (_.2) (var _.2)))
     (lambda (_.0) (intc _.1))
     (if (zero? (intc _.0))
       (lambda (_.1) (var _.1))
       (lambda (_.2) (var _.2)))
     (lambda (_.0) (sub1 (var _.0))))
  )

; Note the constants 'a rather than logical variables a:
; 'a is an eigne-value. We want to have the polymorphic type
(test-check 'type-habitation-3
 (run 10 (q) (!- q `(--> (--> a a) (--> a a))))
 '((lambda (_.0) (var _.0))
 (if (boolc _.0)
     (lambda (_.1) (var _.1))
     (lambda (_.2) (var _.2)))
 (app (lambda (_.0) (var _.0)) (lambda (_.1) (var _.1)))
 (if (zero? (intc _.0))
     (lambda (_.1) (var _.1))
     (lambda (_.2) (var _.2)))
 (lambda (_.0) (if (boolc _.1) (var _.0) (var _.0)))
 (if (boolc _.0)
     (if (boolc _.1)
         (lambda (_.2) (var _.2))
         (lambda (_.3) (var _.3)))
     (lambda (_.4) (var _.4)))
 (lambda (_.0) (lambda (_.1) (var _.1)))
 (fix (lambda (_.0) (var _.0)))
 (if (if (boolc _.0) (boolc _.1) (boolc _.2))
     (lambda (_.3) (var _.3))
     (lambda (_.4) (var _.4)))
 (lambda (_.0) (if (zero? (intc _.1)) (var _.0) (var _.0))))
)

(test-check 'type-habitation-4
  (run 10 (q) 
    (fresh (_) (== q `(lambda . ,_)) (!- q `(--> (--> a a) (--> a a)))))
  '((lambda (_.0) (var _.0))
    (lambda (_.0) (if (boolc _.1) (var _.0) (var _.0)))
    (lambda (_.0) (lambda (_.1) (var _.1)))
    (lambda (_.0) (if (zero? (intc _.1)) (var _.0) (var _.0)))
    (lambda (_.0) (app (lambda (_.1) (var _.1)) (var _.0)))
    (lambda (_.0)
     (if (boolc _.1)
       (if (boolc _.2) (var _.0) (var _.0))
       (var _.0)))
 (lambda (_.0)
   (lambda (_.1) (if (boolc _.2) (var _.1) (var _.1))))
 (lambda (_.0)
   (if (if (boolc _.1) (boolc _.2) (boolc _.3))
       (var _.0)
       (var _.0)))
 (lambda (_.0) (let ([_.1 (var _.0)]) (var _.1)))
 (lambda (_.0)
   (if (boolc _.1) (lambda (_.2) (var _.2)) (var _.0))))
  )

; If we wish to find only combinators, we can tell the system what
; kind of terms to use

(define sc!-
  (lambda (self)
    (lambda (e t)
      (conde
	(((lambda-rel self) e t))
	(((app-rel self) e t))
	;(((fix-rel self) e t))
	;(((polylet-rel self) e t))
	))))
	
(define c!- (sc!- sc!-))

(time
  (map unparse
    (run 10 (q) 
      (fresh (_) (== q `(lambda . ,_)) (c!- q `(--> (--> a a) (--> a a)))))))

(cout nl "Some examples from Djinn: inferring morphisms of the continuation
monad" nl)
; Some examples from Djinn: deriving the type of return and call/cc
; in the continuation monad:

;    Djinn> returnC ? a -> C a
;    returnC :: a -> C a
;    returnC x1 x2 = x2 x1

(define (cont a) `(--> (--> ,a r) r))
(display (map unparse (run 1 (q)  (c!- q `(--> a ,(cont 'a))))))
(newline)

;    Djinn> bindC ? C a -> (a -> C b) -> C b
;    bindC :: C a -> (a -> C b) -> C b
;    bindC x1 x2 x3 = x1 (\ c15 -> x2 c15 (\ c17 -> x3 c17))

; Deriving the expression for call/cc and bind is really difficult. So,
; we restrict the app-rel to avoid the redexes. We don't want to generate
; terms with redexes anyway...
; The above prevents call-by-name redexes. We may wish to exclude only CBV
; redexes (lambdas and variables in the operand position). It is interesting
; how it changes the result...
(define app-rel
  (lambda (s!-)
    (let ((!- (s!- s!-)))
      (lambda (e t)
	(fresh (t-rand rand rator)
	  (== e `(app ,rator ,rand))
	  (fresh (_) (conde ((== rator `(var ,_))) 
		            (else (== rator `(app . ,_)))))
	  (!- rator `(--> ,t-rand ,t))
	  (!- rand t-rand))))))

(cout nl "bind" nl)
(cout
(time 
  (map unparse 
    (run 1 (q) 
     (fresh (x1 x2 _) (== q `(lambda (,x1) (lambda (,x2) . ,_)))
      (c!- q `(--> ,(cont 'a) (--> (--> a ,(cont 'b)) ,(cont 'b))))))))
nl)

;    Djinn> type C a = (a -> r) -> r
;    Djinn> callCC ? ((a -> C b) -> C a) -> C a
;   callCC x1 x2 = x1 (\ c15 _ -> x2 c15) (\ c11 -> x2 c11)

(cout nl "call/cc" nl)
(cout
 (time 
  (map unparse 
    (run 1 (q) 
     (fresh (x1 x2 _) (== q `(lambda (,x1) (lambda (,x2) . ,_)))
      (c!- q `(--> (--> (--> a ,(cont 'b)) ,(cont 'a)) ,(cont 'a)))))))
nl)


(cout nl "Inferring the expressions for shift and reset" nl)

(define (cont a r) `(--> (--> ,a ,r) ,r))

(cout nl "reset" nl)
(cout
 (time 
  (map unparse 
    (run 1 (q) 
     (fresh (x1 x2 _) (== q `(lambda (,x1) (lambda (,x2) . ,_)))
      (c!- q `(--> ,(cont 'a 'a) ,(cont 'a 'r)))))))
 nl)

(cout nl "shift" nl)
(cout
 (time 
  (map unparse 
    (run 1 (q) 
     (fresh (x1 x2 _) (== q `(lambda (,x1) (lambda (,x2) . ,_)))
      (c!- q `(--> (--> (--> a ,(cont 'b 'r)) ,(cont 'b 'b)) 
		  ,(cont 'a 'b)))))))
 nl)

