;	Classical and Intuitionistic logic with Kanren
;
; This file illustrates the use of the typechecking relation (file
; ./type-inference.scm) for proving theorems in Intuitionistic and
; Classical logics.
;
; The type-checking relation, in the term-reconstruction mode,
; reconstructs a term (i.e., a proof) for a type (i.e., a proposition).
; The proposition may contain eigenvariables (for universally-quantified
; variables) and logical variables (for existentially quantified variables),
; and so the de-typechecker is a theorem prover for the fragment of
; intuitionistic predicate logic where all terms are in prenex form.

; $Id$

(load "type-inference.scm")

; Definitions:
;
; Atomic formula (proposition) P is represented by a term of some type P
; (P & Q)  is represented by a term of a type (P * Q)
; (P | Q)                                     (P + Q)
; NOT P                                       P -> F
;
; where F is some distinguished type (which can be abstract for what we
; care).

; we will be using sums, products, and applications. We will be interested
; in the terms in the normal form

; We restrict the app-rel to avoid the redexes. We don't want to generate
; terms with redexes anyway...
; The above prevents call-by-name redexes. We may wish to exclude only CBV
; redexes (lambdas and variables in the operand position). It is interesting
; how it changes the result...
(define appn-rel
  (lambda (s!-)
    (let ((!- (s!- s!-)))
      (lambda (e t)
	(fresh (t-rand rand rator)
	  (== e `(app ,rator ,rand))
	  (fresh (_) (conde ((== rator `(var ,_)))
		            ((== rator `(car (var ,_))))
		            ((== rator `(cdr (var ,_))))
		            (else (== rator `(app . ,_)))))
	  (!- rator `(,t-rand -> . ,t))
	  (!- rand t-rand))))))

(define c!- 
  (make-! lambda-rel appn-rel 	     ; implications, (P ->. Q)
          cons-rel car-rel cdr-rel   ; products, type (P * Q)
          inl-rel inr-rel either-rel ; sums,     type (P + Q)
    ))
(define F 'F)				; The falsity type


;------------------------------------------------------------------------
;			Intuitionistic logic

(test-check "law-of-contradiction"
 (time 
  (map unparse 
    (run 1 (q) (c!- q `(((b -> . F) * b) -> . F)))))
  '((lambda (_.0) ((car _.0) (cdr _.0))))
)

; The result shows that there is a term of the type (((b -> . F) * b) -> . F)
; namely
;   ((lambda (_.0) ((car _.0) (cdr _.0))))
; That term is a proof that the law of contradiction (NOT P & P) -> F
; holds in intuitionistic logic.

(test-check "law-of-conj"
 (time 
  (map unparse 
    (run 1 (q) (c!- q `((a * b) -> . a)))))
  '((lambda (_.0) (car _.0)))
)
; The result proves (A & B) -> A


(test-check "law-of-disj" 
 (time 
  (map unparse 
    (run 1 (q) (c!- q `((a + a) -> . a)))))
 '((lambda (_.0) (either (_.1 _.0) _.1 _.1)))
)
; The result proves (A | A) -> A

(test-check "conseq-of-F"
 (time 
  (map unparse 
    (run 1 (q) (c!- q `(F -> . (a -> . F))))))
  '((lambda (_.0) (lambda (_.1) _.0)))
)

; The result shows that F -> (NOT A) for any A.
; That is, there exists a term, namely, \x -> \k -> x of the type
; F -> (A->F). Which means that falsity entails the negation of any
; formula. Falsity does not entail everything, in intuitionistic logic.

; Another useful law:
(test-check "conseq-of-triple-not"
 (time 
  (map unparse 
    (run 1 (q) (c!- q '((((a -> . F) -> . F) -> . F) -> a -> . F)))))
  '((lambda (_.0) (lambda (_.1) (_.0 (lambda (_.2) (_.2 _.1))))))
)
; which is the proof of
;	NOT NOT NOT A --> NOT A

; Obviously, NOT NOT A does not entail A in intuitionistic logic. But
; the converse does hold:
(test-check "impl-for-double-not"
 (time 
  (map unparse 
    (run 1 (q) (c!- q '(a -> . ((a -> . F) -> . F))))))
  '((lambda (_.0) (lambda (_.1) (_.1 _.0))))
)
; So A -> NOT NOT A.

; De Morgan laws turn out to be more interesting in intuitionistic
; logic: Although
; 	NOT (A | B) -> (NOT A & NOT B)
; as before
; proof:
(test-check "DeMorgan-disj"
 (time 
  (map unparse 
    (run 1 (q) (c!- q '(((a + b) -> . F) -> .
			((a -> . F) * (b -> . F)))))))
  '((lambda (_.0) 
    (cons (lambda (_.1) (_.0 (inl _.1))) (lambda (_.2) (_.0 (inr _.2))))))
)


; It does not intuitionistically follow that
; 	NOT (A & B) -> (NOT A | NOT B)
; Rather, we should have
; 	NOT (A & B) -> NOTNOT (NOT A | NOT B)
; Proof:
(cout nl "DeMorgan-conj will take some 6 secs" nl)
(define (neg x) `(,x -> . F))
(test-check "DeMorgan-conj" 
 (time 
  (map unparse 
    (run 1 (q) (c!- q `(,(neg '(a * b)) -> .
			,(neg (neg `(,(neg 'a) + ,(neg 'b)))))))))
  '((lambda (_.0)
      (lambda (_.1) 
	(_.1 (inl (lambda (_.2) 
		    (_.1 (inr (lambda (_.3) (_.0 (cons _.2 _.3)))))))))))
)

; So, intuitionistically, 
;  NOTNOT (A | B) = NOT( NOT A & NOT B) = NOTNOT (NOTNOT A | NOTNOT B)

;------------------------------------------------------------------------
;			Classical logic
;
; Although lambda-calculus corresponds to intuitionistic logic,
; we can handle classical logic as well, via a double-negation translation:
;
; 	TR(P) ==> NOT NOT P, or (p->F)->F, P is atomic
; 	TR(NOT P) ==> NOT P, or p->F, if P is atomic
; 	TR(NOT A) ==> NOT TR(A) ; for a general formula A

; 	TR(A & B) ==> NOTNOT( TR(A) & TR(B) )
; 	TR(A | B) ==> NOTNOT( TR(A) | TR(B) )
; 	TR(A ->B) ==> NOTNOT( A -> TR(B) )

; Now, regarding the law
; 	TR(NOT P) = NOT P, P atomic
; In general, that should be
; 	TR(NOT A) = NOT (TR A)
; So, for atomic A we get TR(NOT A) = NOT NOT NOT A, but the triple
; negative entails the single one (see above).

;
; The translation has the property that A -> TR(A) is provable
; in intuitionistic logic.  We have already seen the validity of 
; all the cases above but the last one, for the implication.
; For the latter, we ask Kanren to
; derive us the term with the type (A->B) -> NOTNOT (A -> NOTNOT B)

(test-check "tr-impl, or CPS of functions"
 (time 
  (map unparse 
    (run 1 (q) (c!- q `((a -> . b) -> .
		       ,(neg (neg `(a -> . ,(neg (neg 'b))))))))))
  '((lambda (_.0)
      (lambda (_.1)
	(_.1 (lambda (_.2) (lambda (_.3) (_.3 (_.0 _.2))))))))
)

; The result is a CPS translation for functions, btw. So, Kanren
; was able to derive the CPS transform...

; The result A -> TR(A) can be regarded, from the perspective of the
; modal logic, as the law of necessitation, or as a CPS transform, or,
; from the perspective of the translation, that a theorem of
; intuitionistic logic entails the theorem in the translation.

; 	Chung-chieh Shan has pointed out that the above translation
; is, in fact, the NOTNOT translation of Glivenko and
; Kolmogorov. Thus, CPS does prove one direction of
;
;     Glivenko's Theorem: An arbitrary propositional formula A is
; classically provable, if and only if NOTNOTA is intuitionistically
; provable.


; The translation TR is CPS (it's easy to see that's how it was
; derived. The logical justification (as well as terms-as-proof) came
; later, for me. Historically, it was the other way around). Of course,
; the translation from CPS back into the direct style (and introducing
; call/cc where the direct translation demands it) will let us encode
; classical theorems ``directly''.


; We shall see that the translation gives us classical logic indeed. First,
; we attempt to derive a term of the type
; 	((F->F)->F) -> ((A->F)->F)

(test-check "from-F-all-follows"
 (time 
  (map unparse 
    (run 1 (q) (c!- q `(,(neg (neg 'F)) -> . ,(neg (neg 'a)))))))
  '((lambda (_.0) (lambda (_.1) (_.0 (lambda (_.2) _.2)))))
)

; That is, from TR(F) follows TR(A) for any formula A whatsoever. We get
; the classical result that falsity entails everything.

; The most interesting is the following term:

(test-check "LEM"
  (time 
    (map unparse 
      (run 1 (q) (c!- q (neg (neg `(,(neg 'a) + ,(neg (neg 'a)))))))))
  '((lambda (_.0) (_.0 (inr (lambda (_.1) (_.0 (inl _.1)))))))
)

; which proves TR( NOT A | A ). That is, we get the Law of Excluded Middle.

