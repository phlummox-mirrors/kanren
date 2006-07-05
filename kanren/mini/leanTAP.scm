;			leanTAP theorem prover
;
; A simple, elegant and efficient theorem prover for the full classical
; first-order predicate logic. The prover is based on semantic tableaux.

;@article{ beckert95leantap,
;    author = "Bernhard Beckert and Joachim Posegga",
;    title = "{leanTAP}: Lean Tableau-based Deduction",
;    journal = "Journal of Automated Reasoning",
;    volume = "15",
;    number = "3",
;    pages = "339-358",
;    year = "1995",
;    url = "http://citeseer.ist.psu.edu/beckert95leantap.html"


;(load "scheduling.scm")
(load "book-si.scm")

;------------------------------------------------------------------------
; Part I. Converting a formula in the full first-order predicate calculus
; into the negation normal form (NNF). See Section 3 of the paper.
;
; Syntax of the negation normal form:
; term: a variable, an atom, or (f term1 term2 ...)
;       where f is a function symbol.
; positive literal: 
;   (p term1 ...) where p is a predicate symbol (that is, a symbol!)
; negative literal:
;   (not positive-literal)
; literal: 
;   negative or positive literal
; NNF formula:
;   literal
;   (and formula1 formula2 ...)
;   (or  formula1 formula2 ...)
;   (forall varsymbol procedure) where procedure is of type variable -> formula
;   and varsymbol is a symbol (used only for pretty-printing)

; Syntax of the full formulas:
;   literal
;   (and full-formula1 full-formula2 ...)
;   (or  full-formula1 full-formula2 ...)
;   (not full-formula)
;   (=>  full-formula1 full-formula2)
;   (<=> full-formula1 full-formula2)
;   (forall varsymbol procedure)
;   (ex  varsymbol procedure)
;     where procedure is of type variable -> full-formula
;     and varsymbol is a symbol (used only for pretty-printing)

; some syntactic sugar for quantifiers
(define-syntax A
  (syntax-rules ()
    ((A var body) `(forall var ,(lambda (var) `body)))))

(define-syntax E
  (syntax-rules ()
    ((E var body) `(ex var ,(lambda (var) `body)))))

; Pelletier problem 35
(define pelletier-35
  `,(E x ,(E y (=> (p ,x ,y) ,(A x ,(A y (p ,x ,y)))))))

(define (show-formula fml)
  (cond
    ((not (pair? fml)) fml)
    ((eq? (car fml) 'forall) (let ((var (cadr fml)))
			       `(A ,var ,(show-formula ((caddr fml) var)))))
    ((eq? (car fml) 'ex) (let ((var (cadr fml)))
			       `(E ,var ,(show-formula ((caddr fml) var)))))
    (else (cons (car fml) (map show-formula (cdr fml))))))


; (show-formula pelletier-35)

; A simple linear pattern matcher
; It is efficient (generates code at macro-expansion time) and simple:
; it should work on any R5RS Scheme system.


; (match-case-simple exp <clause> ...[<else-clause>])
; <clause> ::= (<pattern> <guard> exp ...)
; <else-clause> ::= (else exp ...)
; <guard> ::= boolean exp | ()
; <pattern> :: =
;        ,var  -- matches always and binds the var
;                 pattern must be linear! No check is done
;         _    -- matches always
;        'exp  -- comparison with exp (using equal?)
;        exp   -- comparison with exp (using equal?)
;        (<pattern1> <pattern2> ...) -- matches the list of patterns
;        (<pattern1> . <pattern2>)  -- ditto
;        ()    -- matches the empty list

(define-syntax match-case-simple
  (syntax-rules ()
    ((_ exp clause ...)
      (let ((val-to-match exp))
	(match-case-simple* val-to-match clause ...)))))

(define (match-failure val)
  (error "failed match" val))

(define-syntax match-case-simple*
  (syntax-rules (else)
    ((_ val (else exp ...))
      (let () exp ...))
    ((_ val)
      (match-failure val))
    ((_ val (pattern () exp ...) . clauses)
      (let ((fail (lambda () (match-case-simple* val . clauses))))
	  ; note that match-pattern may do binding. Here,
	  ; other clauses are outside of these binding
	(match-pattern val pattern (let () exp ...) (fail))))
    ((_ val (pattern guard exp ...) . clauses)
      (let ((fail (lambda () (match-case-simple* val . clauses))))
	(match-pattern val pattern
	  (if guard (let () exp ...) (fail))
	  (fail))))
))


; (match-pattern val pattern kt kf)
(define-syntax match-pattern
  (syntax-rules (_ quote unquote)
    ((_ val _ kt kf) kt)
    ((_ val () kt kf)
      (if (null? val) kt kf))
    ((_ val (quote lit) kt kf)
      (if (equal? val (quote lit)) kt kf))
    ((_ val (unquote var) kt kf)
      (let ((var val)) kt))
    ((_ val (x . y) kt kf)
      (if (pair? val)
	(let ((valx (car val))
	      (valy (cdr val)))
	  (match-pattern valx x
	    (match-pattern valy y kt kf)
	    kf))
	kf))
    ((_ val lit kt kf)
      (if (equal? val (quote lit)) kt kf))))


; Convert a closed full-formula into NNF. This is a deterministic
; procedure. Because our evaluator is different for Prolog, the NPATH
; contraption in the paper is less useful. It's a hassle to implement anyway.

; (define (show-formula1 fml)
;   (cond
;     ((not (pair? fml)) fml)
;     ((eq? (car fml) 'forall) (let ((var (gensym)))
; 			       `(A ,var ,(show-formula1 ((caddr fml) var)))))
;     ((eq? (car fml) 'ex) (let ((var (gensym)))
; 			       `(E ,var ,(show-formula1 ((caddr fml) var)))))
;     (else (cons (car fml) (map show-formula1 (cdr fml))))))

(define (nnf fml)
  (match-case-simple fml

    ; trivial re-writing using the standard tautologies
    ((not (not ,a)) ()
      (nnf  a))
    ((not (forall ,var ,gfml)) ()
      (nnf  `(ex ,var ,(lambda (x) `(not ,(gfml x))))))
    ((not (ex ,var ,gfml)) ()
      (nnf  `(forall ,var ,(lambda (x) `(not ,(gfml x))))))
    ((not (and . ,fmls)) ()
      (nnf  `(or ,@(map (lambda (x) `(not ,x)) fmls))))
    ((not (or . ,fmls)) ()
      (nnf  `(and ,@(map (lambda (x) `(not ,x)) fmls))))
    ((=> ,a ,b) ()
      (nnf  `(or (not ,a) ,b)))
    ((not (=> ,a ,b)) ()
      (nnf  `(and ,a (not ,b))))
    ((<=> ,a ,b) ()
      (nnf  `(or (and ,a ,b) (and (not ,a) (not ,b)))))
    ((not (<=> ,a ,b)) ()
      (nnf  `(or (and (not ,a) ,b) (and ,a (not ,b)))))

    
    ; propagate inside
    ((forall ,var ,gfml) ()
      `(forall ,var 
	 ,(lambda (x) (nnf (gfml x)))))
    ((and . ,fmls) ()
      `(and ,@(map (lambda (x) (nnf  x)) fmls)))
    ((or . ,fmls) ()
      `(or ,@(map (lambda (x) (nnf  x)) fmls)))

    ; skolemization. See the paper
    ((ex _ ,gfml) ()
	     ; replace quantified var with a constant. We use `sk' for clarity
      (let* ((fml-ex `(sk ,(show-formula (gfml 'ex))))
	     (fml-sk (gfml fml-ex))) ; replace qu. var. with skolem function
	(nnf  fml-sk)))

    ; handle literals
    (else fml)))

; test from the paper, p. 6, footnote-9
(define (test-fn9)
  (show-formula
    (nnf `,(A y ,(E x (p ,x ,y))))))

; (show-formula (nnf `,(E x ,(A y (== ,x ,y)))))
; ((caddr (nnf `,(E x ,(A y (== ,x ,y))))) 1)
; (show-formula (nnf `,(A x ,(E y (== ,x ,y)))))
; ((caddr (nnf `,(A x ,(E y (== ,x ,y))))) 1)

(define test-f1t `(=> ,(A x (p ,x)) ,(E x (p ,x))))
(define test-f1f `(=> ,(E x (p ,x)) ,(A x (p ,x))))

; (show-formula (nnf test-f1t))
; (show-formula (nnf test-f1f))


;------------------------------------------------------------------------
;			The prover itself
; (prove nnf-formula '() '() proof)
; succeeds if the NNF formula is derivable. The variable proof is unified
; with the proof (note that the paper did not show the proof!)

; potentially, need safe-condu and safe-conda of the syntax
; (safe-condu ((a b c) test exp ...) ...)
; where the only variable that can be bound during test are the ones that
; are explicitly enumerated here...



(define (prove fml unexpl literals proof)
  (fresh (a b u var)
    ; just a trace comment...
;   (project (fml unexpl literals)
;     (begin (cout "prove: " (show-formula fml) 
; 	     nl unexpl
;             nl
; 	     literals nl)
;       succeed))
  (condu
    ((all (== fml `(and ,a . ,b)) (appendo b unexpl u))
      (prove a u literals proof))	; try a first and b later
    ((== fml `(or ,a))
      (prove a unexpl literals proof))
    ((== fml `(or ,a . ,b))		; have to close both a and bs
      (fresh (p1 p2)
	(prove a unexpl literals p1)
	(prove `(or . ,b) unexpl literals p2)
	(appendo p1 p2 proof)))
    ((all (== fml `(forall ,var ,a))	; instantiate univ quantified fml
	  (appendo unexpl (list fml) u)); put the original formula to the back!
      (conde (fail) (else succeed))
      (fresh (x1)			; divergence may occur here
	(project (a) (prove (a x1) u literals proof))))
    (else				; fml must be a literal
      (letrec ((close-branch
		 (lambda (literals proof)
		   (fresh (neg l lrest)
		     (== literals (cons l lrest))
		     (condu
		       ((conde ((== fml `(not ,neg))) ((== `(not ,fml) neg)))
                        (project (neg) 
                          (begin
			     (let* ((lit
				     (if (and (pair? neg) (eq? 'not (car neg)))
                                         (cadr neg) neg))
                                    (hd (if (pair? lit) (car lit) lit)))
			       (if (not (memq hd '(sk f g h i j k l p q r s ff fp gf gp = t i n)))
                                   (error "bad lit" hd)))
			     succeed))
                        (conde		; the first choice point
			   ((==-check neg l) (== proof (list l)))
			   (else (close-branch lrest proof)))))))))
	(conde				; the second choice point
	  ((close-branch literals proof) (project () 
					   (begin  ;(cout nl "closed" nl)
					   succeed)))
	  (else
	    (fresh (n)			; or choose another formula
	      (== unexpl (cons n u))
	      (prove n u (cons fml literals) proof)))))))))

(define appendo 
  (lambda (l1 l2 l3)
    (conde
      ((== l1 '()) (== l2 l3))
      (else
        (fresh (x l11 l31)
          (== l1 (cons x l11))
          (== l3 (cons x l31))
          (appendo l11 l2 l31))))))


; provec differs from the above in the `cnt' argument, which
; is the upper bound on the number of application of the `gamma' rule
; (i.e., instantiation of a forall-quantified formula).
; Problems like 43 and 38 can only be proven if the application of the
; gamma rule is strictly restricted, to prevent expanding tableau too much.

(define (provec fml unexpl literals cnt proof)
  (fresh (a b u var)
;   (project (fml unexpl literals)
;     (begin (cout "provec: " cnt " " (show-formula fml) 
; 	     nl unexpl 
; 	     literals nl)
;       succeed))
  (condu
    ((all (== fml `(and ,a . ,b)) (appendo b unexpl u))
      (provec a u literals cnt proof))	; try a first and b later
    ((== fml `(or ,a))
      (provec a unexpl literals cnt proof))
    ((== fml `(or ,a . ,b))		; have to close both a and bs
      (fresh (p1 p2)
	(provec a unexpl literals cnt p1)
	(provec `(or . ,b) unexpl literals cnt p2)
	(appendo p1 p2 proof)))
    ((all (== fml `(forall ,var ,a))	; instantiate univ quantified fml
	  (appendo unexpl (list fml) u)); put the original formula to the back!
      ;(conde (fail) (else succeed))
      (if (positive? cnt) succeed fail)
      (fresh (x1)			; divergence may occur here
	(project (a) (provec (a x1) u literals (- cnt 1) proof))))
    (else				; fml must be a literal
      (letrec ((close-branch
		 (lambda (literals proof)
		   (fresh (neg l lrest)
		     (== literals (cons l lrest))
		     (condu
		       ((conde ((== fml `(not ,neg))) ((== `(not ,fml) neg)))
			 (project (neg) 
			   (begin
			     (let* ((lit
				     (if (and (pair? neg) (eq? 'not (car neg)))
				       (cadr neg) neg))
				     (hd (if (pair? lit) (car lit) lit)))
			       (if (not (memq hd '(sk f g h i j k l p q r s ff fp gf gp = t i n)))
				 (error "bad lit" hd)))
			     succeed))
			 (conde		; the first choice point
			   ((==-check neg l) (== proof (list l)))
			   (else (close-branch lrest proof)))))))))
	(conde				; the second choice point
	  ((close-branch literals proof) (project () 
					   (begin  ;(cout nl "closed" nl)
					   succeed)))
	  (else
	    (fresh (n)			; or choose another formula
	      (== unexpl (cons n u))
	      (provec n u (cons fml literals) cnt proof)))))))))
 
(define problem-01 `,(A x (=> ,x ,x)))
; (show-formula (nnf problem-01))
; (run 1 (q) (prove (nnf problem-01) '() '() q))
; (run 1 (q) (prove (nnf `(not ,problem-01)) '() '() q))


; prove a theorem given some axioms. Axioms may be empty
(define (do-prove-th axioms theorem)
  (cout nl "Axioms: ")
  (map (lambda (x) (cout nl (show-formula x))) axioms) 
  (cout  nl "Theorem: " (show-formula theorem) nl)
  (let* ((neg-formula `(and (not ,theorem) ,@axioms))
	 (nf (nnf neg-formula)))
    (cout "NNF is: " (show-formula nf) nl)
    (cout "The proof is:" 
      (run 1 (q) (provec nf '() '() 5 q))
      nl)))

(define (do-prove-th axioms theorem)
  (cout nl "Axioms: ")
  (map (lambda (x) (cout nl (show-formula x))) axioms) 
  (cout  nl "Theorem: " (show-formula theorem) nl)
  (let* ((neg-formula `(and (not ,theorem) ,@axioms))
	 (nf (nnf neg-formula)))
    (cout "NNF is: " (show-formula nf) nl)
    (cout "The proof is:" 
      (run 1 (q) (prove nf '() '() q))
      nl)))

'(time (do-prove-th '() problem-01))

(define p43 (nnf
  `(and
     (or (and (q a b) (not (q b a))) (and (not (q a b)) (q b a)))
     ;(and (q a b) (not (q b a)))
     ,(A x ,(A y (or (and (q ,x ,y) ,(A z (<=> (f ,z ,x) (f ,z ,y))))
		     (and (not (q ,x ,y))
		          (not (<=> (f (sk ,x ,y) ,x) (f (sk ,x ,y) ,y)))))))
   )))
;(cout (run 1 (q) (provec p43 '() '() 5 q)) nl)

; (cout nl "Pelletier problem 43" nl)
; (time (do-prove-th
;   `(
;      ,(A x ,(A y (or (and (q ,x ,y) ,(A z (<=> (f ,z ,x) (f ,z ,y))))
; 		     (and (not (q ,x ,y))
; 		          (not (<=> (f (sk ,x ,y) ,x) (f (sk ,x ,y) ,y)))))))
;    )
;   `,(A x ,(A y (<=> (q ,x ,y) (q ,y ,x))))))

 
(define problem-02 `,(A x (=> ,x ,(A y (=> ,y ,x)))))
(do-prove-th '() problem-02)

(do-prove-th '() test-f1t)
(do-prove-th '() test-f1f) ; it fails to prove!



; Pelletier problems. Source:
; http://www.cs.cmu.edu/afs/cs/project/ai-repository/ai/areas/reasonng/atp/problems/atp/

; Full Predicate Logic (without Identity and Functions). Problem #35.

; (Ex)(Ey)(Pxy -> (Ax)(Ay)Pxy).

(cout nl "Pelletier problem 35" nl)
(define pelletier-35
  `,(E x ,(E y (=> (p ,x ,y) ,(A x ,(A y (p ,x ,y)))))))
(time (do-prove-th '() pelletier-35))


; Full Predicate Logic (without Identity and Functions). Problem #36.
; (Ax)(Ey)Fxy
; (Ax)(Ey)Gxy
; (Ax)(Ay)((Fxy | Gxy) -> (Az)((Fyz | Gyz) -> Hxz)) 
; -------------------------------------------------
; (Ax)(Ey)Hxy

(cout nl "Pelletier problem 36" nl)
(time (do-prove-th
  `(
     ,(A x ,(E y (f ,x ,y)))
     ,(A x ,(E y (g ,x ,y)))
     ,(A x ,(A y (=> (or (f ,x ,y) (g ,x ,y))
		   ,(A z (=> (or (f ,y ,z) (g ,y ,z)) (h ,x ,z))))))
   )
  `,(A x ,(E y (h ,x ,y)))))


     
; Full Predicate Logic (without Identity and Functions). Problem #37.
; (Az)(Ew)(Ax)(Ey)[(Pxz -> Pyw) & Pyz & (Pyw -> (Eu)Quw)]
; (Ax)(Az)[-Pxz -> (Ey)Qyz]
; (Ex)(Ey)Qxy -> (Ax)Rxx
; ---------------------------------------------
; (Ax)(Ey)Rxy

(cout nl "Pelletier problem 37" nl)
(time (do-prove-th
  `(
     ,(A z ,(E w ,(A x ,(E y
			  (and (=> (p ,x ,z) (p ,y ,w)) 
			       (p ,y ,z)
			       (=> (p ,y ,w) ,(E u (q ,u ,w))))))))
     ,(A x ,(A z (=> (not (p ,x ,z)) ,(E y (q ,y ,z)))))
     (=> ,(E x ,(E y (q ,x ,y))) ,(A x (r ,x ,x)))
  )
  `,(A x ,(E y (r ,x ,y)))))


; Natural Language Description:
;
; Full Predicate Logic (without Identity and Functions). Problem #43.
;             - De Champeaux, 1979.
;
; Define set equality ('Q') as having exactly the same members. Prove
; set equality is symmetric.
;
; (Ax)(Ay)(Qxy <-> (Az)(Fzx <-> Fzy))
; ----------------------------------
;    (Ax)(Ay)(Qxy <-> Qyx)

(cout nl "Pelletier problem 43" nl)
(time (do-prove-th
  `(
     ,(A x ,(A y (<=> (q ,x ,y) ,(A z (<=> (f ,z ,x) (f ,z ,y))))))
   )
  `,(A x ,(A y (<=> (q ,x ,y) (q ,y ,x))))))


; The leanTAP paper says this problem is quite hard
;
; Full Predicate Logic (without Identity and Functions).
;
; This is problem #38 from "Seventy-five Problems for Testing
; Automated Theorem Provers", paper by Francis Jeffry Pelletier.
;
; {(Ax)[Pa & (Px -> (Ey)(Py & Rxy)) -> (Ez)(Ew)(Pz & Rxw & Rwz)] <->
; (Ax)[-Pa + Px + (Ez)(Ew)Pz & Rxw & Rwz)) &
; (-Pa + -(Ey)(Py & Rxy) + (Ez)(Ew)(Pz & Rxw & Rwz))]}

(cout nl "Pelletier problem 38" nl)
(time (do-prove-th '() 			; no axioms
  `(<=>
     ,(A x (=> (and (p a) (=> (p ,x) ,(E y (and (p ,y) (r ,x ,y)))))
	       ,(E z ,(E w (and (p ,z) (r ,x ,w) (r ,w ,z))))))

     ,(A x (and
	     (or (not (p a)) (p ,x) 
	       ,(E z ,(E w (and (p ,z) (r ,x ,w) (r ,w ,z)))))
	     (or (not (p a))
	         (not ,(E y (and (p ,y) (r ,x ,y))))
	        ,(E z ,(E w (and (p ,z) (r ,x ,w) (r ,w ,z))))))))
))

; Full Predicate Logic (without Identities and Functions). Problem #44
; (Ax)[Fx -> (Ey)(Gy & Hxy) & (Ez)(Gz & -Hxz)]
; (Ex)[Jx & (Ay)[Gy -> Hxy]]
; ---------------------------
; (Ex)(Jx & -Fx)

(cout nl "Pelletier problem 44" nl)
(time (do-prove-th
  `(
     ,(A x (=> (f ,x) (and ,(E y (and (g ,y) (h ,x ,y)))
			   ,(E z (and (g ,z) (not (h ,x ,z)))))))
     ,(E x (and (j ,x) ,(A y (=> (g ,y) (h ,x ,y)))))
   )
  `,(E x (and (j ,x) (not (f ,x))))))



; Full Predicate Logic (without Identities and Functions). Problem #45.
;
; (Ax)(Fx & (Ay)[Gy & Hxy -> Jxy] -> (Ay)(Gy & Hxy -> Ky))
; -(Ey)(Ly & Ky)
; (Ex)[Fx & (Ay)(Hxy -> Ly) &
; ---------------------------
; (Ay)(Gy & Hxy -> Jxy)]
; ----------------------
; (Ex)(Fx & -(Ey)(Gy & Hxy))

(cout nl "Pelletier problem 45" nl)
(time (do-prove-th
  `(
     ,(A x (=>
	     (and (f ,x) ,(A y (=> (and (g ,y) (h ,x ,y)) (j ,x ,y))))
	     ,(A y (=> (and (g ,y) (h ,x ,y)) (k ,y)))))
     (not ,(E y (and (l ,y) (k ,y))))
     ,(E x (and (f ,x)
	        ,(A y (=> (h ,x ,y) (l ,y)))
	        ,(A y (=> (and (g ,y) (h ,x ,y)) (j ,x ,y)))))
   )
  `,(E x (and (f ,x) (not ,(E y (and (g ,y) (h ,x ,y))))))))

