;			The body of KANREN
;
; The appropriate prelude (e.g., chez-specific.scm) is assumed.
;
; $Id$

(define-syntax lambda@
  (syntax-rules ()
    ((_ (formal) body0 body1 ...) (lambda (formal) body0 body1 ...))
    ((_ (formal0 formal1 formal2 ...) body0 body1 ...)
     (lambda (formal0)
       (lambda@ (formal1 formal2 ...) body0 body1 ...)))))

(define-syntax @  
  (syntax-rules ()
    ((_ rator rand) (rator rand))
    ((_ rator rand0 rand1 rand2 ...) (@ (rator rand0) rand1 rand2 ...))))

(test-check 'test-@-lambda@
  (@ (lambda@ (x y z) (+ x (+ y z))) 1 2 3)
  6)

'(test-check 'test-@-lambda@
  (@ (lambda@ (x y z) (+ x (+ y z))) 1 2 3)
  42)

(define Y
  (lambda (f)
    ((lambda (u) (u (lambda (x) (lambda (n) ((f (u x)) n)))))
     (lambda (x) (x x)))))

; An attempt to do a limited beta-substitution at macro-expand time
; (define-syntax @    
;   (syntax-rules (syntax-rules)
;     ((_ (syntax-rules sdata ...) rand0 ...)
;       (let-syntax 
; 	((tempname (syntax-rules sdata ...)))
; 	(tempname rand0 ...)))
;     ((_ rator rand0 rand1 ...)
;      (@-simple rator rand0 rand1 ...))))


;  Fk    = () -> Ans
;  Ans   = Nil + [Subst,Fk] or just a conceptual stream of substitutions
;  Sk    = Subst -> Fk -> Ans  
;  Goal  = Subst -> SGoal
;  SGoal = Sk -> Fk -> Ans

;  initial-sk : Sk
;  initial-fk : Fk

(define initial-sk (lambda@ (subst fk)
		     (cons subst fk)))
(define initial-fk (lambda () '()))


; Trivial goals
(define succeed (lambda@ (s k) (@ k s)))  ; eta-reduced
(define fail (lambda@ (s k f) (f)))
(define sfail (lambda@ (k f) (f)))	; Failed SGoal


;------------------------------------------------------------------------
; Making logical variables "scoped" and garbage-collected
;  -----> it was used, but no longer
;  -----> The code is still here, as we plan to come back to this...
;
; A framework to remove introduced variables when they leave their scope.
; To make removing variables easier, we consider the list of subst as a
; "stack". Before we add a new variable, we retain a pointer to the
; stack. Then, when we are about to remove the added variables after their
; scope is ended, we stop at the shared retained substitution, and we know
; that anything below the retained substitution can't possibly contain the
; reference to the variables we're about to remove.
;
; Pruning of substitutions is analogous to environment pruning (aka tail-call
; optimization) in WAM on _forward_ execution.

; LV-ELIM IN-SUBST SUBST ID ....
; remove the bindings of ID ... from SUBST (by composing with the
; rest of subst). IN-SUBST is the mark.
; If we locate IN-SUBST in SUBST, we know that everything below the
; mark can't possibly contain ID ...

; lv-elim-1 VAR IN-SUBST SUBST
; VAR is a logical variable, SUBST is a substitution, and IN-SUBST
; is a tail of SUBST (which may be '()).
; VAR is supposed to have non-complex binding in SUBST
; (see Definition 3 in the document "Properties of Substitutions").
; If VAR is bound in SUBST, the corresponding commitment 
; is supposed to occur in SUBST up to but not including IN-SUBST.
; According to Proposition 10, if VAR freely occurs in SUBST, all such
; terms are VAR itself.
; The result is a substitution with the commitment to VAR removed
; and the other commitments composed with the removed commitment.
; The order of commitments is preserved.

(define lv-elim-1
  (lambda (var in-subst subst)
    (if (eq? subst in-subst) subst
      ; if VAR is not bound, there is nothing to prune
      (let*-and subst ((var-binding (assq var subst)))
	(let ((tv (commitment->term var-binding)))
	  (let loop ((current subst))
	    (cond
	      ((null? current) current)
	      ((eq? current in-subst) current)
	      ((eq? (car current) var-binding)
	       (loop (cdr current)))
	      ((eq? (commitment->term (car current)) var)
	       (cons (commitment (commitment->var (car current)) tv)
		 (loop (cdr current))))
	      (else (cons (car current) (loop (cdr current)))))))))))

; The same but for multiple vars
; To prune multiple-vars, we can prune them one-by-one
; We can attempt to be more efficient and prune them in parallel.
; But we encounter a problem:
; If we have a substitution
;  ((x . y) (y . 1) (a . x))
; Then pruning 'x' first and 'y' second will give us ((a . 1))
; Pruning 'y' first and 'x' second will give us ((a . 1))
; But naively attempting to prune 'x' and 'y' in parallel
; disregarding dependency between them results in ((a . y))
; which is not correct.
; We should only be concerned about a direct dependency:
;  ((x . y) (y . (1 t)) (t . x) (a . x))
; pruning x and y in sequence or in parallel gives the same result:
;  ((t . (1 t)) (a . (1 t)))
; We should also note that the unifier will never return a substitution
; that contains a cycle ((x1 . x2) (x2 . x3) ... (xn . x1))

(define lv-elim
  (lambda (vars in-subst subst)
    (if (eq? subst in-subst)
      subst
      (let ((var-bindings ; the bindings of truly bound vars
	      (let loop ((vars vars))
		(if (null? vars) vars
		  (let ((binding (assq (car vars) subst)))
		    (if binding
		      (cons binding (loop (cdr vars)))
		      (loop (cdr vars))))))))
	(cond
	  ((null? var-bindings) subst) ; none of vars are bound
	  ((null? (cdr var-bindings))
	    ; only one variable to prune, use the faster version
	   (lv-elim-1 (commitment->var (car var-bindings))
	     in-subst subst))
	  ((let test ((vb var-bindings)) ; check multiple dependency
	     (and (pair? vb)
	       (or (let ((term (commitment->term (car vb))))
		     (and (var? term) (assq term var-bindings)))
		 (test (cdr vb)))))
	    ; do pruning sequentially
	   (let loop ((var-bindings var-bindings) (subst subst))
	     (if (null? var-bindings) subst
	       (loop (cdr var-bindings)
		 (lv-elim-1 (commitment->var (car var-bindings))
		   in-subst subst)))))
	  (else				; do it in parallel
	    (let loop ((current subst))
	      (cond
		((null? current) current)
		((eq? current in-subst) current)
		((memq (car current) var-bindings)
		 (loop (cdr current)))
		((assq (commitment->term (car current)) var-bindings) =>
		 (lambda (ct)
		   (cons (commitment (commitment->var (car current)) 
			   (commitment->term ct))
		     (loop (cdr current)))))
		(else (cons (car current) (loop (cdr current))))))))))))

; when the unifier is moved up, move lv-elim test from below up...

; That was the code for the unifier that introduced temp variables
; (define-syntax exists
;   (syntax-rules ()
;     ((_ () gl) gl)
;     ((_ (ex-id) gl)
;      (let-lv (ex-id)
;        (lambda@ (sk fk in-subst)
;          (@ gl
;            (lambda@ (fk out-subst)
;              (@ sk fk (lv-elim-1 ex-id in-subst out-subst)))
;            fk in-subst))))
;     ((_ (ex-id ...) gl)
;      (let-lv (ex-id ...) 
;        (lambda@ (sk fk in-subst)
;          (@ gl
;            (lambda@ (fk out-subst)
;              (@ sk fk (lv-elim (list ex-id ...) in-subst out-subst)))
;            fk in-subst))))))

; For the unifier that doesn't introduce temp variables,
; exists is essentially let-lv
; At present, we don't do any GC.
; Here's the reason we don't do any pruning now:
; Let's unify the variable x with a term `(1 2 3 4 5 ,z). The result
; will be the binding x -> `(1 2 3 4 5 ,z). Let's unify `(1 . ,y) with
; x. The result will be a binding y -> `(2 3 4 5 ,z). Note that the
; bindings of x and y share a tail. Let us now unify z with 42. The
; result will be a binding z->42. So far, so good. Suppose however that
; z now "goes out of scope" (the exists form that introduced z
; finishes). We now have to traverse all the terms in the substitution
; and replace z with its binding. The result will be a substitution
; 	x -> (1 2 3 4 5 42)
; 	y -> (2 3 4 5 42)
; Now, the bindings of x and y do not share anything at all! The pruning
; has broke sharing. If we want to unify x and `(1 . ,y) again, we have
; to fully traverse the corresponding terms again.
; So, to prune variables and preserve sharing, we have to topologically sort
; the bindings first!

(define-syntax exists
  (syntax-rules ()
    ((_ () gl) gl)
    ((_ (ex-id ...) gl)
     (let-lv (ex-id ...) gl))
    ))

;-----------------------------------------------------------
; Sequencing of relations
; Goal is a multi-valued function (which takes
;   subst, sk, fk, and exits to either sk or fk).
; A relation is a parameterized goal.
;
; All sequencing operations are defined on goals.
; They can be "lifted" to relations (see below).
; 

; TRACE-GOAL-RAW TITLE GL -> GL
; Traces all invocations and re-invocations of a goal
; printing subst before and after, in their raw form
(define trace-goal-raw
  (lambda (title gl)
    (let ((print-it
	    (lambda (event subst)
	      (display title) (display " ")
	      (display event) (pretty-print subst) (newline))))
      (lambda@ (subst sk fk)
	(print-it "CALL:" subst)
	(@ gl subst
	  (lambda@ (subst fk)
	    (print-it "RETURN:" subst)
	    (@ sk subst
	      (lambda ()
		(display title) (display " REDO") (newline)
		(fk))
	      ))
	  (lambda ()
	    (display title) (display " FAIL") (newline)
	    (fk))
	  )))))

; Conjunctions
; All conjunctions below satisfy properties
;    ans is an answer of (a-conjunction gl1 gl2 ...) ==>
;       forall i. ans is an answer of gl_i
;    (a-conjunction) ==> success


; (all gl1 gl2 ...)
; A regular Prolog conjunction. Non-deterministic (i.e., can have 0, 1,
; or more answers).
; Properties:
;  (all gl) ==> gl
;  (all gl1 ... gl_{n-1} gln) is a "join" of answerlists of
;        (all gl1 ... gl_{n-1}) and gln

(define-syntax all
  (syntax-rules ()
    ((_) succeed)
    ((_ gl) gl)
    ((_ gl0 gl1 ...)
     (lambda@ (subst sk) (splice-in-gls/all subst sk gl0 gl1 ...)))))

(define-syntax splice-in-gls/all
  (syntax-rules ()
    ((_ subst sk gl) (@ gl subst sk))
    ((_ subst sk gl0 gl1 ...)
     (@ gl0 subst (lambda (subst) (splice-in-gls/all subst sk gl1 ...))))))


; (promise-one-answer gl)
; Operationally, it is the identity.
; It is an optimization directive: if the user knows that an goal
; can produce at most one answer, he can tell the system about it.
; The behavior is undefined if the user has lied.

(define-syntax promise-one-answer
  (syntax-rules ()
    ((_ gl) gl)))

; (all! gl1 gl2 ...)
; A committed choice nondeterminism conjunction
; From the Mercury documentation:

;   In addition to the determinism annotations described earlier, there
;   are "committed choice" versions of multi and nondet, called cc_multi
;   and cc_nondet. These can be used instead of multi or nondet if all
;   calls to that mode of the predicate (or function) occur in a context
;   in which only one solution is needed.
;
; (all! gl) evaluates gl in a single-choice context. That is,
; if gl fails, (all! gl) fails. If gl has at least one answer,
; this answer is returned.
; (all! gl) has at most one answer regardless of the answers of gl.
;   ans is an answer of (all! gl) ==> ans is an answer of gl
; The converse is not true.
; Corollary: (all! gl) =/=> gl
; Corollary: gl is (semi-) deterministic: (all! gl) ==> gl
; (all! (promise-one-answer gl)) ==> gl
;
; By definition, (all! gl1 gl2 ...) ===> (all! (all gl1 gl2 ...))

(define-syntax all!
  (syntax-rules (promise-one-answer)
    ((_) (promise-one-answer (all)))
    ((_ (promise-one-answer gl)) (promise-one-answer gl)) ; keep the mark
    ((_ gl0 gl1 ...)
     (promise-one-answer
       (lambda@ (subst sk fk)
	 (@
	   (splice-in-gls/all subst
	     (lambda@ (subst fk-ign) (@ sk subst fk)) gl0 gl1 ...)
	   fk))))))

; (all!! gl1 gl2 ...)
; Even more committed choice nondeterministic conjunction
; It evaluates all elements of the conjunction in a single answer context
; (all!! gl) ==> (all! gl) =/=> gl
; (all!! gl1 gl2 ...) ==> (all (all! gl1) (all! gl2) ...)
;                       ==> (all! (all! gl1) (all! gl2) ...)
; (all!! gl1 ... gln (promise-one-answer gl)) ==>
;    (all (all!! gl1 ... gln) gl)

(define-syntax all!!
  (syntax-rules ()
    ((_) (all!))
    ((_ gl) (all! gl))
    ((_ gl0 gl1 ...)
     (promise-one-answer 
       (lambda@ (subst sk fk)
         (splice-in-gls/all!! subst sk fk gl0 gl1 ...))))))

(define-syntax splice-in-gls/all!!
  (syntax-rules (promise-one-answer)
    ((_ subst sk fk)
      (@ sk subst fk))
    ((_ subst sk fk (promise-one-answer gl))
      (@ gl subst sk fk))
    ((_ subst sk fk gl0 gl1 ...)
      (@ gl0 subst
	(lambda@ (subst fk-ign) (splice-in-gls/all!! subst sk fk gl1 ...))
	fk))))

; (if-only COND THEN)
; (if-only COND THEN ELSE)
; Here COND, THEN, ELSE are goals.
; If COND succeeds at least once, the result is equivalent to
;      (all (all! COND) TNEN)
; If COND fails, the result is the same as ELSE.
; If ELSE is omitted, it is assumed fail. That is, (if-only COND THEN)
; fails if the condition fails.  "This  unusual semantics
; is part of the ISO and all de-facto Prolog standards."
; Thus, declaratively,
;   (if-only COND THEN ELSE) ==> (any (all (all! COND) THEN)
;                                     (all (fails COND) ELSE))
; Operationally, we try to generate a good code.

; "The majority of predicates written by human programmers are
; intended to give at most one solution, i.e., they are
; deterministic. These predicates are in effect case statements
; [sic!], yet they are too often compiled in an inefficient manner
; using the full generality of backtracking (which implies saving the
; machine state and repeated failure and state restoration)." (Peter
; Van Roy, 1983-1993: The Wonder Years of Sequential Prolog
; Implementation).


(define-syntax if-only
  (syntax-rules ()
    ((_ condition then)
     (lambda@ (subst sk fk)
       (@ condition subst
         ; sk from cond
         (lambda@ (subst fk-ign) (@ then subst sk fk))
         ; failure from cond
         fk)))
    ((_ condition then else)
     (lambda@ (subst sk fk)
       (@ condition subst
         (lambda@ (subst fk-ign) (@ then subst sk fk))
         (lambda () (@ else subst sk fk))
         )))))

; (if-all! (COND1 ... CONDN) THEN)
; (if-all! (COND1 ... CONDN) THEN ELSE)
;
; (if-all! (COND1 ... CONDN) THEN ELSE) ==>
;   (if-only (all! COND1 ... CONDN) THEN ELSE)
; (if-all! (COND1) THEN ELSE) ==>
;   (if-only COND1 THEN ELSE)

; Eventually, it might be a recognized special case in if-only.

; (define-syntax if-all!
;   (syntax-rules ()
;     ((_ (condition) then) (if-only condition then))
;     ((_ (condition) then else) (if-only condition then else))
;     ((_ (condition1 condition2 ...) then)
;      (lambda@ (sk fk)
;        (@ (splice-in-gls/all
;             (lambda@ (fk-ign)
;               (@ then sk fk))
;             condition1 condition2 ...)
;           fk)))
;     ((_ (condition1 condition2 ...) then else)
;      (lambda@ (sk fk subst)
;        (@ (splice-in-gls/all
;             (lambda@ (fk-ign)
;               (@ then sk fk)) condition1 condition2 ...)
;           (lambda ()
;             (@ else sk fk subst))
; 	 subst)))))

; Disjunction of goals
; All disjunctions below satisfy properties
;  ans is an answer of (a-disjunction gl1 gl2 ...) ==>
;    exists i. ans is an answer of gl_i
; (a-disjunction) ==> fail

; Any disjunction. A regular Prolog disjunction (introduces
; a choicepoints, in Prolog terms)
; Note that 'any' is not a union! In particular, it is not
; idempotent.
; (any) ===> fail
; (any gl) ===> gl
; (any gl1 ... gln) ==> _concatenation_ of their answerlists

(define-syntax any
  (syntax-rules ()
    ((_) fail)
    ((_ gl) gl)
    ((_ gl ...)
      (lambda@ (subst sk fk)
	(splice-in-gls/any subst sk fk gl ...)))))

(define-syntax splice-in-gls/any
  (syntax-rules ()
    ((_ subst sk fk gl1) (@ gl1 subst sk fk))
    ((_ subst sk fk gl1 gl2 ...)
     (@ gl1 subst sk (lambda () (splice-in-gls/any subst sk fk gl2 ...))))))


; Negation
; (fails gl) succeeds iff gl has no solutions
; (fails gl) is a semi-deterministic predicate: it can have at most
; one solution
; (succeeds gl) succeeds iff gl has a solution
;
; (fails (fails gl)) <===> (succeeds gl)
; but (succeeds gl) =/=> gl
; Cf. (equal? (not (not x)) x) is #f in Scheme in general.
; Note, negation is only sound if some rules (Grounding Rules) are satisfied.

(define fails
  (lambda (gl)
    (lambda@ (subst sk fk)
      (@ gl subst
        (lambda@ (subst current-fk) (fk))
        (lambda () (@ sk subst fk))
        ))))

; Again, G-Rule must hold for this predicate to be logically sound
(define succeeds
  (lambda (gl)
    (lambda@ (subst sk fk)
      (@ gl subst (lambda@ (subst-ign fk-ign) (@ sk subst fk))
	fk))))

; partially-eval-sgl: Partially evaluate a semi-goal. A
; semi-goal is an expression that, when applied to two
; arguments, sk and fk, can produce zero, one, or more answers.  Any
; goal can be turned into a semi-goal if partially applied
; to subst.  The following higher-order semi-goal takes a
; goal and yields the first answer and another, residual
; goal. The latter, when evaluated, will give the rest of the
; answers of the original semi-goal.  partially-eval-sgl could
; be implemented with streams (lazy lists). The following is a purely
; combinational implementation.
;
; (@ partially-eval-sgl sgl a b) =>
;   (b) if sgl has no answers
;   (a s residial-sgl) if sgl has a answer. That answer is delivered
;                       in s. 
; The residial semi-goal can be passed to partially-eval-sgl
; again, and so on, to obtain all answers from a goal one by one.

; The following definition is eta-reduced.

(define (partially-eval-sgl sgl)
  (@ sgl
    (lambda@ (subst fk a b)
      (@ a subst 
	(lambda@ (sk1 fk1)
	  (@
	    (fk) 
	    ; new a
	    (lambda@ (sub11 x) (@ sk1 sub11 (lambda () (@ x sk1 fk1))))
	    ; new b
	    fk1))))
    (lambda () (lambda@ (a b) (b)))))

; An interleaving disjunction.
; Declaratively, any-interleave is the same as any.
; Operationally, any-interleave schedules each component goal
; in round-robin. So, any-interleave is fair: it won't let a goal
; that produces infinitely many answers (such as repeat) starve the others.
; any-interleave introduces a breadth-first-like traversal of the
; decision tree.
; I seem to have seen a theorem that says that a _fair_ scheduling
; (like that provided by any-interleave) entails a minimal or well-founded
; semantics of a Prolog program.

(define-syntax any-interleave
  (syntax-rules ()
    ((_) fail)
    ((_ gl) gl)
    ((_ gl ...)
     (lambda@ (subst sk fk)
       (interleave sk fk (list (gl subst) ...))))))

; we treat sgls as a sort of a circular list
(define interleave
  (lambda (sk fk sgls)
    (cond
      ((null? sgls) (fk))		; all of the sgls are finished
      ((null? (cdr sgls))
       ; only one of sgls left -- run it through the end
       (@ (car sgls) sk fk))
      (else
        (let loop ((curr sgls) (residuals '()))
	  ; check if the current round is finished
	  (if (null? curr) (interleave sk fk (reverse residuals))
	    (@
	      partially-eval-sgl (car curr)
	      ; (car curr) had an answer
	      (lambda@ (subst residual)
	        (@ sk subst
	          ; re-entrance cont
		  (lambda () (loop (cdr curr) (cons residual residuals)))))
	    ; (car curr) is finished - drop it, and try next
	    (lambda () (loop (cdr curr) residuals)))))))))

; An interleaving disjunction removing duplicates: any-union
; This is a true union of the constituent goals: it is fair, and
; it removes overlap in the goals to union, if any. Therefore,
;    (any-union gl gl) ===> gl
; whereas (any gl gl) =/=> gl
; because the latter has twice as many answers as gl.
;
; Any-union (or interleave-non-overlap, to be precise) is quite similar
; to the function interleave above. But now, the order of goals
; matters. Given goals gl1 gl2 ... glk ... gln,
; at the k-th step we try to partially-eval glk. If it yields an answer,
; we check if gl_{k+1} ... gln can be satisfied with that answer.
; If any of them does, we disregard the current answer and ask glk for
; another one. We maintain the invariant that
;  ans is an answer of (any-union gl1 ... gln) 
;  ===> exists i. ans is an answer of gl_i
;       && forall j>i. ans is not an answer of gl_j
; The latter property guarantees the true union.
; Note the code below does not check if the answers of each individual
; goal are unique. It is trivial to modify the code so that
; any-union removes the duplicates not only among the goals but
; also within a goal. That change entails a run-time cost. More
; importantly, it breaks the property
; (any-union gl gl) ===> gl
; Only a weaker version, (any-union' gl gl) ===> (any-union' gl)
; would hold. Therefore, we do not make that change.

(define-syntax any-union
  (syntax-rules ()
    ((_) fail)
    ((_ gl) gl)
    ((_ gl ...)
     (lambda@ (subst sk fk)
       (interleave-non-overlap sk fk (list (cons (gl subst) gl) ...))))))

; we treat sagls as a sort of a circular list
; Each element of sagls is a pair (sgl . gl)
; where gl is the original goal (needed for the satisfiability testing)
; and sgl is the corresponding semi-goal or a 
; residual thereof.
(define interleave-non-overlap
  (lambda (sk fk sagls)
    (let outer ((sagls sagls))
      (cond
        ((null? sagls) (fk))  ; all of the sagls are finished
        ((null? (cdr sagls))  ; only one gl is left -- run it through the end
	 (@ (caar sagls) sk fk))
        (else
	  (let loop ((curr sagls)
                     (residuals '()))
            ; check if the current round is finished
	    (if (null? curr) (outer (reverse residuals))
                (@
                 partially-eval-sgl (caar curr)
                  ; (caar curr) had an answer
                 (lambda@ (subst residual)
                  ; let us see now if the answer, subst, satisfies any of the
                  ; gls down the curr.
                   (let check ((to-check (cdr curr)))
                     (if (null? to-check) ; OK, subst is unique,give it to user
                         (@ sk subst
                           ; re-entrance cont
                           (lambda ()
                             (loop (cdr curr) 
                               (cons (cons residual (cdar curr)) residuals))))
                         (@ (cdar to-check) subst
                            ; subst was the answer to some other gl:
			    ; check failed
                            (lambda@ (subst1 fk1)
                              (loop (cdr curr) 
                                (cons (cons residual (cdar curr)) residuals)))
                            ; subst was not the answer: continue check
                            (lambda () (check (cdr to-check)))))))
                 ; (car curr) is finished - drop it, and try next
                 (lambda () (loop (cdr curr) residuals))))))))))


; Another if-then-else
; (if-some COND THEN)
; (if-some COND THEN ELSE)
; Here COND, THEN, ELSE are goals.
; If COND succeeds at least once, the result is equivalent to
;      (all COND TNEN)
; If COND fails, the result is the same as ELSE.
; If ELSE is omitted, it is assumed fail. That is, (if-some COND THEN)
; fails if the condition fails.  "This  unusual semantics
; is part of the ISO and all de-facto Prolog standards."
; Thus, declaratively,
;   (if-some COND THEN ELSE) ==> (any (all COND THEN)
;                                     (all (fails COND) ELSE))
; from which follows
;   (if-some COND THEN)              ==> (all COND THEN)
;   (if-some COND THEN fail)         ==> (all COND THEN)
; but
;   (if-some COND succeed ELSE)     =/=> (any COND ELSE)
;
; Other corollary:
;   (if-some COND THEN ELSE) ==> (if-only (fails COND) ELSE (all COND THEN))
;
; Operationally, we try to generate a good code.
;
; In Prolog, if-some is called a soft-cut (aka *->). In Mercury,
; if-some is the regular IF-THEN-ELSE.
;
; We can implement if-some with partially-eval-sgl. Given a COND, we
; peel off one answer, if possible. If there is one, we then execute THEN
; passing it the answer and the fk from COND so that if THEN fails,
; it can obtain another answer. If COND has no answers, we execute
; ELSE. Again, we can do all that purely declaratively, without
; talking about introducing and destroying choice points.

(define-syntax if-some
  (syntax-rules ()
    ((_ condition then) (all condition then))
    ((_ condition then else)
     (lambda@ (subst sk fk)
       (@ partially-eval-sgl (condition subst)
         (lambda@ (ans residual)
           (@ then ans sk
             ; then failed. Check to see if condition has another answer
             (lambda () (@ residual (lambda@ (subst) (@ then subst sk)) fk))))
             ; condition failed
         (lambda () (@ else subst sk fk)))))))


; An interleaving conjunction: all-interleave
;
; This conjunction is similar to the regular conjunction `all' but
; delivers the answers in the breadth-first rather than depth-first
; order.
;
; Motivation.
; Let us consider the conjunction (all gl1 gl2)
; where gl1 is (any gl11 gl12) and gl2 is an goal with the
; infinite number of answers (in the environment when either gl11 or
; gl12 succeed). It is easy to see (all gl1 gl2) will have the
; infinite number of answers too -- but only the proper subset of
; all the possible answers. Indeed, (all gl1 gl2) will essentially
; be equivalent to (all gl11 gl2). Because gl2 succeeds infinitely
; many times, the choice gl12 in gl1 will never be explored.
; We can see that formally:
; (all gl1 gl2) 
;   = (all (any gl11 gl12) gl2) 
;   = (any (all gl11 gl2) (all gl12 gl2))
; Because (all gl11 gl2) can succeed infinitely many times, it starves
; the other disjunction, (all gl12 gl2).
; But we know how to deal with that: we just replace any with any-interleave:
; (all gl1 gl2) --> (any-interleave (all gl11 gl2) (all gl12 gl2))
;
; It seems that the problem is solved? We just re-write our expressions
; into the disjunctive normal form, and then replace the top-level
; `any' with `any-interleave'. Alas, that means that to get the benefit
; of fair scheduling and get all the possible solutions of the conjunction
; (i.e., recursive enumerability), we need to re-write all the code.
; We have to explicitly re-write a conjunction of disjunctions into
; the disjunctive normal form. That is not that easy considering that gl2
; will most likely be a recursive goal re-invoking the original
; conjunction. That would be a lot of re-writing.
;
; The conjunction all-interleave effectively does the above `re-writing'
; That is, given the example above,
;	(all-interleave (any gl11 gl12) gl2)
; is observationally equivalent to
;	(any-interleave (all gl11 gl2) (all gl12 gl2))
;
; The advantage is that we do not need to re-write our conjunctions:
; we merely replace `all' with `all-interleave.'
; 
; How can we do that in the general case, (all gl1 gl2)
; where gl1 is not _explicitly_ a disjunction? We should remember the
; property of partially-eval-sgl: Any goal `gl' with at least one
; answer can be represented as (any gl-1 gl-rest)
; where gl-1 is a primitive goal holding the first answer of `gl',
; and gl-rest holding the rest of the answers. We then apply the
; all-any-distributive law and re-write
; (all-interleave gl1 gl2) 
; ==> (all-interleave (any gl1-1 gl1-rest) gl2) 
; ==> (any-interleave (all gl1 gl2) (all-interleave gl1-rest gl2))
;
; If gl1 has no answers, then (all-interleave gl1 gl2) fails, as
; a conjunction must.
; It is also easy to see that
; (all-interleave gl1 gl2 ...) is the same as
; (all-interleave gl1 (all-interleave gl2 ...))
;
; Although all-interleave was motivated by an example (all gl1 gl2)
; where gl1 is finitary and only gl2 is infinitary, the above
; equations (and the implementation below) show that all-interleave
; can do the right thing even if gl1 is infinitary as well. To be
; precise, given
;
;	(all-interleave gl1 gl2)
;
; with gl1 and gl2 infinitary, the i-th solution of gl1 will be
; observed in every 2^i-th solution to the whole conjunction. Granted,
; all-interleave isn't precisely very fair -- the later solutions of
; gl1 will appear progressively more rarely -- yet, they will all
; appear. The infinity of c0 is big enough. That is, given any
; solution to gl1, we will eventually, in finite time, find it in the
; solution of the whole conjunction (provided gl2 doesn't fail on
; that solution, of course).



(define-syntax all-interleave
  (syntax-rules ()
    ((_) (all))
    ((_ gl) gl)
    ((_ gl0 gl1 ...)
      (lambda@ (subst)
	(all-interleave-bin
	  (gl0 subst) (all-interleave gl1 ...))))))

(define all-interleave-bin
  (lambda (sgl1 gl2)
    (lambda@ (sk fk)
      (@ partially-eval-sgl sgl1
	(lambda@ (ans residual)
	  (interleave sk fk
	    (list 
	      (@ gl2 ans)
	      (all-interleave-bin residual gl2)
	    )))
	  ;gl1 failed
	  fk))))


; Relations...........................

; The current incremented unification of argument passing is quite similar to
; the compilation of argument unifications in WAM.

; relation (VAR ...) (to-show TERM ...) [GL]
; Defines a relation of arity (length '(TERM ...)) with an optional body
; GL. VAR ... are logical variables that are local to the relation, i.e.,
; appear in TERM or GL. It's better to list as VAR ... only logical
; variables that appear in TERM. Variables that appear only in GL should
; be introduced with exists. That makes their existential quantification
; clearer. Variables that appear in TERM are universally quantified.
;
; relation (head-let TERM ...) [GL]
; See relation-head-let below.
;
; relation (ANNOT-VAR ...) (to-show TERM ...) [GL]  (see remark below!)
; where ANNOT-VAR is either a simple VAR or (once VAR)
; where 'once' is a distingushed symbol. The latter form introduces
; a once-var, aka linear variable. A linear variable appears only once in
; TERM ... and only at the top level (that is, one and only one TERM
; in the to-show pattern contains ONCE-VAR, and that term is ONCE-VAR
; itself). In addition, ONCE-VAR must appear at most once in the body GL.
; (Of course, then ONCE-VAR could be _, instead.)
; If these conditions are satisfied, we can replace a logical variable
; ONCE-VAR with a regular Scheme variable.

; Alternative notation:
; (relation (a c) (to-show term1 (once c) term2) body)
; Makes it easier to deal with. But it is unsatisfactory:
; to-show becomes a binding form...
;
; When ``compiling'' a relation, we now look through the
; (to-show ...) pattern for a top-level occurrence of the logical variable
; introduced by the relation. For example:
;	(relation (x y) (to-show `(,x . ,y) x) body)
; we notice that the logical variable 'x' occurs at the top-level. Normally we
; compile the relation like that into the following
;    (lambda (g1 g2)
;      (exists (x y)
;        (lambda@ (subst)
; 	 (let*-and (fail subst) ((subst (unify g1 `(,x . ,y)  subst))
; 			         (subst (unify g2 x subst)))
; 	     (@ body subst)))))
;
; However, that we may permute the order of 'unify g...' clauses
; to read
;    (lambda (g1 g2)
;      (exists (x y)
;        (lambda@ (subst)
; 	 (let*-and (fail subst) ((subst (unify x g2 subst))
; 			         (subst (unify g1 `(,x . ,y)  subst))
; 			         )
; 	     (@ body subst)))))
;
; We may further note that according to the properties of the unifier
; (see below), (unify x g2 subst) must always succeed, 
; because x is a fresh variable.
; Furthermore, the result of (unify x g2 subst) is either subst itself,
; or subst with the binding of x. Therefore, we can check if
; the binding at the top of (unify x g2 subst) is the binding to x. If
; so, we can remove the binding and convert the variable x from being logical
; to being lexical. Thus, we compile the relation as
;
;    (lambda (g1 g2)
;      (exists (x y)
;        (lambda@ (subst)
; 	 (let* ((subst (unify-free/any x g2 subst))
; 	        (fast-path? (and (pair? subst)
; 			         (eq? x (commitment->var (car subst)))))
; 	        (x (if fast-path? (commitment->term (car subst)) x))
; 	        (subst (if fast-path? (cdr subst) subst)))
; 	 (let*-and sfail ((subst (unify g1 `(,x . ,y)  subst))
; 			 )
; 	     (@ body subst))))))
;
; The benefit of that approach is that we limit the growth of subst and avoid
; keeping commitments that had to be garbage-collected later.


(define-syntax relation
  (syntax-rules (to-show head-let once _)
    ((_ (head-let head-term ...) gl)
     (relation-head-let (head-term ...) gl))
    ((_ (head-let head-term ...))	; not particularly useful without body
     (relation-head-let (head-term ...)))
    ((_ () (to-show term ...) gl)	; pattern with no vars _is_ linear
     (relation-head-let (`,term ...) gl))
    ((_ () (to-show term ...))		; the same without body: not too useful
     (relation-head-let (`,term ...)))
    ((_ (ex-id ...) (to-show term ...) gl)  ; body present
     (relation "a" () () (ex-id ...) (term ...) gl))
    ((_ (ex-id ...) (to-show term ...))      ; no body
     (relation "a" () () (ex-id ...) (term ...)))
    ; process the list of variables and handle annotations
    ((_ "a" vars once-vars ((once id) . ids) terms . gl)
     (relation "a" vars (id . once-vars) ids terms . gl))
    ((_ "a" vars once-vars (id . ids) terms . gl)
     (relation "a" (id . vars) once-vars ids terms . gl))
    ((_ "a" vars once-vars () terms . gl)
     (relation "g" vars once-vars () () () (subst) terms . gl))
    ; generating temp names for each term in the head
    ; don't generate if the term is a variable that occurs in
    ; once-vars
    ; For _ variables in the pattern, generate unique names for the lambda
    ; parameters, and forget them
    ; also, note and keep track of the first occurrence of a term
    ; that is just a var (bare-var) 
    ((_ "g" vars once-vars (gs ...) gunis bvars bvar-cl (_ . terms) . gl)
     (relation "g" vars once-vars (gs ... anon) gunis
       bvars bvar-cl terms . gl))
    ((_ "g" vars once-vars (gs ...) gunis bvars (subst . cls)
           (term . terms) . gl)
     (id-memv?? term once-vars 
       ; success continuation: term is a once-var
       (relation "g" vars once-vars (gs ... term) gunis bvars (subst . cls)
	 terms . gl)
       ; failure continuation: term is not a once-var
       (id-memv?? term vars
	 ; term is a bare var
	 (id-memv?? term bvars
	   ; term is a bare var, but we have seen it already: general case
	   (relation "g" vars once-vars  (gs ... g) ((g . term) . gunis) 
	     bvars (subst . cls) terms . gl)
	   ; term is a bare var, and we have not seen it
	   (relation "g" vars once-vars (gs ... g) gunis
	     (term . bvars)
	     (subst
	       (subst (unify-free/any term g subst))
	       (fast-path? (and (pair? subst)
			      (eq? term (commitment->var (car subst)))))
	       (term (if fast-path? (commitment->term (car subst)) term))
	       (subst (if fast-path? (cdr subst) subst))
	       . cls)
	     terms . gl))
	 ; term is not a bare var
	 (relation "g" vars once-vars  (gs ... g) ((g . term) . gunis) 
	   bvars (subst . cls) terms . gl))))
    ((_ "g" vars once-vars gs gunis bvars bvar-cl () . gl)
     (relation "f" vars once-vars gs gunis bvar-cl . gl))

    ; Final: writing the code
    ((_ "f" vars () () () (subst) gl)   ; no arguments (no head-tests)
      (lambda ()
	(exists vars gl)))
                                    ; no tests but pure binding
    ((_ "f" (ex-id ...) once-vars (g ...) () (subst) gl)
     (lambda (g ...)
       (exists (ex-id ...) gl)))
				    ; the most general
    ((_ "f" (ex-id ...) once-vars (g ...) ((gv . term) ...) 
       (subst let*-clause ...) gl) 
     (lambda (g ...)
       (exists (ex-id ...)
	 (lambda (subst)
	   (let* (let*-clause ...)
	     (let*-and sfail ((subst (unify gv term subst)) ...)
	       (@ gl subst)))))))))

; A macro-expand-time memv function for identifiers
;	id-memv?? FORM (ID ...) KT KF
; FORM is an arbitrary form or datum, ID is an identifier.
; The macro expands into KT if FORM is an identifier that occurs
; in the list of identifiers supplied by the second argument.
; Otherwise, id-memv?? expands to KF.
; All the identifiers in (ID ...) must be unique.
; Two identifiers match if both refer to the same binding occurrence, or
; (both are undefined and have the same spelling).

(define-syntax id-memv??
  (syntax-rules ()
    ((id-memv?? form (id ...) kt kf)
      (let-syntax
	((test
	   (syntax-rules (id ...)
	     ((test id _kt _kf) _kt) ...
	     ((test otherwise _kt _kf) _kf))))
	(test form kt kf)))))

; Test cases
; (id-memv?? x (a b c) #t #f)
; (id-memv?? a (a b c) 'OK #f)
; (id-memv?? () (a b c) #t #f)
; (id-memv?? (x ...) (a b c) #t #f)
; (id-memv?? "abc" (a b c) #t #f)
; (id-memv?? x () #t #f)
; (let ((x 1))
;   (id-memv?? x (a b x) 'OK #f))
; (let ((x 1))
;   (id-memv?? x (a x b) 'OK #f))
; (let ((x 1))
;   (id-memv?? x (x a b) 'OK #f))


; relation-head-let (head-term ...) gl 
; A simpler, and more efficient kind of relation. The simplicity comes
; from a simpler pattern at the head of the relation. The pattern must
; be linear and shallow with respect to introduced variables.  The gl
; is optional (although omitting it doesn't make much sense in
; practice) There are two kinds of head-terms.  One kind is an
; identifier. This identifier is taken to be a logical identifier, to
; be unified with the corresponding actual argument.  Each logical
; identifier must occur exactly once.  Another kind of a head-terms is
; anything else. That anything else may be a constant, a scheme
; variable, or a complex term that may even include logical variables
; such as _ -- but not logical variables defined in the same head-let
; pattern.  To make the task of distinguishing logical identifiers
; from anything else easier, we require that anything else of a sort
; of a manifest constant be explicitly quoted or quasiquoted. It would
; be OK to add `, to each 'anything else' term.
;
; Examples:
; (relation-head-let (x y z) (foo x y z))
; Here x y and z are logical variables.
; (relation-head-let (x y '7) (foo x y))
; Here we used a manifest constant that must be quoted
; (relation-head-let (x y `(1 2 . ,_)) (foo x y))
; We used a quasi-quoted constant with an anonymous variable.
; (let ((z `(1 2 . ,_))) (relation-head-let (x y `,z) (foo x y))
; The same as above, but using a lexical Scheme variable.
; The binding procedure is justified by Proposition 9 of
; the Properties of Substitutions.
;
; 'head-let' is an example of "compile-time" simplifications. 
; For example, we distinguish constants in the term head at
; "compile time" and so we re-arrange the argument-passing
; unifications to handle the constants first.
; The test for the anonymous variable (eq? gvv0 _) below
; is an example of a global simplification with a run-time
; test. A compiler could have inferred the result of the test -- but only
; upon the global analysis of all the clauses.
; Replacing a logical variable with an ordinary variable, which does 
; not have to be pruned, is equivalent to the use of temporary and
; unsafe variables in WAM.

(define-syntax relation-head-let
  (syntax-rules ()
    ((_ (head-term ...) . gls)
     (relation-head-let "g" () (head-term ...) (head-term ...) . gls))
    ; generate names of formal parameters
    ((_ "g" (genvar ...) ((head-term . tail-term) . ht-rest)
       head-terms . gls)
     (relation-head-let "g" (genvar ... g) ht-rest head-terms . gls))
    ((_ "g" (genvar ...) (head-term . ht-rest) head-terms . gls)
     (relation-head-let "g" (genvar ... head-term) ht-rest head-terms . gls))
    ((_ "g" genvars  () head-terms . gls)
     (relation-head-let "d" () () genvars head-terms genvars . gls))
    ; partition head-terms into vars and others
    ((_ "d" vars others (gv . gv-rest) ((hth . htt) . ht-rest) gvs . gls)
     (relation-head-let "d" vars ((gv (hth . htt)) . others)
       gv-rest ht-rest gvs . gls))
    ((_ "d" vars others (gv . gv-rest) (htv . ht-rest) gvs . gls)
     (relation-head-let "d" (htv . vars) others
       gv-rest ht-rest gvs . gls))
    ((_ "d" vars others () () gvs . gls)
     (relation-head-let "f" vars others gvs . gls))
 
    ; final generation
    ((_ "f" vars ((gv term) ...) gvs) ; no body
     (lambda gvs                                     ; don't bother bind vars
       (lambda@ (subst)
	 (let*-and sfail ((subst (unify gv term subst)) ...)
	   (@ succeed subst)))))

    ((_ "f" (var0 ...) ((gvo term) ...) gvs gl)
     (lambda gvs
       (lambda@ (subst)			; first unify the constants
	 (let*-and sfail ((subst (unify gvo term subst)) ...)
           (let ((var0 (if (eq? var0 _) (logical-variable '?) var0)) ...)
             (@ gl subst))))))))

; (define-syntax relation/cut
;   (syntax-rules (to-show)
;     ((_ cut-id (ex-id ...) (to-show x ...) gl ...)
;      (relation/cut cut-id (ex-id ...) () (x ...) (x ...) gl ...))
;     ((_ cut-id ex-ids (var ...) (x0 x1 ...) xs gl ...)
;      (relation/cut cut-id ex-ids (var ... g) (x1 ...) xs gl ...))
;     ((_ cut-id (ex-id ...) (g ...) () (x ...) gl ...)
;      (lambda (g ...)
;        (exists (ex-id ...)
;          (all! (== g x) ...
;            (lambda@ (sk fk subst cutk)
;              (let ((cut-id (!! cutk)))
;                (@ (all gl ...) sk fk subst cutk)))))))))

(define-syntax fact
  (syntax-rules ()
    ((_ (ex-id ...) term ...)
     (relation (ex-id ...) (to-show term ...) succeed))))

; Lifting from goals to relations
; (define-rel-lifted-comb rel-syntax gl-proc-or-syntax)
; Given (gl-proc-or-syntax gl ...)
; define 
; (rel-syntax (id ...) rel-exp ...)
; We should make rel-syntax behave as a CBV function, that is,
; evaluate rel-exp early.
; Otherwise, things like
; (define father (extend-relation father ...))
; loop.

; (define-syntax extend-relation
;   (syntax-rules ()
;     ((_ (id ...) rel-exp ...)
;      (extend-relation-aux (id ...) () rel-exp ...))))

; (define-syntax extend-relation-aux
;   (syntax-rules ()
;     ((_ (id ...) ((g rel-exp) ...))
;      (let ((g rel-exp) ...)
;        (lambda (id ...)
;          (any (g id ...) ...))))
;     ((_ (id ...) (let-pair ...) rel-exp0 rel-exp1 ...)
;      (extend-relation-aux (id ...)
;        (let-pair ... (g rel-exp0)) rel-exp1 ...))))

(define-syntax define-rel-lifted-comb
  (syntax-rules ()
    ((_ rel-syntax-name gl-proc-or-syntax)
     (define-syntax rel-syntax-name
       (syntax-rules ()
         ((_ ids . rel-exps)
          (lift-gl-to-rel-aux gl-proc-or-syntax ids () . rel-exps)))))))

(define-syntax lift-gl-to-rel-aux
  (syntax-rules ()
    ((_ gl-handler ids ((g rel-var) ...))
     (let ((g rel-var) ...)
       (lambda ids
         (gl-handler (g . ids) ...))))
    ((_ gl-handler ids (let-pair ...) rel-exp0 rel-exp1 ...)
     (lift-gl-to-rel-aux gl-handler ids 
       (let-pair ... (g rel-exp0)) rel-exp1 ...))))

(define-rel-lifted-comb extend-relation any)

; The following  goal-to-relations 
; transformers are roughly equivalent. I don't know which is better.
; see examples below.

; (lift-to-relations ids (gl-comb rel rel ...))
(define-syntax lift-to-relations
  (syntax-rules ()
    ((_ ids (gl-comb rel ...))
     (lift-gl-to-rel-aux gl-comb ids () rel ...))))

; (let-gls ids ((name rel) ...) body)
; NB: some macro systems do not like if 'ids' below is replaced by (id ...)
(define-syntax let-gls
  (syntax-rules ()
    ((_ ids ((gl-name rel-exp) ...) body)
     (lambda ids
       (let ((gl-name (rel-exp . ids)) ...)
         body)))))

; Unify lifted to be a binary relation
(define-syntax ==
  (syntax-rules (_)
    ((_ _ u) (lambda@ (subst sk) (@ sk subst)))
    ((_ t _) (lambda@ (subst sk) (@ sk subst)))
    ((_ t u)
     (lambda@ (subst)
       (let*-and sfail ((subst (unify t u subst)))
         (succeed subst))))))


;	query (redo-k subst id ...) A SE ... -> result or '()
; The macro 'query' runs the goal A in the empty
; initial substitution, and reifies the resulting
; answer: the substitution and the redo-continuation bound
; to fresh variables with the names supplied by the user.
; The substitution and the redo continuation can then be used
; by Scheme expressions SE ...
; Before running the goal, the macro creates logical variables
; id ... for use in A and SE ...
; If the goal fails, '() is returned and SE ... are not evaluated.
; Note the similarity with shift/reset-based programming
; where the immediate return signifies "failure" and the invocation
; of the continuation a "success"
; Returning '() on failure makes it easy to create the list of answers

(define-syntax query
  (syntax-rules ()
    ((_ (redo-k subst id ...) A SE ...)
      (let-lv (id ...)
	(@ A empty-subst
	  (lambda@ (subst redo-k) SE ...)
	  (lambda () '()))))))

(define stream-prefix
  (lambda (n strm)
    (if (null? strm) '()
      (cons (car strm)
        (if (zero? n) '()
          (stream-prefix (- n 1) ((cdr strm))))))))

(define-syntax solve
  (syntax-rules ()
    ((_ n (var0 ...) gl)
      (if (<= n 0) '()
	(stream-prefix (- n 1)
	  (query (redo-k subst var0 ...)
	    gl
	    (cons (reify-subst (list var0 ...) subst) redo-k)))))))


(define-syntax solution
  (syntax-rules ()
    ((_ (var0 ...) x)
     (let ((ls (solve 1 (var0 ...) x)))
       (if (null? ls) #f (car ls))))))


(define-syntax project
  (syntax-rules ()
    ((_ (var ...) gl)
     (lambda@ (subst)
       (let ((var (nonvar! (subst-in var subst))) ...)
	 (@ gl subst))))))

(define-syntax project/no-check
  (syntax-rules ()
    ((_ (var ...) gl)
     (lambda@ (subst)
       (let ((var (subst-in var subst)) ...)
	 (@ gl subst))))))

(define-syntax predicate
  (syntax-rules ()
    ((_ scheme-expression)
     (lambda@ (subst)
       (if scheme-expression (succeed subst) (fail subst))))))

(define nonvar!
  (lambda (t)
    (if (var? t)
      (errorf 'nonvar! "Logic variable ~s found after substituting."
	(reify t))
      t)))

; TRACE-VARS TITLE (VAR ...)
; Is a deterministic goal that prints the current values of VARS
; TITLE is any displayable thing.

; (define-syntax trace-vars
;   (syntax-rules ()
;     ((trace-vars title (var0 ...))
;      (promise-one-answer
;        (predicate/no-check (var0 ...)
;          (begin (display title) (display " ")
;                 (display '(var0 ...)) (display " ") (display (list var0 ...))
;                 (newline)))))))

(define-syntax trace-vars
  (syntax-rules ()
    ((_ title (var0 ...))
     (promise-one-answer
       (project/no-check (var0 ...)
         (predicate
	   (for-each 
	     (lambda (name val)
	       (cout title " " name ": " val nl))
             '(var0 ...) (reify `(,var0 ...)))
	   ))))))

;equality predicate: X == Y in Prolog
;if X is a var, then X == Y holds only if Y
;is the same var
(define *equal?
  (lambda (x y)
    (cond
      ((and (var? x) (var? y)) (eq? x y))
      ((var? x) #f)                     ; y is not a var
      ((var? y) #f)                     ; x is not a var
      (else (equal? x y)))))

; extend-relation-with-recur-limit LIMIT VARS RELS -> REL
; This is a variation of 'extend-relation' that makes sure
; that the extended relation is not recursively entered more
; than LIMIT times. The form extend-relation-with-recur-limit
; can be used to cut a left-recursive relation, and to implement
; an iterative deepening strategy.
; extend-relation-with-recur-limit must be a special form
; because we need to define the depth-counter-var
; outside of relations' lambda (so we count the recursive invocations
; for all arguments).
(define-syntax extend-relation-with-recur-limit
  (syntax-rules ()
    ((_ limit ids rel ...)
      (let ((depth-counter-var (logical-variable '*depth-counter*)))
	(lambda ids
	  (let ((gl (any (rel . ids) ...)))
	    (lambda@ (subst)
	      (cond
		((assq depth-counter-var subst)
		  => (lambda (cmt)
		       (let ((counter (commitment->term cmt)))
			 (if (>= counter limit)
			   sfail
			   (let ((s (extend-subst depth-counter-var
				      (+ counter 1) subst)))
			     (@ gl s))))))
		(else
		  (let ((s (extend-subst depth-counter-var 1 subst)))
		    (@ gl s)))))))))
    ))

; ?- help(call_with_depth_limit/3).
; call_with_depth_limit(+Goal, +Limit, -Result)
;     If  Goal can be proven  without recursion deeper than Limit  levels,
;     call_with_depth_limit/3 succeeds,  binding  Result  to  the  deepest
;     recursion  level  used  during the  proof.    Otherwise,  Result  is
;     unified  with depth_limit_exceeded  if the limit was exceeded  during
;     the  proof,  or the  entire predicate  fails if  Goal fails  without
;     exceeding Limit.

;     The  depth-limit is  guarded by the  internal machinery.   This  may
;     differ  from the depth computed based  on a theoretical model.   For
;     example,  true/0  is  translated  into an  inlined  virtual  machine
;     instruction.   Also, repeat/0 is not implemented as below, but  as a
;     non-deterministic foreign predicate.

;     repeat.
;     repeat :-
;             repeat.

;     As  a  result, call_with_depth_limit/3 may  still loop  inifitly  on
;     programs  that should  theoretically finish  in finite time.    This
;     problem  can be cured by  using Prolog equivalents to such  built-in
;     predicates.

;     This   predicate  may  be   used  for  theorem-provers  to   realise
;     techniques  like iterrative  deepening.   It  was implemented  after
;     discussion with Steve Moyle smoyle@ermine.ox.ac.uk.

;------------------------------------------------------------------------
;;;;; Starts the real work of the system.

(let* ((father  
	(relation ()
	  (to-show 'jon 'sam)))
      (child-of-male
	(relation (child dad)
	  (to-show child dad)
	  (father dad child)))
       (child-of-male1
	 (relation (child dad)
	   (to-show child dad)
	   (child-of-male dad child)))
       )
  (test-check 'test-father0
    (let ((result
	    (@ (father 'jon 'sam) empty-subst
	      initial-sk initial-fk)))
      (and
	(equal? (car result) '())
	(equal? ((cdr result)) '())))
    #t)

  (test-check 'test-child-of-male-0
    (reify-subst '()
      (car (@ (child-of-male 'sam 'jon) empty-subst
	     initial-sk initial-fk)))
  ;`(,(commitment 'child.0 'sam) ,(commitment 'dad.0 'jon)))
  '())  ; variables shouldn't leak


  ; The mark should be found here...
  (test-check 'test-child-of-male-1
  (reify-subst '()
    (car (@ (child-of-male 'sam 'jon) empty-subst
	    initial-sk initial-fk)))
  ;`(,(commitment 'child.0 'sam) ,(commitment 'dad.0 'jon)))
  '())
)

(let* ((father  
	(relation ()
	  (to-show 'jon 'sam)))
       (rob/sal
	 (relation ()
	   (to-show 'rob 'sal)))
       (new-father
	 (extend-relation (a1 a2) father rob/sal))
	(rob/pat
	  (relation ()
	    (to-show 'rob 'pat)))
	(newer-father
	  (extend-relation (a1 a2) new-father rob/pat))

	)
  (test-check 'test-father-1
    (let ((result
	    (@ (new-father 'rob 'sal) empty-subst
	      initial-sk initial-fk)))
      (and
	(equal? (car result) '())
	(equal? ((cdr result)) '())))
    #t)

  (test-check 'test-father-2
    (query (redo-k subst x)
      (new-father 'rob x)
      (list (equal? (car subst) (commitment x 'sal)) (redo-k)))
    '(#t ()))

  (test-check 'test-father-3
    (query (_ subst x)
      (new-father 'rob x)
      (reify-subst (list x) subst))
    '((x.0 sal)))

  (test-check 'test-father-4
    (query (_ subst x y)
      (new-father x y)
      (reify-subst (list x y) subst))
    '((x.0 jon) (y.0 sam)))

  (test-check 'test-father-5
    (query (redok subst x)
      (newer-father 'rob x)
      (pretty-print subst)
      (cons
	(reify-subst (list x) subst)
	(redok)))
    '(((x.0 sal)) ((x.0 pat))))

)

(let* ((father  
	 (extend-relation (a1 a2)
	   (relation () (to-show 'jon 'sam))
	   (relation () (to-show 'rob 'sal))
	   (relation () (to-show 'rob 'pat))
	   (relation () (to-show 'sam 'rob)))
	 ))

  (test-check 'test-father-6/solve
    (and
      (equal?
	(solve 5 (x) (father 'rob x))
	'(((x.0 sal)) ((x.0 pat))))
      (equal?
	(solve 6 (x y) (father x y))
	'(((x.0 jon) (y.0 sam))
	   ((x.0 rob) (y.0 sal))
	   ((x.0 rob) (y.0 pat))
	   ((x.0 sam) (y.0 rob)))))
  #t)

  (test-check 'test-father-7/solution
    (solution (x) (father 'rob x))
    '((x.0 sal)))
)



; (define-syntax intersect-relation
;   (syntax-rules ()
;     ((_ (id ...) rel-exp) rel-exp)
;     ((_ (id ...) rel-exp0 rel-exp1 rel-exp2 ...)
;      (binary-intersect-relation (id ...) rel-exp0
;        (intersect-relation (id ...) rel-exp1 rel-exp2 ...)))))

(define-rel-lifted-comb intersect-relation all)

(let*
  ((parents-of-scouts
     (extend-relation (a1 a2)
       (fact () 'sam 'rob)
       (fact () 'roz 'sue)
       (fact () 'rob 'sal)))
    (parents-of-athletes
      (extend-relation (a1 a2)
	(fact () 'sam 'roz)
	(fact () 'roz 'sue)
	(fact () 'rob 'sal)))

    (busy-parents
      (intersect-relation (a1 a2) parents-of-scouts parents-of-athletes))

    (conscientious-parents
      (extend-relation (a1 a2) parents-of-scouts parents-of-athletes))
    )

  (test-check 'test-conscientious-parents
    (solve 7 (x y) (conscientious-parents x y))
    '(((x.0 sam) (y.0 rob))
       ((x.0 roz) (y.0 sue))
       ((x.0 rob) (y.0 sal))
       ((x.0 sam) (y.0 roz))
       ((x.0 roz) (y.0 sue))
       ((x.0 rob) (y.0 sal))))
)

(let* ((father  
	 (extend-relation (a1 a2)
	   (relation () (to-show 'jon 'sam))
	   (relation () (to-show 'rob 'sal))
	   (relation () (to-show 'rob 'pat))
	   (relation () (to-show 'sam 'rob)))
	 ))

  (let
    ((grandpa-sam
       (relation (grandchild)
	 (to-show grandchild)
	 (exists (parent)
	   (all (father 'sam parent)
	        (father parent grandchild))))))
    (test-check 'test-grandpa-sam-1
      (solve 6 (y) (grandpa-sam y))
      '(((y.0 sal)) ((y.0 pat))))
   )

  (let
    ((grandpa-sam
       (relation ((once grandchild))
	 (to-show grandchild)
	 (exists (parent)
	   (all (father 'sam parent)
	        (father parent grandchild))))))
    (test-check 'test-grandpa-sam-1
      (solve 6 (y) (grandpa-sam y))
      '(((y.0 sal)) ((y.0 pat))))
    )

  (let ((child
	  (relation ((once child) (once dad))
	    (to-show child dad)
	    (father dad child))))
    (test-check 'test-child-1
      (solve 10 (x y) (child x y))
      '(((x.0 sam) (y.0 jon))
	 ((x.0 sal) (y.0 rob))
	 ((x.0 pat) (y.0 rob))
	 ((x.0 rob) (y.0 sam))))
    )

  (let ((grandpa
	  (relation ((once grandad) (once grandchild))
	    (to-show grandad grandchild)
	    (exists (parent)
	      (all
		(father grandad parent)
		(father parent grandchild))))))
    (test-check 'test-grandpa-1
      (solve 4 (x) (grandpa 'sam x))
      '(((x.0 sal)) ((x.0 pat)))))

  (let ((grandpa-maker
	  (lambda (guide* grandad*)
	    (relation (grandchild)
	      (to-show grandchild)
	      (exists (parent)
		(all
		  (guide* grandad* parent)
		  (guide* parent grandchild)))))))
    (test-check 'test-grandpa-maker-2
      (solve 4 (x) ((grandpa-maker father 'sam) x))
      '(((x.0 sal)) ((x.0 pat)))))
  
)

(let*
  ((father
     (extend-relation (a1 a2)
       (fact () 'jon 'sam)
       (extend-relation (a1 a2)
	 (fact () 'sam 'rob)
	 (extend-relation (a1 a2)
	   (fact () 'sam 'roz)
	   (extend-relation (a1 a2)
	     (fact () 'rob 'sal)
	     (fact () 'rob 'pat))))))
    (mother
      (extend-relation (a1 a2)
	(fact () 'roz 'sue)
	(fact () 'roz 'sid)))
    )

  (let*
    ((grandpa/father
       (relation (grandad grandchild)
	 (to-show grandad grandchild)
	 (exists (parent)
	   (all
	     (father grandad parent)
	     (father parent grandchild)))))
     (grandpa/mother
       (relation (grandad grandchild)
	 (to-show grandad grandchild)
	 (exists (parent)
	   (all
	     (father grandad parent)
	     (mother parent grandchild)))))
     (grandpa
       (extend-relation (a1 a2) grandpa/father grandpa/mother)))

    (test-check 'test-grandpa-5
      (solve 10 (y) (grandpa 'sam y))
      '(((y.0 sal)) ((y.0 pat)) ((y.0 sue)) ((y.0 sid))))
    )

  ; A relation is just a function
  (let
    ((grandpa-sam
       (let ((r (relation (child)
		  (to-show child)
		  (exists (parent)
		    (all
		      (father 'sam parent)
		      (father parent child))))))
	 (relation (child)
	   (to-show child)
	   (r child)))))

    (test-check 'test-grandpa-55
      (solve 6 (y) (grandpa-sam y))
      '(((y.0 sal)) ((y.0 pat))))
    )

; The solution that used cuts
; (define grandpa/father
;   (relation/cut cut (grandad grandchild)
;     (to-show grandad grandchild)
;     (exists (parent)
;       (all
;         (father grandad parent)
;         (father parent grandchild)
;         cut))))
;
; (define grandpa/mother
;   (relation (grandad grandchild)
;     (to-show grandad grandchild)
;     (exists (parent)
;       (all
;         (father grandad parent)
;         (mother parent grandchild)))))


; Now we don't need it
  (let*
    ((grandpa/father
       (relation (grandad grandchild)
	 (to-show grandad grandchild)
	 (exists (parent)
	   (all!
	     (father grandad parent)
	     (father parent grandchild)))))

      (grandpa/mother
	(relation (grandad grandchild)
	  (to-show grandad grandchild)
	  (exists (parent)
	    (all
	      (father grandad parent)
	      (mother parent grandchild)))))

      (grandpa
	(lift-to-relations (a1 a2)
	  (all!
	    (extend-relation (a1 a2) grandpa/father grandpa/mother))))
      )
    (test-check 'test-grandpa-8
      (solve 10 (x y) (grandpa x y))
      '(((x.0 jon) (y.0 rob))))
    )
  
; The solution that used to require cuts
; (define grandpa/father
;   (relation/cut cut (grandad grandchild)
;     (to-show grandad grandchild)
;     (exists (parent)
;       (all cut (father grandad parent) (father parent grandchild)))))

  (let
    ((grandpa/father
       (relation (grandad grandchild)
	 (to-show grandad grandchild)
	 (exists (parent)
	   (all
	     (father grandad parent) (father parent grandchild)))))

      (grandpa/mother
	(relation (grandad grandchild)
	  (to-show grandad grandchild)
	  (exists (parent)
	    (all
	      (father grandad parent) (mother parent grandchild)))))
      )

; Properly, this requires soft cuts, aka *->, or Mercury's
; if-then-else. But we emulate it...
    (let
      ((grandpa
	 (let-gls (a1 a2) ((grandpa/father grandpa/father)
			   (grandpa/mother grandpa/mother))
	   (if-only (succeeds grandpa/father) grandpa/father grandpa/mother)))
	)
      (test-check 'test-grandpa-10
	(solve 10 (x y) (grandpa x y))
	'(((x.0 jon) (y.0 rob))
	   ((x.0 jon) (y.0 roz))
	   ((x.0 sam) (y.0 sal))
	   ((x.0 sam) (y.0 pat))))
      (test-check 'test-grandpa-10-1
	(solve 10 (x) (grandpa x 'sue))
	'(((x.0 sam))))
      )

; The same as above, with if-all! -- just to test the latter.
    (let
      ((grandpa
	 (let-gls (a1 a2) ((grandpa/father grandpa/father)
			    (grandpa/mother grandpa/mother))
	   (if-only (all! (succeeds grandpa/father) (succeeds grandpa/father))
	     grandpa/father grandpa/mother))))

      (test-check 'test-grandpa-10
	(solve 10 (x y) (grandpa x y))
	'(((x.0 jon) (y.0 rob))
	   ((x.0 jon) (y.0 roz))
	   ((x.0 sam) (y.0 sal))
	   ((x.0 sam) (y.0 pat))))

      (test-check 'test-grandpa-10-1
	(solve 10 (x) (grandpa x 'sue))
	'(((x.0 sam))))
      )


; Now do it with soft-cuts
    (let
      ((grandpa
	 (let-gls (a1 a2) ((grandpa/father grandpa/father)
			    (grandpa/mother grandpa/mother))
	   (if-some grandpa/father succeed grandpa/mother)))
	)
      (test-check 'test-grandpa-10-soft-cut
	(solve 10 (x y) (grandpa x y))
	'(((x.0 jon) (y.0 rob))
	   ((x.0 jon) (y.0 roz))
	   ((x.0 sam) (y.0 sal))
	   ((x.0 sam) (y.0 pat))))
      )

    (let*
      ((a-grandma
	 (relation (grandad grandchild)
	   (to-show grandad grandchild)
	   (exists (parent)
	     (all! (mother grandad parent)))))
	(no-grandma-grandpa
	  (let-gls (a1 a2) ((a-grandma a-grandma)
			     (grandpa (lift-to-relations (a1 a2)
					(all!
					  (extend-relation (a1 a2) 
					    grandpa/father grandpa/mother)))))
	    (if-only a-grandma fail grandpa)))
	)
      (test-check 'test-no-grandma-grandpa-1
	(solve 10 (x) (no-grandma-grandpa 'roz x))
	'()))
))

(let
  ((parents-of-scouts
     (extend-relation (a1 a2)
       (fact () 'sam 'rob)
       (fact () 'roz 'sue)
       (fact () 'rob 'sal)))
    (fathers-of-cubscouts
      (extend-relation (a1 a2)
	(fact () 'sam 'bob)
	(fact () 'tom 'adam)
	(fact () 'tad 'carl)))
    )

  (test-check 'test-partially-eval-sgl
   (let-lv (p1 p2)
    (let* ((parents-of-scouts-sgl
	     ((parents-of-scouts p1 p2) empty-subst))
           (cons@ (lambda@ (x y) (cons x y)))
           (split1 (@ 
                    partially-eval-sgl parents-of-scouts-sgl
                    cons@ (lambda () '())))
           (a1 (car split1))
           (split2 (@ partially-eval-sgl (cdr split1) cons@
                     (lambda () '())))
           (a2 (car split2))
           (split3 (@ partially-eval-sgl (cdr split2) cons@
                     (lambda () '())))
           (a3 (car split3)))
      (map (lambda (subst)
             (reify-subst (list p1 p2) subst))
	(list a1 a2 a3))))
  '(((p1.0 sam) (p2.0 rob)) ((p1.0 roz) (p2.0 sue)) ((p1.0 rob) (p2.0 sal))))
)


(test-check 'test-pred1
  (let ((test1
	  (lambda (x)
	    (any (predicate (< 4 5))
	      (== x (< 6 7))))))
    (solution (x) (test1 x)))
  '((x.0 _.0)))

(test-check 'test-pred2
  (let ((test2
	  (lambda (x)
	    (any (predicate (< 5 4))
	      (== x (< 6 7))))))
    (solution (x) (test2 x)))
  '((x.0 #t)))

(test-check 'test-pred3
  (let ((test3
	  (lambda (x y)
	    (any
	      (== x (< 5 4))
	      (== y (< 6 7))))))
    (solution (x y) (test3 x y)))
  `((x.0 #f) (y.0 _.0)))

(test-check 'test-Seres-Spivey
  (let ((father
	  (lambda (dad child)
	    (any
	      (all (== dad 'jon) (== child 'sam))
	      (all (== dad 'sam) (== child 'rob))
	      (all (== dad 'sam) (== child 'roz))
	      (all (== dad 'rob) (== child 'sal))
	      (all (== dad 'rob) (== child 'pat))
	      (all (== dad 'jon) (== child 'hal))
	      (all (== dad 'hal) (== child 'ted))
	      (all (== dad 'sam) (== child 'jay))))))
    (letrec
        ((ancestor
           (lambda (old young)
             (any
               (father old young)
               (exists (not-so-old)
                 (all
                   (father old not-so-old)
                   (ancestor not-so-old young)))))))
      (solve 20 (x) (ancestor 'jon x))))
  '(((x.0 sam))
    ((x.0 hal))
    ((x.0 rob))
    ((x.0 roz))
    ((x.0 jay))
    ((x.0 sal))
    ((x.0 pat))
    ((x.0 ted))))

(define towers-of-hanoi
  (letrec
      ((move
         (extend-relation (a1 a2 a3 a4)
           (fact () 0 _ _ _)
           (relation (n a b c)
             (to-show n a b c)
             (project (n)
               (if-only (predicate (positive? n))
                 (let ((m (- n 1)))
                   (all 
                     (move m a c b)
                     (project (a b)
                       (begin
                         (cout "Move a disk from " a " to " b nl)
                         (move m c b a)))))))))))
    (relation (n)
      (to-show n)
      (move n 'left 'middle 'right))))

(cout "test-towers-of-hanoi with 3 disks: "
  (solution () (towers-of-hanoi 3))
  nl nl
  )


(test-check 'test-fun-resubst
  (reify
    (let ((j (relation (x w z)
	       (to-show z)
	       (let ((x 4)
                     (w 3))
                 (== z (cons x w))))))
      (solve 4 (q) (j q))))
  '(((q.0 (4 . 3)))))

(define towers-of-hanoi-path
  (let ((steps '()))
    (let ((push-step (lambda (x y) (set! steps (cons `(,x ,y) steps)))))
      (letrec
          ((move
             (extend-relation (a1 a2 a3 a4)
               (fact () 0 _ _ _)
               (relation (n a b c)
                 (to-show n a b c)
                 (project (n)
                   (if-only (predicate (positive? n))
                     (let ((m (- n 1)))
                       (all
                         (move m a c b)
                         (project (a b)
                           (begin
                             (push-step a b)
                             (move m c b a)))))))))))
        (relation (n path)
          (to-show n path)
          (begin
            (set! steps '())
            (any
              (fails (move n 'l 'm 'r))
              (== path (reverse steps)))))))))

(test-check 'test-towers-of-hanoi-path
  (solution (path) (towers-of-hanoi-path 3 path))
  '((path.0 ((l m) (l r) (m r) (l m) (r l) (r m) (l m)))))

;------------------------------------------------------------------------

          
(test-check 'unification-of-free-vars-1
  (solve 1 (x)
    (let-lv (y)
      (all!! (== x y) (== y 5))))
  '(((x.0 5))))

(test-check 'unification-of-free-vars-2
  (solve 1 (x)
    (let-lv (y)
      (all!! (== y 5) (== x y))))
  '(((x.0 5))))

(test-check 'unification-of-free-vars-3
  (solve 1 (x)
    (let-lv (y)
      (all!! (== y x) (== y 5))))
  '(((x.0 5))))

(test-check 'unification-of-free-vars-3
  (solve 1 (x)
    (let-lv (y)
      (all!! (== x y) (== y 5) (== x y))))
  '(((x.0 5))))

(test-check 'unification-of-free-vars-4
  (solve 1 (x)
    (exists (y)
      (all! (== y x) (== y 5) (== x y))))
  '(((x.0 5))))


(letrec
  ((concat
     (lambda (xs ys)
       (cond
	 ((null? xs) ys)
	 (else (cons (car xs) (concat (cdr xs) ys)))))))

  (test-check 'test-concat-as-function
    (concat '(a b c) '(u v))
    '(a b c u v))

  (test-check 'test-fun-concat
    (solve 1 (q)
      (== q (concat '(a b c) '(u v))))
    '(((q.0 (a b c u v)))))
)

; Now the same with the relation
(letrec
  ((concat
     (extend-relation (a1 a2 a3)
       (fact (xs) '() xs xs)
       (relation (x xs (once ys) zs)
	 (to-show `(,x . ,xs) ys `(,x . ,zs))
	 (concat xs ys zs)))))
 (test-check 'test-concat
  (time
    (and
      (equal?
        (solve 6 (q) (concat '(a b c) '(u v) q))
        '(((q.0 (a b c u v)))))
      (equal?
        (solve 6 (q) (concat '(a b c) q '(a b c u v)))
        '(((q.0 (u v)))))
      (equal?
        (solve 6 (q) (concat q '(u v) '(a b c u v)))
        '(((q.0 (a b c)))))
      (equal?
        (solve 6 (q r) (concat q r '(a b c u v)))
        '(((q.0 ()) (r.0 (a b c u v)))
          ((q.0 (a)) (r.0 (b c u v)))
          ((q.0 (a b)) (r.0 (c u v)))
          ((q.0 (a b c)) (r.0 (u v)))
          ((q.0 (a b c u)) (r.0 (v)))
          ((q.0 (a b c u v)) (r.0 ()))))
      (equal?
        (solve 6 (q r s) (concat q r s))
	'(((q.0 ()) (r.0 _.0) (s.0 _.0))
	  ((q.0 (_.0)) (r.0 _.1) (s.0 (_.0 . _.1)))
	  ((q.0 (_.0 _.1)) (r.0 _.2) (s.0 (_.0 _.1 . _.2)))
	  ((q.0 (_.0 _.1 _.2)) (r.0 _.3) (s.0 (_.0 _.1 _.2 . _.3)))
	  ((q.0 (_.0 _.1 _.2 _.3)) (r.0 _.4) (s.0 (_.0 _.1 _.2 _.3 . _.4)))
	  ((q.0 (_.0 _.1 _.2 _.3 _.4)) (r.0 _.5)
	   (s.0 (_.0 _.1 _.2 _.3 _.4 . _.5))))
	)
      '(equal?
        (solve 6 (q r) (concat q '(u v) `(a b c . ,r)))
        '(((q.0 (a b c)) (r.0 (u v)))
          ((q.0 (a b c _.0)) (r.0 (_.0 u v)))
          ((q.0 (a b c _.0 _.1)) (r.0 (_.0 _.1 u v)))
          ((q.0 (a b c _.0 _.1 _.2)) (r.0 (_.0 _.1 _.2 u v)))
          ((q.0 (a b c _.0 _.1 _.2 _.3)) (r.0 (_.0 _.1 _.2 _.3 u v)))
          ((q.0 (a b c _.0 _.1 _.2 _.3 _.4))
           (r.0 (_.0 _.1 _.2 _.3 _.4 u v)))))
      (equal?
        (solve 6 (q) (concat q '() q))
        '(((q.0 ()))
          ((q.0 (_.0)))
          ((q.0 (_.0 _.1)))
          ((q.0 (_.0 _.1 _.2)))
          ((q.0 (_.0 _.1 _.2 _.3)))
          ((q.0 (_.0 _.1 _.2 _.3 _.4)))))
      ))
  #t)
)

; Using the properties of the unifier to do the proper garbage
; collection of logical vars

; (test-check 'lv-elim-1
;   (reify
;     (let-lv (x z dummy)
;       (@ 
; 	(exists (y)
; 	  (== `(,x ,z ,y) `(5 9 ,x)))
; 	(lambda@ (fk subst) subst)
; 	initial-fk
; 	(unit-subst dummy 'dummy))))
;   '((y.0 . 5) (z.0 . 9) (x.0 . 5) (dummy.0 . dummy)))
;   ;'((z.0 . 9) (x.0 . 5) (dummy.0 . dummy)))

; (test-check 'lv-elim-2
;   (reify
;     (let-lv (x dummy)
;       (@ 
; 	(exists (y)
; 	  (== `(,x ,y) `((5 ,y) ,7)))
; 	(lambda@ (fk subst) subst)
; 	initial-fk
; 	(unit-subst dummy 'dummy))))
;   '((y.0 . 7) (x.0 5 y.0) (dummy.0 . dummy)))
;   ;'((a*.0 . 7) (x.0 5 a*.0) (dummy.0 . dummy)))

; ; verifying corollary 2 of proposition 10
; (test-check 'lv-elim-3
;   (reify
;     (let-lv (x v dummy)
;       (@ 
; 	(exists (y)
; 	  (== x `(a b c ,v d)))
; 	(lambda@ (fk subst) subst)
; 	initial-fk
; 	(unit-subst dummy 'dummy))))
;   '((x.0 a b c v.0 d) (dummy.0 . dummy)))
;   ;'((a*.0 . v.0) (x.0 a b c a*.0 d) (dummy.0 . dummy)))

; ; pruning several variables sequentially and in parallel
; (test-check 'lv-elim-4-1
;   (reify
;     (let-lv (x v b dummy)
;       (@ 
; 	(let-lv (y)
; 	  (== `(,b ,x ,y) `(,x ,y 1)))
; 	(lambda@ (fk subst) subst)
; 	initial-fk
; 	(unit-subst dummy 'dummy))))
;   '((y.0 . 1) (x.0 . y.0) (b.0 . x.0) (dummy.0 . dummy)))

; ; (test-check 'lv-elim-4-2
; ;   (concretize
; ;     (let-lv (v b dummy)
; ;       (@ 
; ; 	(exists (x)
; ; 	  (exists (y)
; ; 	    (== `(,b ,x ,y) `(,x ,y 1))))
; ; 	  (lambda@ (fk subst) subst)
; ; 	  initial-fk
; ; 	  (unit-subst dummy 'dummy))))
; ;     '((b.0 . 1) (dummy.0 . dummy)))

; ; (test-check 'lv-elim-4-3
; ;   (concretize
; ;     (let-lv (v b dummy)
; ;       (@ 
; ; 	(exists (y)
; ; 	  (exists (x)
; ; 	    (== `(,b ,x ,y) `(,x ,y 1))))
; ; 	  (lambda@ (fk subst) subst)
; ; 	  initial-fk
; ; 	  (unit-subst dummy 'dummy))))
; ;     '((b.0 . 1) (dummy.0 . dummy)))

; (test-check 'lv-elim-4-4
;   (reify
;     (let-lv (v b dummy)
;       (@ 
; 	(exists (x y)
; 	    (== `(,b ,x ,y) `(,x ,y 1)))
; 	  (lambda@ (fk subst) subst)
; 	  initial-fk
; 	  (unit-subst dummy 'dummy))))
;   '((y.0 . 1) (x.0 . y.0) (b.0 . x.0) (dummy.0 . dummy)))
;   ;'((b.0 . 1) (dummy.0 . dummy)))

; ; pruning several variables sequentially and in parallel
; ; for indirect (cyclic) dependency
; (test-check 'lv-elim-5-1
;   (reify
;     (let-lv (x v b dummy)
;       (@ 
; 	(let-lv (y)
; 	  (== `(,b ,y ,x) `(,x (1 ,x) ,y)))
; 	(lambda@ (fk subst) subst)
; 	initial-fk
; 	(unit-subst dummy 'dummy))))
;   '((x.0 1 x.0) (y.0 1 x.0) (b.0 . x.0) (dummy.0 . dummy)))
;   ;'((x.0 1 a*.0) (a*.0 . x.0) (y.0 1 a*.0) (b.0 . x.0) (dummy.0 . dummy)))

; ; (test-check 'lv-elim-5-2
; ;   (concretize
; ;     (let-lv (v b dummy)
; ;       (@ 
; ; 	(exists (x)
; ; 	  (exists (y)
; ; 	  (== `(,b ,y ,x) `(,x (1 ,x) ,y))))
; ; 	(lambda@ (fk subst) subst)
; ; 	initial-fk
; ; 	(unit-subst dummy 'dummy))))
; ;   '((a*.0 1 a*.0) (b.0 1 a*.0) (dummy.0 . dummy)))

; ; (test-check 'lv-elim-5-3
; ;   (concretize
; ;     (let-lv (v b dummy)
; ;       (@ 
; ; 	(exists (y)
; ; 	  (exists (x)
; ; 	  (== `(,b ,y ,x) `(,x (1 ,x) ,y))))
; ; 	(lambda@ (fk subst) subst)
; ; 	initial-fk
; ; 	(unit-subst dummy 'dummy))))
; ;   '((a*.0 1 a*.0) (b.0 1 a*.0) (dummy.0 . dummy)))

; (test-check 'lv-elim-5-4
;   (reify
;     (let-lv (v b dummy)
;       (@ 
; 	(exists (x y)
; 	  (== `(,b ,y ,x) `(,x (1 ,x) ,y)))
; 	(lambda@ (fk subst) subst)
; 	initial-fk
; 	(unit-subst dummy 'dummy))))
;   '((x.0 1 x.0) (y.0 1 x.0) (b.0 . x.0) (dummy.0 . dummy)))
;  ;'((a*.0 1 a*.0) (b.0 1 a*.0) (dummy.0 . dummy)))

; ; We should only be concerned about a direct dependency:
; ;  ((x . y) (y . (1 t)) (t . x) (a . x))
; ; pruning x and y in sequence or in parallel gives the same result:
; ;  ((t . (1 t)) (a . (1 t)))


; Extending relations in truly mathematical sense.
; First, why do we need this.
(let*
  ((fact1 (fact () 'x1 'y1))
   (fact2 (fact () 'x2 'y2))
   (fact3 (fact () 'x3 'y3))
   (fact4 (fact () 'x4 'y4))

   ; R1 and R2 are overlapping
   (R1 (extend-relation (a1 a2) fact1 fact2))
   (R2 (extend-relation (a1 a2) fact1 fact3))
  )
   ; Infinitary relation
   ; r(z,z).
   ; r(s(X),s(Y)) :- r(X,Y).
  (letrec
   ((Rinf
     (extend-relation (a1 a2)
       (fact () 'z 'z)
       (relation (x y t1 t2)
	 (to-show t1 t2)
	 (all
	   (== t1 `(s ,x))
	   (== t2 `(s ,y))
	   (Rinf x y)))))
  )

  (cout nl "R1:" nl)
  (pretty-print (solve 10 (x y) (R1 x y)))
  (cout nl "R2:" nl)
  (pretty-print (solve 10 (x y) (R2 x y)))
  (cout nl "R1+R2:" nl)
  (pretty-print 
    (solve 10 (x y)
      ((extend-relation (a1 a2) R1 R2) x y)))

  (cout nl "Rinf:" nl)
  (time (pretty-print (solve 5 (x y) (Rinf x y))))
  (cout nl "Rinf+R1: Rinf starves R1:" nl)
  (time
    (pretty-print 
      (solve 5 (x y)
	((extend-relation (a1 a2) Rinf R1) x y))))

; Solving the starvation problem: extend R1 and R2 so that they
; are interleaved
; ((sf-extend R1 R2) sk fk)
; (R1 sk fk)
; If R1 fails, we try the rest of R2
; If R1 succeeds, it executes (sk fk)
; with fk to re-prove R1. Thus fk is the "rest" of R1
; So we pass sk (lambda () (run-rest-of-r2 interleave-with-rest-of-r1))
; There is a fixpoint in the following algorithm!
; Or a second-level shift/reset!

  (test-check "Rinf+R1"
    (time 
      (solve 7 (x y)
	(any-interleave (Rinf x y) (R1 x y))))
    '(((x.0 z) (y.0 z))
       ((x.0 x1) (y.0 y1))
       ((x.0 (s z)) (y.0 (s z)))
       ((x.0 x2) (y.0 y2))
       ((x.0 (s (s z))) (y.0 (s (s z))))
       ((x.0 (s (s (s z)))) (y.0 (s (s (s z)))))
       ((x.0 (s (s (s (s z))))) (y.0 (s (s (s (s z)))))))
    )

  (test-check "R1+Rinf"
    (time 
      (solve 7 (x y)
	(any-interleave (R1 x y) (Rinf x y))))
    '(((x.0 x1) (y.0 y1))
       ((x.0 z) (y.0 z))
       ((x.0 x2) (y.0 y2))
       ((x.0 (s z)) (y.0 (s z)))
       ((x.0 (s (s z))) (y.0 (s (s z))))
       ((x.0 (s (s (s z)))) (y.0 (s (s (s z)))))
       ((x.0 (s (s (s (s z))))) (y.0 (s (s (s (s z)))))))
    )


  (test-check "R2+R1"
    (solve 7 (x y)
      (any-interleave (R2 x y) (R1 x y)))
    '(((x.0 x1) (y.0 y1))
       ((x.0 x1) (y.0 y1))
       ((x.0 x3) (y.0 y3))
       ((x.0 x2) (y.0 y2)))
    )

  (test-check "R1+fact3"
    (solve 7 (x y)
      (any-interleave (R1 x y) (fact3 x y)))
    '(((x.0 x1) (y.0 y1)) ((x.0 x3) (y.0 y3)) ((x.0 x2) (y.0 y2)))
    )

  (test-check "fact3+R1"
    (solve 7 (x y)
      (any-interleave (fact3 x y) (R1 x y)))
    '(((x.0 x3) (y.0 y3)) ((x.0 x1) (y.0 y1)) ((x.0 x2) (y.0 y2)))
    )

; testing all-interleave
  (test-check 'all-interleave-1
    (solve 100 (x y z)
      (all-interleave
	(any (== x 1) (== x 2))
	(any (== y 3) (== y 4))
	(any (== z 5) (== z 6) (== z 7))))
    '(((x.0 1) (y.0 3) (z.0 5))
       ((x.0 2) (y.0 3) (z.0 5))
       ((x.0 1) (y.0 4) (z.0 5))
       ((x.0 2) (y.0 4) (z.0 5))
       ((x.0 1) (y.0 3) (z.0 6))
       ((x.0 2) (y.0 3) (z.0 6))
       ((x.0 1) (y.0 4) (z.0 6))
       ((x.0 2) (y.0 4) (z.0 6))
       ((x.0 1) (y.0 3) (z.0 7))
       ((x.0 2) (y.0 3) (z.0 7))
       ((x.0 1) (y.0 4) (z.0 7))
       ((x.0 2) (y.0 4) (z.0 7)))
    )

  (test-check "R1 * Rinf: clearly starvation"
    (solve 5 (x y u v)
      (all (R1 x y) (Rinf u v)))
  ; indeed, only the first choice of R1 is apparent
    '(((x.0 x1) (y.0 y1) (u.0 z) (v.0 z))
       ((x.0 x1) (y.0 y1) (u.0 (s z)) (v.0 (s z)))
       ((x.0 x1) (y.0 y1) (u.0 (s (s z))) (v.0 (s (s z))))
       ((x.0 x1) (y.0 y1) (u.0 (s (s (s z)))) (v.0 (s (s (s z)))))
       ((x.0 x1) (y.0 y1) (u.0 (s (s (s (s z))))) (v.0 (s (s (s (s z)))))))
    )

  (test-check "R1 * Rinf: interleaving"
    (solve 5 (x y u v)
      (all-interleave (R1 x y) (Rinf u v)))
  ; both choices of R1 are apparent
    '(((x.0 x1) (y.0 y1) (u.0 z) (v.0 z))
       ((x.0 x2) (y.0 y2) (u.0 z) (v.0 z))
       ((x.0 x1) (y.0 y1) (u.0 (s z)) (v.0 (s z)))
       ((x.0 x2) (y.0 y2) (u.0 (s z)) (v.0 (s z)))
       ((x.0 x1) (y.0 y1) (u.0 (s (s z))) (v.0 (s (s z)))))
    )

  ;; Test for nonoverlapping.

  (cout nl "any-union" nl)
  (test-check "R1+R2"
    (solve 10 (x y)
      (any-union (R1 x y) (R2 x y)))
    '(((x.0 x1) (y.0 y1))
       ((x.0 x2) (y.0 y2))
       ((x.0 x3) (y.0 y3))))

  (test-check "R2+R1"
    (solve 10 (x y)
      (any-union (R2 x y) (R1 x y)))
    '(((x.0 x1) (y.0 y1))
       ((x.0 x3) (y.0 y3))
       ((x.0 x2) (y.0 y2))))
  
  (test-check "R1+R1"
    (solve 10 (x y)
      (any-union (R1 x y) (R1 x y)))
    '(((x.0 x1) (y.0 y1))
       ((x.0 x2) (y.0 y2))))
  
  (test-check "Rinf+R1"
    (solve 7 (x y)
      (any-union (Rinf x y) (R1 x y)))
    '(((x.0 z) (y.0 z))
     ((x.0 x1) (y.0 y1))
      ((x.0 (s z)) (y.0 (s z)))
      ((x.0 x2) (y.0 y2))
      ((x.0 (s (s z))) (y.0 (s (s z))))
      ((x.0 (s (s (s z)))) (y.0 (s (s (s z)))))
      ((x.0 (s (s (s (s z))))) (y.0 (s (s (s (s z))))))))

  (test-check "R1+RInf"
    (solve 7 (x y)
      (any-union (R1 x y) (Rinf x y)))
    '(((x.0 x1) (y.0 y1))
       ((x.0 z) (y.0 z))
       ((x.0 x2) (y.0 y2))
       ((x.0 (s z)) (y.0 (s z)))
       ((x.0 (s (s z))) (y.0 (s (s z))))
       ((x.0 (s (s (s z)))) (y.0 (s (s (s z)))))
       ((x.0 (s (s (s (s z))))) (y.0 (s (s (s (s z))))))))


; Infinitary relation Rinf2
; r(z,z).
; r(s(s(X)),s(s(Y))) :- r(X,Y).
; Rinf2 overlaps with Rinf in the infinite number of points
  (letrec
    ((Rinf2
       (extend-relation (a1 a2)
	 (fact () 'z 'z)
	 (relation (x y t1 t2)
	   (to-show t1 t2)
	   (all
	     (== t1 `(s (s ,x)))
	     (== t2 `(s (s ,y)))
	     (Rinf2 x y)))))
      )
    (test-check "Rinf2"
      (solve 5 (x y) (Rinf2 x y))
      '(((x.0 z) (y.0 z))
	 ((x.0 (s (s z))) (y.0 (s (s z))))
	 ((x.0 (s (s (s (s z))))) (y.0 (s (s (s (s z))))))
	 ((x.0 (s (s (s (s (s (s z)))))))
	   (y.0 (s (s (s (s (s (s z))))))))
	 ((x.0 (s (s (s (s (s (s (s (s z)))))))))
	   (y.0 (s (s (s (s (s (s (s (s z))))))))))))

    (test-check "Rinf+Rinf2"
      (solve 9 (x y)
	(any-union (Rinf x y) (Rinf2 x y)))
      '(((x.0 z) (y.0 z))
	 ((x.0 (s z)) (y.0 (s z)))
	 ((x.0 (s (s z))) (y.0 (s (s z))))
	 ((x.0 (s (s (s (s z))))) (y.0 (s (s (s (s z))))))
	 ((x.0 (s (s (s z)))) (y.0 (s (s (s z)))))
	 ((x.0 (s (s (s (s (s (s z)))))))
	   (y.0 (s (s (s (s (s (s z))))))))
	 ((x.0 (s (s (s (s (s (s (s (s z)))))))))
	   (y.0 (s (s (s (s (s (s (s (s z))))))))))
	 ((x.0 (s (s (s (s (s z)))))) (y.0 (s (s (s (s (s z)))))))
	 ((x.0 (s (s (s (s (s (s (s (s (s (s z)))))))))))
	   (y.0 (s (s (s (s (s (s (s (s (s (s z))))))))))))))
    
    (test-check "Rinf2+Rinf"
      (solve 9 (x y)
	(any-union (Rinf2 x y) (Rinf x y)))
      '(((x.0 z) (y.0 z))
	 ((x.0 (s z)) (y.0 (s z)))
	 ((x.0 (s (s z))) (y.0 (s (s z))))
	 ((x.0 (s (s (s z)))) (y.0 (s (s (s z)))))
	 ((x.0 (s (s (s (s z))))) (y.0 (s (s (s (s z))))))
	 ((x.0 (s (s (s (s (s z)))))) (y.0 (s (s (s (s (s z)))))))
	 ((x.0 (s (s (s (s (s (s z)))))))
	   (y.0 (s (s (s (s (s (s z))))))))
	 ((x.0 (s (s (s (s (s (s (s z))))))))
	   (y.0 (s (s (s (s (s (s (s z)))))))))
	 ((x.0 (s (s (s (s (s (s (s (s z)))))))))
	   (y.0 (s (s (s (s (s (s (s (s z))))))))))))
    )))


(cout nl "Append with limited depth" nl)
; In Prolog, we normally write:
; append([],L,L).
; append([X|L1],L2,[X|L3]) :- append(L1,L2,L3).
;
; If we switch the clauses, we get non-termination.
; In our system, it doesn't matter!

(letrec
  ((extend-clause-1
     (relation (l)
       (to-show '() l l)
       succeed))
   (extend-clause-2
     (relation (x l1 l2 l3)
       (to-show `(,x . ,l1) l2 `(,x . ,l3))
       (extend-rel l1 l2 l3)))
   (extend-rel
       (extend-relation-with-recur-limit 5 (a b c)
	 extend-clause-1
	 extend-clause-2))
    )

  ; Note (solve 100 ...)
  ; Here 100 is just a large number: we want to print all solutions
    (cout nl "Extend: clause1 first: " 
      (solve 100 (a b c) (extend-rel a b c))
      nl))

(letrec
  ((extend-clause-1
     (relation (l)
       (to-show '() l l)
       succeed))
   (extend-clause-2
     (relation (x l1 l2 l3)
       (to-show `(,x . ,l1) l2 `(,x . ,l3))
       (extend-rel l1 l2 l3)))
   (extend-rel
     (extend-relation-with-recur-limit 3 (a b c)
       extend-clause-2
       extend-clause-1)))

  (cout nl "Extend: clause2 first. In Prolog, it would diverge!: " 
    (solve 100 (a b c) (extend-rel a b c)) nl))


(letrec
  ((base-+-as-relation
     (fact (n) 'zero n n))
   (recursive-+-as-relation
     (relation (n1 n2 n3)
       (to-show `(succ ,n1) n2 `(succ ,n3))
       (+-as-relation n1 n2 n3)))
   ; Needed eta-expansion here: otherwise, SCM correctly reports
   ; an error (but Petite doesn't, alas)
   ; This is a peculiarity of extend-relation as a macro
   ; Potentially, we need the same approach as in minikanren
   (+-as-relation
     (extend-relation (a1 a2 a3)
       (lambda (a1 a2 a3) (base-+-as-relation a1 a2 a3))
       (lambda (a1 a2 a3) (recursive-+-as-relation a1 a2 a3))
       ))
    )

  (test-check "Addition"
    (solve 20 (x y)
      (+-as-relation x y '(succ (succ (succ (succ (succ zero)))))))
    '(((x.0 zero) (y.0 (succ (succ (succ (succ (succ zero)))))))
       ((x.0 (succ zero)) (y.0 (succ (succ (succ (succ zero))))))
       ((x.0 (succ (succ zero))) (y.0 (succ (succ (succ zero)))))
       ((x.0 (succ (succ (succ zero)))) (y.0 (succ (succ zero))))
       ((x.0 (succ (succ (succ (succ zero))))) (y.0 (succ zero)))
       ((x.0 (succ (succ (succ (succ (succ zero)))))) (y.0 zero))))

  (newline)
)


;(exit 0)


