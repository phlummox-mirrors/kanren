;(load "plshared.ss")

; $Id$

(define-syntax let-values
  (syntax-rules ()
    [(_ (x ...) vs body0 body1 ...)
     (call-with-values (lambda () vs) (lambda (x ...) body0 body1 ...))]))

(define-syntax let-lv
  (syntax-rules ()
    [(_ () body) body]
    [(_ () body0 body1 body2 ...) (begin body0 body1 body2 ...)]
    [(_ (id ...) body0 body1 ...)
     (let ([id (var 'id)] ...) body0 body1 ...)]))

(define-syntax lambda@
  (syntax-rules ()
    [(_ (formal) body0 body1 ...) (lambda (formal) body0 body1 ...)]
    [(_ (formal0 formal1 formal2 ...) body0 body1 ...)
     (lambda (formal0)
       (lambda@ (formal1 formal2 ...) body0 body1 ...))]))

(define-syntax @    
  (syntax-rules ()
    [(_ rator rand) (rator rand)]
    [(_ rator rand0 rand1 rand2 ...) (@ (rator rand0) rand1 rand2 ...)]))

; Regression testing framework
; test-check TITLE TESTED-EXPRESSION EXPECTED-RESULT 
; where TITLE is something printable (e.g., a symbol or a string)
; EXPECTED-RESULT and TESTED-EXPRESSION are both expressions.
; The expressions are evaluated and their results are compared
; by equal?
; If the results compare, we just print the TITLE.
; Otherwise, we print the TITLE, the TESTED-EXPRESSION, and
; the both results.
(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s~%" title)
       (let* ([expected expected-result]
              [produced tested-expression])
         (or (equal? expected produced)
             (error 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(test-check 'test-@-lambda@
  (@ (lambda@ (x y z) (+ x (+ y z))) 1 2 3)
  6)

'(test-check 'test-@-lambda@
  (@ (lambda@ (x y z) (+ x (+ y z))) 1 2 3)
  42)
   
(define-record var (id) ())
(define var make-var)

; A framework to remove introduced variables when they leave their scope.
; To make removing variables easier, we consider the list
; of subst as a "stack". Before we add a new variable, we put a mark
; on the stack. Mark is a special variable binding, whose term is 
; the current subst. When we are about to remove added variables after
; their scope is ended, we locate the mark (using eq?) and check that
; the term bound to the mark is indeed the subst after the mark.
; If it so, then the subst list wasn't perturbed, and we know that
; anything below the mark can't possibly contain the reference to the
; variable we're about to remove.

(define-syntax exists
  (syntax-rules ()
    [(_ () ant) ant]
    [(_ (id ...) ant)
     (let-lv (id ...)
       (lambda@ (sk fk in-subst)
	 (@ ant
            (lambda@ (fk out-subst)
              (@ sk fk (prune-subst (list id ...) in-subst out-subst)))
            fk in-subst)))]))

; check if any of vars occur in a term
(define relatively-ground?
  (lambda (term vars)
    (cond
      [(var? term) (not (memq term vars))]
      [else #t])))

; PRUNE IN-SUBST SUBST ID ....
; remove the bindings of ID ... from SUBST (by composing with the
; rest of subst). IN-SUBST is the mark.
; If we locate IN-SUBST in SUBST, we know that everything below the
; mark can't possibly contain ID ...

(define compose-subst/own-survivors
  (lambda (base refining survivors)
    (let refine ([b* base])
      (if (null? b*) survivors
          (cons-if-real-commitment
            (commitment->var (car b*))
            (subst-in (commitment->term (car b*)) refining)
            (refine (cdr b*)))))))

(define compose-subst
  (lambda (base refining)
    (compose-subst/own-survivors base refining
      (let survive ([r* refining])
        (cond
          [(null? r*) '()]
          [(assq (commitment->var (car r*)) base) (survive (cdr r*))]
          [else (cons (car r*) (survive (cdr r*)))])))))

(define prune-subst
  (lambda (vars in-subst subst)
    (if (eq? subst in-subst)
        subst
        (let loop ([current subst] [to-remove '()] [clean '()] [to-subst '()])
          (cond
            [(null? current) (compose-subst/own-survivors to-subst to-remove clean)]
            [(eq? current in-subst)
             (compose-subst/own-survivors to-subst to-remove (append clean current))]
            [(memq (commitment->var (car current)) vars)
             (loop (cdr current) (cons (car current) to-remove) clean to-subst)]
            [(relatively-ground? (commitment->term (car current)) vars)
             (loop (cdr current) to-remove (cons (car current) clean) to-subst)]
            [else (loop (cdr current) to-remove clean (cons (car current) to-subst))])))))

(print-gensym #f)
; (define var
;   (lambda (id)
;     (cons 'var id)))
; (define var?
;   (lambda (x)
;     (and (pair? x) (eqv? (car x) 'var))))
; (define var-id
;   (lambda (x)
;     (if (var? x) (cdr x) (error 'var-id "Invalid Logic Variable: ~s" x))))
;;; ------------------------------------------------------

(define commitment cons)             ;;; change to list
(define commitment->term cdr)       ;;; and change to cadr
(define commitment->var car)

(define empty-subst '())

(define unit-subst
  (lambda (var t)
    (if (and (var? t) (eq? t _)) empty-subst (list (commitment var t)))))

(define extend-subst
  (lambda (unbound-var contains-no-bound-vars subst)
    (cons (commitment unbound-var contains-no-bound-vars) subst)))

(define cons-if-real-commitment
  (lambda (var term subst)
    (cond
      [(eq? term var) subst]
      [else (cons (commitment var term) subst)])))

(define subst-in  ;;; This definition will change several times.
  (lambda (t subst)
    (cond
      [(var? t)
       (cond
         [(assq t subst) => commitment->term]
         [else t])]
      [else t])))

(define unify
  (lambda (t u subst)
    (cond
      [(unify* (subst-in t subst) (subst-in u subst))
       => (lambda (refining-subst)
            (compose-subst subst refining-subst))]
      [else #f])))

(define unify*
  (lambda (t u)
    (cond
      [(trivially-equal? t u) empty-subst]
      [(var? t) (unit-subst t u)]
      [(var? u) (unit-subst u t)]
      [else #f])))

(define trivially-equal?
  (lambda (t u)
    (or (eqv? t u) ;;; must stay eqv?
        (and (string? t) (string? u) (string=? t u))
        (eq? t _)
        (eq? u _))))

(define _ (let-lv (_) _))

(test-check 'test-nonrecursive-unify
  (let-lv (x y)
    (and
      (equal?
	(unify x 3 empty-subst)
	`(,(commitment x 3)))
      (equal?
	(unify 4 y empty-subst)
	`(,(commitment y 4)))
      (equal?
	(unify x y empty-subst)
	`(,(commitment x y)))
      (equal?
	(unify 'x 'x empty-subst)
	'())
      (equal?
	(unify x x empty-subst)
	'())
      (equal?
	(unify 4 'y empty-subst)
	#f)
      (equal?
	(unify 'x 3 empty-subst)
	#f)
      (equal?
	(unify 3 4 empty-subst)
	#f)))
  #t)


(define == 
  (lambda (x y)
    (lambda@ (sk fk subst)
      (cond
        [(unify x y subst)
         => (lambda (subst)
              (@ sk fk subst))]
        [else (fk)]))))

(define-syntax ==
  (syntax-rules ()
    [(_ t u)
     (lambda@ (sk fk subst)
       (cond
         [(unify t u subst)
          => (lambda (subst)
               (@ sk fk subst))]
         [else (fk)]))]))

;(load "plprelims.ss")

;  Fk  = () -> Ans
;  Ans =  Nil + [Subst,Fk]
;  Sk = Fk -> Subst -> Ans  
;  Antecedent = Sk -> Sk
;  Rule = Antecedent -> [Goal-fn,Int] -> Antecedent

;  relation: Term -> Antecedent
;  to-show: Term -> Antecedent -> Rule
;  initial-sk : Sk
;  initial-fk : Fk

;(load "expand-only.ss")

;quasiquote has been coded by Oscar Waddell.
(define-syntax quasiquote
  (let ([tmplid #'barney-the-purple-dinosaur])
    (lambda (x)
      (import scheme)
      (define lexical?
        (lambda (id)
          (not
            (free-identifier=? id
              (datum->syntax-object tmplid
                (syntax-object->datum id))))))
      (define check
        (lambda (x)
          (syntax-case x (unquote unquote-splicing)
            [(unquote e) (void)]
            [(unquote-splicing e) (void)]
            [(,e . rest) (check #'rest)]
            [(,@e . rest) (check #'rest)]
            [(car . cdr) (begin (check #'car) (check #'cdr))]
            [id
              (identifier? #'id)
              (when (lexical? #'id)
                (parameterize ([error-handler (warning-handler)]
                               [reset-handler values])
                  (syntax-error #'id "looks like you're missing , or ,@ on")))]
            [other (void)])))
      (syntax-case x ()
        [(_ . whatever)
         (begin
           (check #'whatever)
           #'(quasiquote . whatever))]))))

(define concretize-var    ;;; returns two values
  (lambda (var env)
    (cond
      [(assq var env)
       => (lambda (var-c)
            (values (artificial-id var-c) env))]
      [else (let ([var-c `(,var . ,(cond
                                     [(assq/var-id (var-id var) env)
                                      => (lambda (var-c) (+ (cdr var-c) 1))]
                                     [else 0]))])
              (values (artificial-id var-c) (cons var-c env)))])))

(define concretize-term ;;; assumes no pairs; returns two values.
  (lambda (t env)
    (cond
      [(var? t) (concretize-var t env)]
      [else (values t env)])))

(define concretize-subst  ;;; returns a single value.
  (letrec
      ([cs (lambda (subst env)
             (cond
               [(null? subst) '()]
               [else
                 (let ([comm (car subst)])
                   (let-values (cv new-env)
                     (concretize-var (commitment->var comm) env)
                     (let-values (ct newer-env)
                       (concretize-term (commitment->term comm) new-env)
                       (cons
                         (commitment cv ct)
                         (cs (cdr subst) newer-env)))))]))])
    (lambda (subst)
      (cs subst '()))))

(define artificial-id
  (lambda (var-c)
    (string->symbol
      (string-append
        (symbol->string (var-id (car var-c))) "." (number->string (cdr var-c))))))

(define assq/var-id
  (lambda (id env)
    (cond
      [(null? env) #f]
      [(eq? (var-id (caar env)) id) (car env)]
      [else (assq/var-id id (cdr env))])))

(define-syntax trace-lambda@
  (syntax-rules ()
    [(_ id () body0 body1 ...) (begin body0 body1 ...)]
    [(_ id (formal0 formal1 ...) body0 body1 ...)
     (trace-lambda id (formal0)
       (trace-lambda@ id (formal1 ...) body0 body1 ...))]))

(define empty-subst? null?)

(let-lv (x y)
  (test-check 'test-compose-subst-0
    (append (unit-subst x y) (unit-subst y 52))
    `(,(commitment x y) ,(commitment y 52))))


(test-check 'test-compose-subst-1
  (let-lv (x y)
    (equal?
      (compose-subst (unit-subst x y) (unit-subst y 52))
      `(,(commitment x 52) ,(commitment y 52))))
  #t)

(test-check 'test-compose-subst-2
  (let-lv (w x y)
    (equal?
      (let ([s (compose-subst (unit-subst y w) (unit-subst w 52))])
	(compose-subst (unit-subst x y) s))
      `(,(commitment x 52) ,(commitment y 52) ,(commitment w 52))))
  #t)

(test-check 'test-compose-subst-3
  (let-lv (w x y)
    (equal?
      (let ([s (compose-subst (unit-subst w 52) (unit-subst y w))])
	(compose-subst (unit-subst x y) s))
      `(,(commitment x w) ,(commitment w 52) ,(commitment y w))))
  #t)

(test-check 'test-compose-subst-4
  (let-lv (x y z)
    (equal?
      (let ([s (compose-subst (unit-subst y z) (unit-subst x y))]
	    [r (compose-subst
		 (compose-subst (unit-subst x 'a) (unit-subst y 'b))
		 (unit-subst z y))])
	(compose-subst s r))
      `(,(commitment x 'b) ,(commitment z y))))
  #t)

(test-check 'test-compose-subst-5
  (concretize-subst
    (compose-subst
      (let-lv (x) (unit-subst x 3))
      (let-lv (x) (unit-subst x 4))))
  '((x.0 . 3) (x.1 . 4)))

(define initial-fk (lambda () '()))
(define initial-sk (lambda@ (fk subst)
		     ;(pretty-print subst)
		     (cons subst fk)))


;-----------------------------------------------------------
; Sequencing of relations
; Antecedent is a multi-valued function (which takes
;   sk, fk, subst and exits to either sk or fk).
; A relation is a parameterized antecedent.
;
; All sequencing operations are defined on antecedents.
; They can be "lifted" to relations (see below).
; 

; Conjunctions
; All conjunctions below satisfy properties
;    ans is an answer of (a-conjunction ant1 ant2 ...) ==>
;       forall i. ans is an answer of ant_i
;    (a-conjunction) ==> true


; (all ant1 ant2 ...)
; A regular Prolog conjunction. Non-deterministic (i.e., can have 0, 1,
; or more answers).
; Properties:
;  (all ant) ==> ant
;  (all ant1 ... ant_{n-1} antn) is a "join" of answerlists of
;        (all ant1 ... ant_{n-1}) and antn

(define-syntax all
  (syntax-rules ()
    [(_) (lambda@ (sk) sk)]
    [(_ ant) ant]
    [(_ ant0 ant1 ...)
     (lambda@ (sk)
       (splice-in-ants/all sk ant0 ant1 ...))]))

(define-syntax splice-in-ants/all
  (syntax-rules ()
    [(_ sk ant) (@ ant sk)]
    [(_ sk ant0 ant1 ...)
     (@ ant0 (splice-in-ants/all sk ant1 ...))]))


(define succeed (all))

; (promise-one-answer ant)
; Operationally, it is the identity.
; It is an optimization directive: if the user knows that an antecedent
; can produce at most one answer, he can tell the system about it.
; The behavior is underfined if the user has lied.

(define-syntax promise-one-answer
  (syntax-rules ()
    ((_ ant) ant)))


; (all! ant1 ant2 ...)
; A committed choice nondeterminism conjunction
; From the Mercury documentation:

;   In addition to the determinism annotations described earlier, there
;   are "committed choice" versions of multi and nondet, called cc_multi
;   and cc_nondet. These can be used instead of multi or nondet if all
;   calls to that mode of the predicate (or function) occur in a context
;   in which only one solution is needed.
;
; (all! ant) evaluates ant in a single-choice context. That is,
; if ant fails, (all! ant) fails. If ant has at least one answer,
; this answer is returned.
; (all! ant) has at most one answer regardless of the answers of ant.
;   ans is an asnwer of (all! ant) ==> ans is an answer of ant
; The converse is not true.
; Corollary: (all! ant) =/=> ant
; Corollary: ant is (semi-) deterministic: (all! ant) ==> ant
; (all! (promise-one-answer ant)) ==> ant
;
; By definition, (all! ant1 ant2 ...) ===> (all! (all ant1 ant2 ...))

(define-syntax all!
  (syntax-rules (promise-one-answer)
    [(_) (promise-one-answer (all))]
    [(_ (promise-one-answer ant)) (promise-one-answer ant)] ; keep the mark
    [(_ ant0 ant1 ...)
     (promise-one-answer
       (lambda@ (sk fk)
	 (@
	   (splice-in-ants/all (lambda@ (fk-ign) (@ sk fk)) ant0 ant1 ...)
	   fk)))]))

; (all!! ant1 ant2 ...)
; Even more committed choice nondeterministic conjunction
; It evaluates all elements of the conjunction in a single answer context
; (all!! ant) ==> (all! ant) =/=> ant
; (all!! ant1 ant2 ...) ==> (all (all! ant1) (all! ant2) ...)
;                       ==> (all! (all! ant1) (all! ant2) ...)
; (all!! ant1 ... antn (promise-one-answer ant)) ==>
;    (all (all!! ant1 ... antn) ant)

(define-syntax all!!
  (syntax-rules ()
    [(_) (all!)]
    [(_ ant) (all! ant)]
    [(_ ant0 ant1 ...)
      (promise-one-answer 
	(lambda@ (sk fk)
	  (splice-in-ants/all!! sk fk ant0 ant1 ...)))]))

(define-syntax splice-in-ants/all!!
  (syntax-rules (promise-one-answer)
    [(_ sk fk)
      (@ sk fk)]
    [(_ sk fk (promise-one-answer ant))
      (@ ant sk fk)]
    [(_ sk fk ant0 ant1 ...)
      (@ ant0 (lambda (fk-ign) (splice-in-ants/all!! sk fk ant1 ...)) fk)]))

; (if-only COND THEN)
; (if-only COND THEN ELSE)
; Here COND, THEN, ELSE are antecedents.
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

(define-syntax if-only
  (syntax-rules ()
    ((_ condition then)
      (lambda@ (sk fk)
	(@ condition
	  ; sk from cond
	  (lambda@ (fk-ign) (@ then sk fk))
	  ; failure from cond
	  fk)))
    ((_ condition then else)
      (lambda@ (sk fk)
	(@ condition
	  (lambda@ (fk-ign) (@ then sk fk))
	  (lambda () (@ else sk fk)))))
))

; (if-all! (COND1 ... CONDN) THEN)
; (if-all! (COND1 ... CONDN) THEN ELSE)
;
; (if-all! (COND1 ... CONDN) THEN ELSE) ==>
;   (if-only (all! COND1 ... CONDN) THEN ELSE)
; (if-all! (COND1) THEN ELSE) ==>
;   (if-only COND1 THEN ELSE)

(define-syntax if-all!
  (syntax-rules ()
    [(_ (condition) then) (if-only condition then)]
    [(_ (condition) then else) (if-only condition then else)]
    [(_ (condition1 condition2 ...) then)
     (lambda@ (sk fk)
       (@ (splice-in-ants/all
            (lambda@ (fk-ign)
              (@ then sk fk))
            condition1 condition2 ...)
          fk))]
    [(_ (condition1 condition2 ...) then else)
     (lambda@ (sk fk)
       (@ (splice-in-ants/all
            (lambda@ (fk-ign)
              (@ then sk fk)) condition1 condition2 ...)
          (lambda ()
            (@ else sk fk))))]))

; Disjunction of antecedents
; All disjunctions below satisfy properties
;  ans is an answer of (a-disjunction ant1 ant2 ...) ==>
;    exists i. ans is an answer of ant_i
; (a-disjunction) ==> fail

; Any disjunction. A regular Prolog disjunction (introduces
; a choicepoints, in Prolog terms)
; Note that 'any' is not a union! In particular, it is not
; idempotent.
; (any) ===> fail
; (any ant) ===> ant
; (any ant1 ... antn) ==> _concatenation_ of their answerlists

(define-syntax any
  (syntax-rules ()
    [(_) (lambda@ (sk fk subst) (fk))]
    [(_ ant) ant]
    [(_ ant ...)
      (lambda@ (sk fk subst)
	(splice-in-ants/any sk fk subst ant ...))]))

(define-syntax splice-in-ants/any
  (syntax-rules ()
    [(_ sk fk subst ant1) (@ ant1 sk fk subst)]
    [(_ sk fk subst ant1 ant2 ...)
     (@ ant1 sk (lambda ()
                  (splice-in-ants/any sk fk subst ant2 ...))
       subst)]))

(define fail (any))


; Negation
; (fails ant) succeeds iff ant has no solutions
; (fails ant) is a semi-deterministic predicate: it can have at most
; one solution
; (succeeds ant) succeeds iff ant has a solution
;
; (fails (fails ant)) <===> (succeeds ant)
; but (succeeds ant) =/=> ant
; Cf. (equal? (not (not x)) x) is #f in Scheme in general.

(define fails
  (lambda (ant)
    (lambda@ (sk fk subst)
      (@ ant
        (lambda@ (current-fk subst) (fk))
        (lambda () (@ sk fk subst))
        subst))))

(define succeeds
  (lambda (ant)
    (lambda@ (sk fk subst)
      (@ ant (lambda@ (fk-ign subst-ign) (@ sk fk subst))
	fk subst))))

; partially-eval-sant: Partially evaluate a semi-antecedent
; An semi-antecedent is an expression that, when applied to
; two arguments, sk fk, can produce zero, one, or
; more answers.
; Any antecedent can be turned into a semi-antecedent if partially applied
; to subst.
; The following higher-order semi-antecedent takes an
; antecedent and yields the first answer and another, residual
; antecedent. The latter, when evaluated, will give the rest
; of the answers of the original semi-antecedent.
; partially-eval-sant could be implemented with streams (lazy
; lists). The following is a purely combinational implementation.
;
; (@ partially-eval-sant sant a b) =>
;   (b) if sant has no answers
;   (a s residial-sant) if sant has a answer. That answer is delivered
;                       in s. 
; The residial semi-antecedent can be passed to partially-eval-sant
; again, and so on, to obtain all answers from an antecedent one by one.

; The following definition is eta-reduced.

(define (partially-eval-sant sant)
  (@ sant
    (lambda@ (fk subst a b)
      (@ a subst 
	(lambda@ (sk1 fk1)
	  (@
	    (fk) 
	    ; new a
	    (lambda@ (sub11 x) (@ sk1 (lambda () (@ x sk1 fk1)) sub11))
	    ; new b
	    fk1))))
    (lambda () (lambda@ (a b) (b)))))

(define (ant->sant ant subst)
  (lambda@ (sk fk)
    (@ ant sk fk subst)))

; An interleaving disjunction.
; Declaratively, any-interleave is the same as any.
; Operationally, any-interleave schedules each component antecedent
; in round-robin. So, any-interleave is fair: it won't let an antecedent
; that produces infinitely many answers (such as repeat) starve the others.
; any-interleave introduces a breadth-first-like traversal of the
; decision tree.
; I seem to have seen a theorem that says that a _fair_ scheduling
; (like that provided by any-interleave) entails a minumal or well-founded
; semantics of a Prolog program.

(define-syntax any-interleave
  (syntax-rules ()
    [(_) fail]
    [(_ ant) ant]
    [(_ ant ...)
      (lambda@ (sk fk subst)
	(interleave sk fk
	  (list (ant->sant ant subst) ...)))]))

; we treat sants as a sort of a circular list
(define (interleave sk fk sants)
  (cond
    ((null? sants) (fk))		; all of the sants are finished
    ((null? (cdr sants))
      ; only one sants left -- run it through the end
      (@ (car sants) sk fk))
    (else
      (let loop ((curr sants) (residuals '()))
	; check if the current round is finished
	(if (null? curr) (interleave sk fk (reverse residuals))
	  (@
	    partially-eval-sant (car curr)
	    ; (car curr) had an answer
	    (lambda@ (subst residual)
	      (@ sk
	        ; re-entrance cont
		(lambda () (loop (cdr curr) (cons residual residuals)))
		subst))
	  ; (car curr) is finished - drop it, and try next
	  (lambda () (loop (cdr curr) residuals))))))))

; An interleaving disjunction removing duplicates: any-union
; This is a true union of the constituent antecedents: it is fair, and
; it removes overlap in the antecedents to union, if any. Therefore,
;    (any-union ant ant) ===> ant
; whereas (any ant ant) =/=> ant
; because the latter has twice as many answers as ant.
;
; Any-union (or interleave-non-overlap, to be precise) is quite similar
; to the function interleave above. But now, the order of antecedents
; matters. Given antecedents ant1 ant2 ... antk ... antn,
; at the k-th step we try to partially-eval antk. If it yields an answer,
; we check if ant_{k+1} ... antn can be satisfied with that answer.
; If any of them does, we disregard the current answer and ask antk for
; another one. We maintain the invariant that
;  ans is an answer of (any-union ant1 ... antn) 
;  ===> exists i. ans is an answer of ant_i
;       && forall j>i. ans is not an answer of ant_j
; The latter property guarantees the true union.
; Note the code below does not check if answers of each individual
; antecedent are unique. It is trivial to modify the code so that
; any-union removes the duplicates not only among the antecedents but
; also within an antecedent. That change entails a run-time cost. More
; importantly, it breaks the property
; (any-union ant ant) ===> ant
; Only a weaker version, (any-union' ant ant) ===> (any-union' ant)
; would hold. Therefore, we do not do that change.

(define-syntax any-union
  (syntax-rules ()
    [(_) fail]
    [(_ ant) ant]
    [(_ ant ...)
      (lambda@ (sk fk subst)
	(interleave-non-overlap sk fk
	  (list (cons (ant->sant ant subst) ant) ...)))]))

; we treat saants as a sort of a circular list
; Each element of saants is a pair (sant . ant)
; where ant is the original antecedent (needed for the satisfiability testing)
; and sant is the corresponding semi-antecedent or a 
; residual thereof.
(define (interleave-non-overlap sk fk saants)
  (let outer ((saants saants))
    (cond
      ((null? saants) (fk))		; all of the saants are finished
      ((null? (cdr saants))
        ; only one ant is left -- run it through the end
	(@ (caar saants) sk fk))
      (else
	(let loop ((curr saants) (residuals '()))
	  ; check if the current round is finished
	  (if (null? curr) (outer (reverse residuals))
	  (@
	    partially-eval-sant (caar curr)
	    ; (caar curr) had an answer
	    (lambda@ (subst residual)
	      ; let us see now if the answer, subst, satisfies any of the
	      ; ants down the curr.
	      (let check ((to-check (cdr curr)))
		(if (null? to-check) ; OK, subst is unique, give it to user
		  (@ sk
	           ; re-entrance cont
		    (lambda () (loop (cdr curr) 
				 (cons (cons residual (cdar curr)) residuals)))
		    subst)
		  (@ (cdar to-check)
		    ; subst was the answer to some other ant: check failed
		    (lambda@ (fk1 subst1) 
		      (loop (cdr curr) 
			(cons (cons residual (cdar curr)) residuals)))
		    ; subst was not the answer: continue check
		    (lambda () (check (cdr to-check)))
		    subst))))
	  ; (car curr) is finished - drop it, and try next
	  (lambda () (loop (cdr curr) residuals)))))))))

; Another if-then-else
; (if-some COND THEN)
; (if-some COND THEN ELSE)
; Here COND, THEN, ELSE are antecedents.
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
; We can implement if-some with partially-eval-sant. Given a COND, we
; peel of one answer, if possible. If it is, we then execute THEN
; passing it the answer and the fk from COND so that if THEN fails,
; it can obtain another answer. If COND has no answers, we execute
; ELSE. Again, we can do all that purely declaratively, without
; talking about introducing and destroying choice points.

(define-syntax if-some
  (syntax-rules ()
    ((_ condition then) (all condition then))
    ((_ condition then else)
      (lambda@ (sk fk subst)
	(@ partially-eval-sant (ant->sant condition subst)
	  (lambda@ (ans residual)
	    (@ then sk
	      ; then failed. Check to see if condition has another answer
	      (lambda () (@ residual (@ then sk) fk))
	      ans))
	  ; condition failed
	  (lambda () (@ else sk fk subst)))))
))


; Relations...........................

(define-syntax relation
  (syntax-rules (to-show)
    [(_ (ex-id ...) (to-show x ...) ant ...)     
     (relation (ex-id ...) () (x ...) (x ...) ant ...)]
    [(_ (ex-id ...) (var ...) (x0 x1 ...) xs ant ...)
     (relation (ex-id ...) (var ... g) (x1 ...) xs ant ...)]
    [(_ (ex-id ...) () () () ant ...)
     (lambda ()
       (exists (ex-id ...)
         (all ant ...)))]
    [(_ (ex-id ...) (g ...) () (x ...))
     (lambda (g ...)
       (exists (ex-id ...)
 	 (all!! (promise-one-answer (== g x)) ...)))]
    [(_ (ex-id ...) (g ...) () (x ...) ant)
     (lambda (g ...)
       (exists (ex-id ...)
 	 (if-all! ((promise-one-answer (== g x)) ...) ant)))]
    [(_ (ex-id ...) (g ...) () (x ...) ant ...)
     (lambda (g ...)
       (exists (ex-id ...)
         (all (all!! (promise-one-answer (== g x)) ...) ant ...)))]))

; (define-syntax relation/cut
;   (syntax-rules (to-show)
;     [(_ cut-id (ex-id ...) (to-show x ...) ant ...)
;      (relation/cut cut-id (ex-id ...) () (x ...) (x ...) ant ...)]
;     [(_ cut-id ex-ids (var ...) (x0 x1 ...) xs ant ...)
;      (relation/cut cut-id ex-ids (var ... g) (x1 ...) xs ant ...)]
;     [(_ cut-id (ex-id ...) (g ...) () (x ...) ant ...)
;      (lambda (g ...)
;        (exists (ex-id ...)
;          (all! (== g x) ...
;            (lambda@ (sk fk subst cutk)
;              (let ([cut-id (!! cutk)])
;                (@ (all ant ...) sk fk subst cutk))))))]))

(define-syntax fact
  (syntax-rules ()
    [(_ (ex-id ...) x ...)
     (relation (ex-id ...) (to-show x ...))]))

; Lifting from antecedents to relations
; (define-rel-lifted-comb rel-syntax ant-proc-or-syntax)
; Given (ant-proc-or-syntax ant ...)
; define 
; (rel-syntax (id ...) rel-exp ...)
; We should make rel-syntax behave as a CBV function, that is,
; evaluate rel-exp early.
; Otherwise, things like
; (define father (extend-relation father ...))
; loop.

; (define-syntax extend-relation
;   (syntax-rules ()
;     [(_ (id ...) rel-exp ...)
;      (extend-relation-aux (id ...) () rel-exp ...)]))

; (define-syntax extend-relation-aux
;   (syntax-rules ()
;     [(_ (id ...) ([g rel-exp] ...))
;      (let ([g rel-exp] ...)
;        (lambda (id ...)
;          (any (g id ...) ...)))]
;     [(_ (id ...) (let-pair ...) rel-exp0 rel-exp1 ...)
;      (extend-relation-aux (id ...)
;        (let-pair ... [g rel-exp0]) rel-exp1 ...)]))

(define-syntax define-rel-lifted-comb
  (syntax-rules ()
    ((_ rel-syntax-name ant-proc-or-syntax)
      (define-syntax rel-syntax-name
	(syntax-rules ()
	  ((_ ids . rel-exps)
	    (lift-ant-to-rel-aux ant-proc-or-syntax ids () . rel-exps)))))))

(define-syntax lift-ant-to-rel-aux
  (syntax-rules ()
    [(_ ant-handler (id ...) ([g rel-var] ...))
     (let ([g rel-var] ...)
       (lambda (id ...)
         (ant-handler (g id ...) ...)))]
    [(_ ant-handler ids (let-pair ...) rel-exp0 rel-exp1 ...)
     (lift-ant-to-rel-aux ant-handler ids 
       (let-pair ... [g rel-exp0]) rel-exp1 ...)]))

(define-rel-lifted-comb extend-relation any)

; The following  antecedent-to-relations 
; transformers are roughly equivalent. I don't know which is better.
; see examples below.

; (lift-to-relations ids (ant-comb rel rel ...))
(define-syntax lift-to-relations
  (syntax-rules ()
    ((_ ids (ant-comb rel ...))
      (lift-ant-to-rel-aux ant-comb ids () rel ...))))

; (let-ants ids ((name rel) ...) body)
(define-syntax let-ants
  (syntax-rules ()
    ((_ (id ...) ((ant-name rel-exp) ...) body)
      (lambda (id ...)
	(let ((ant-name (rel-exp id ...)) ...)
	  body)))))

;------------------------------------------------------------------------
;;;;; Starts the real work of the system.

(define father  
  (relation ()
    (to-show 'jon 'sam)))

(test-check 'test-father0
  (let ([result
          (@ (father 'jon 'sam)
             initial-sk initial-fk empty-subst)])
    (and
      (equal? (car result) '())
      (equal? ((cdr result)) '())))
  #t)

;;; Now we need concretize-subst about here.

(define child-of-male
  (relation (child dad)
    (to-show child dad)
    (father dad child)))

(test-check 'test-child-of-male-0
  (concretize-subst
    (car (@ (child-of-male 'sam 'jon)
	    initial-sk initial-fk empty-subst)))
  ;`(,(commitment 'child.0 'sam) ,(commitment 'dad.0 'jon)))))
  '())  ; variables shouldn't leak


; The mark should be found here...
(define child-of-male-1
  (relation (child dad)
    (to-show child dad)
    (child-of-male dad child)))
(test-check 'test-child-of-male-1
  (concretize-subst
    (car (@ (child-of-male 'sam 'jon)
	    initial-sk initial-fk empty-subst)))
  ;`(,(commitment 'child.0 'sam) ,(commitment 'dad.0 'jon)))))
  '())

(define rob/sal
  (relation ()
    (to-show 'rob 'sal)))

(define new-father
  (extend-relation (a1 a2) father rob/sal))

(test-check 'test-father-1
  (let ([result
	  (@ (new-father 'rob 'sal)
	    initial-sk initial-fk empty-subst)])
    (and
      (equal? (car result) '())
      (equal? ((cdr result)) '())))
  #t)


(define query
  (let ([initial-fk (lambda () '())]
        [initial-sk (lambda@ (fk subst) (cons subst fk))])
    (lambda (antecedent)
      (@ antecedent initial-sk initial-fk empty-subst))))

(test-check 'test-father-2
  (let-lv (x)
    (let ([result (query (new-father 'rob x))])
      (and
	(equal? (car result) `(,(commitment x 'sal)))
	(equal? ((cdr result)) '()))))
  #t)

(define concretize
  (lambda (t)
    (let-values (ct new-env) (concretize-term t '())
      ct)))

(define-syntax concretize-subst/vars
  (syntax-rules ()
    [(_ subst) '()]
    [(_ subst x0 x1 ...)
     (let-values (cx env) (concretize-var x0 '())
       (let-values (ct env) (concretize-term (subst-in x0 subst) env)
         (cons (list cx ct)
           (concretize-subst/vars/env subst env x1 ...))))]))

(define-syntax concretize-subst/vars/env
  (syntax-rules ()
    [(_ subst env) '()]
    [(_ subst env x0 x1 ...)
     (let-values (cv env) (concretize-var x0 env)
       (let-values (ct env) (concretize-term (subst-in x0 subst) env)
         (cons (list cv ct)
           (concretize-subst/vars/env subst env x1 ...))))]))

(test-check 'test-father-3
  (let-lv (x)
    (let ([answer (query (new-father 'rob x))])
      (let ([subst (car answer)])
        (concretize-subst/vars subst x))))
  '((x.0 sal)))

(test-check 'test-father-4
  (let-lv (x y)
    (let ([answer (query (new-father x y))])
      (let ([subst (car answer)])
        (concretize-subst/vars subst x y))))
  '((x.0 jon) (y.0 sam)))

(define rob/pat
  (relation ()
    (to-show 'rob 'pat)))

(define newer-father
  (extend-relation (a1 a2) new-father rob/pat))

(test-check 'test-father-5
  (let-lv (x)
    (and
      (equal?
	(let ([answer1 (query (newer-father 'rob x))])
	  (pretty-print answer1)
	  (let ([subst (car answer1)])
            (list
              (concretize-subst/vars subst x)
              (let ([answer2 ((cdr answer1))])
                (pretty-print answer2)
                (let ([subst (car answer2)])
                  (concretize-subst/vars subst x))))))
	'(((x.0 sal)) ((x.0 pat))))
      (equal?
	(let ([answer1 (query (newer-father 'rob x))])
	  (let ([subst (car answer1)])
	    (cons
              (concretize-subst/vars subst x)
	      (let ([answer2 ((cdr answer1))])
		(let ([subst (car answer2)])
		  (cons
                    (concretize-subst/vars subst x)
		    (let ([answer3 ((cdr answer2))])
		      (if (null? answer3)
                          '()
                          (let ([subst (car answer3)])
                            (cons
                              (concretize-subst/vars subst x)
                              '()))))))))))
        '(((x.0 sal)) ((x.0 pat))))))
  #t)

(define stream-prefix
  (lambda (n strm)
    (if (null? strm) '()
      (cons (car strm)
        (if (zero? n) '()
          (stream-prefix (- n 1) ((cdr strm))))))))

(define concretize
  (lambda (t)
    (let-values (ct new-env) (concretize-term t '())
      ct)))

(define-syntax solve
  (syntax-rules ()
    [(_ n (var ...) ant)
     (let-lv (var ...)
       (map (lambda (subst)
	      (concretize-subst/vars subst var ...))
         (stream-prefix (- n 1) (query ant))))]))

(define sam/rob
  (relation ()
    (to-show 'sam 'rob)))

(define newest-father (extend-relation (a1 a2) newer-father sam/rob))

(test-check 'test-father-6/solve
  (and
    (equal?
      (solve 5 (x) (newest-father 'rob x))
      '(((x.0 sal)) ((x.0 pat))))
    (equal?
      (solve 6 (x y) (newest-father x y))
      '(((x.0 jon) (y.0 sam))
        ((x.0 rob) (y.0 sal))
        ((x.0 rob) (y.0 pat))
        ((x.0 sam) (y.0 rob)))))
  #t)


; (define-syntax binary-intersect
;   (syntax-rules ()
;     ((_ ant1 ant2)
;       (lambda@ (sk)
; 	(@ ant1 (@ ant2 sk))))))

(define-syntax binary-intersect
  (syntax-rules ()
    ((_ ant1 ant2) (all ant1 ant2))))

(define-rel-lifted-comb binary-intersect-relation binary-intersect)

(define parents-of-scouts
  (extend-relation (a1 a2)
    (fact () 'sam 'rob)
    (fact () 'roz 'sue)
    (fact () 'rob 'sal)))

(define parents-of-athletes
  (extend-relation (a1 a2)
    (fact () 'sam 'roz)
    (fact () 'roz 'sue)
    (fact () 'rob 'sal)))

(define busy-parents
  (binary-intersect-relation (a1 a2) 
    parents-of-scouts parents-of-athletes))

(define busy-parents
  (binary-intersect-relation (a1 a2) 
    parents-of-scouts parents-of-athletes))

(test-check 'test-busy-parents
  (solve 5 (x) (exists (y) (busy-parents x y)))
  '(((x.0 roz)) ((x.0 rob))))

; (define-syntax intersect-relation
;   (syntax-rules ()
;     [(_ (id ...) rel-exp) rel-exp]
;     [(_ (id ...) rel-exp0 rel-exp1 rel-exp2 ...)
;      (binary-intersect-relation (id ...) rel-exp0
;        (intersect-relation (id ...) rel-exp1 rel-exp2 ...))]))

(define-rel-lifted-comb intersect-relation all)

(define busy-parents
  (intersect-relation (a1 a2) parents-of-scouts parents-of-athletes))

(define conscientious-parents
  (extend-relation (a1 a2) parents-of-scouts parents-of-athletes))

(test-check 'test-conscientious-parents
  (solve 7 (x y) (conscientious-parents x y))
  '(((x.0 sam) (y.0 rob))
    ((x.0 roz) (y.0 sue))
    ((x.0 rob) (y.0 sal))
    ((x.0 sam) (y.0 roz))
    ((x.0 roz) (y.0 sue))
    ((x.0 rob) (y.0 sal))))

(define-syntax solution
  (syntax-rules ()
    [(_ (var ...) x)
     (let ([ls (solve 1 (var ...) x)])
       (if (null? ls) #f (car ls)))]))

(test-check 'test-father-7/solution
  (solution (x) (newest-father 'rob x))
  '((x.0 sal)))

(define grandpa-sam
  (relation (grandchild)
    (to-show grandchild)
    (exists (parent)
      (lambda (sk)
        ((newest-father 'sam parent)
         ((newest-father parent grandchild) sk))))))

(test-check 'test-grandpa-sam-1
  (solve 6 (y) (grandpa-sam y))
  '(((y.0 sal)) ((y.0 pat))))


(define child
  (relation (child dad)
    (to-show child dad)
    (newest-father dad child)))

(test-check 'test-child-1
  (solve 10 (x y) (child x y))
  '(((x.0 sam) (y.0 jon))
    ((x.0 sal) (y.0 rob))
    ((x.0 pat) (y.0 rob))
    ((x.0 rob) (y.0 sam))))

(define grandpa-sam
  (relation (grandchild)
    (to-show grandchild)
    (exists (parent)
      (all
        (newest-father 'sam parent)
        (newest-father parent grandchild)))))

(test-check 'test-grandpa-sam-2
  (solve 6 (y) (grandpa-sam y))
  '(((y.0 sal)) ((y.0 pat))))

(define grandpa-maker
  (lambda (grandad)
    (relation (grandchild)
      (to-show grandchild)
      (exists (parent)
        (all
          (newest-father grandad parent)
          (newest-father parent grandchild))))))

(test-check 'test-grandpa-maker-1
  (solve 6 (x) ((grandpa-maker 'sam) x))
  '(((x.0 sal)) ((x.0 pat))))

(define grandpa-maker
  (lambda (guide* grandad*)
    (relation (grandchild)
      (to-show grandchild)
      (exists (parent)
        (all
          (guide* grandad* parent)
          (guide* parent grandchild))))))


(test-check 'test-grandpa-maker-2
  (solve 4 (x) ((grandpa-maker newest-father 'sam) x))
  '(((x.0 sal)) ((x.0 pat))))

(define grandpa
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (newest-father grandad parent)
        (newest-father parent grandchild)))))

(test-check 'test-grandpa-1
  (solve 4 (x) (grandpa 'sam x))
  '(((x.0 sal)) ((x.0 pat))))

(define-syntax fact
  (syntax-rules ()
    [(_ (var ...) x ...) (relation (var ...) (to-show x ...))]))

(define-syntax trace-fact
  (syntax-rules ()
    [(_ id (var ...) x ...) (trace-relation id (to-show (var ...) x ...))]))

(define father
  (extend-relation (a1 a2)
    (fact () 'jon 'sam)
    (extend-relation (a1 a2)
      (fact () 'sam 'rob)
      (extend-relation (a1 a2)
        (fact () 'sam 'roz)
        (extend-relation (a1 a2)
          (fact () 'rob 'sal)
          (fact () 'rob 'pat))))))

(define mother
  (extend-relation (a1 a2)
    (fact () 'roz 'sue)
    (fact () 'roz 'sid)))

(define grandpa
  (extend-relation (a1 a2)
    (relation (grandad grandchild)
      (to-show grandad grandchild)
      (exists (parent)
        (all
          (father grandad parent)
          (father parent grandchild))))
    (relation (grandad grandchild)
      (to-show grandad grandchild)
      (exists (parent)
        (all
          (father grandad parent)
          (mother parent grandchild))))))

(test-check 'test-grandpa-2
  (solve 10 (y) (grandpa 'sam y))
  '(((y.0 sal)) ((y.0 pat)) ((y.0 sue)) ((y.0 sid))))

(define grandpa/father
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (father parent grandchild)))))

(define grandpa/mother
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (mother parent grandchild)))))

(define grandpa
  (extend-relation (a1 a2) grandpa/father grandpa/mother))

(test-check 'test-grandpa-5
  (solve 10 (y) (grandpa 'sam y))
  '(((y.0 sal)) ((y.0 pat)) ((y.0 sue)) ((y.0 sid))))

(define grandpa-sam
  (let ([r (relation (child)
             (to-show child)
             (exists (parent)
               (all
                 (father 'sam parent)
                 (father parent child))))])
    (relation (child)
      (to-show child)
      (r child))))

(test-check 'test-grandpa-55
  (solve 6 (y) (grandpa-sam y))
  '(((y.0 sal)) ((y.0 pat))))

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
(define grandpa/father
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all!
        (father grandad parent)
        (father parent grandchild)))))

(define grandpa/mother
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (mother parent grandchild)))))

(define grandpa
  (lift-to-relations (a1 a2)
    (all!
      (extend-relation (a1 a2) grandpa/father grandpa/mother))))

(test-check 'test-grandpa-8
  (solve 10 (x y) (grandpa x y))
  '(((x.0 jon) (y.0 rob))))

; The solution that used to require cuts
; (define grandpa/father
;   (relation/cut cut (grandad grandchild)
;     (to-show grandad grandchild)
;     (exists (parent)
;       (all cut (father grandad parent) (father parent grandchild)))))

(define grandpa/father
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all (father grandad parent) (father parent grandchild)))))

; Properly, this requires soft cuts, aka *->, or Mercury's
; if-then-else. But we emulate it...
(define grandpa
  (let-ants (a1 a2) ((grandpa/father grandpa/father)
		     (grandpa/mother grandpa/mother))
    (if-only (succeeds grandpa/father) grandpa/father grandpa/mother)))

(test-check 'test-grandpa-10
  (solve 10 (x y) (grandpa x y))
  '(((x.0 jon) (y.0 rob))
    ((x.0 jon) (y.0 roz))
    ((x.0 sam) (y.0 sal))
    ((x.0 sam) (y.0 pat))))

; Now do it with soft-cuts
(define grandpa
  (let-ants (a1 a2) ((grandpa/father grandpa/father)
		     (grandpa/mother grandpa/mother))
    (if-some grandpa/father succeed grandpa/mother)))

(test-check 'test-grandpa-10-soft-cut
  (solve 10 (x y) (grandpa x y))
  '(((x.0 jon) (y.0 rob))
    ((x.0 jon) (y.0 roz))
    ((x.0 sam) (y.0 sal))
    ((x.0 sam) (y.0 pat))))

(define a-grandma
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all! (mother grandad parent)))))

(define no-grandma-grandpa
  (let-ants (a1 a2) ((a-grandma a-grandma) (grandpa grandpa))
    (if-only a-grandma fail grandpa)))

(test-check 'test-no-grandma-grandpa-1
  (solve 10 (x) (no-grandma-grandpa 'roz x))
  '())


(define parents-of-scouts
  (extend-relation (a1 a2)
    (fact () 'sam 'rob)
    (fact () 'roz 'sue)
    (fact () 'rob 'sal)))

(define fathers-of-cubscouts
  (extend-relation (a1 a2)
    (fact () 'sam 'bob)
    (fact () 'tom 'adam)
    (fact () 'tad 'carl)))

(test-check 'test-partially-eval-sant
  (let-lv (p1 p2)
    (let* ((parents-of-scouts-sant
	     (ant->sant (parents-of-scouts p1 p2) empty-subst))
	    (cons@ (lambda@ (x y) (cons x y)))
	    (split1 (@ 
		      partially-eval-sant parents-of-scouts-sant
		      cons@ (lambda () '())))
	    (a1 (car split1))
	    (split2 (@ partially-eval-sant (cdr split1) cons@
		      (lambda () '())))
	    (a2 (car split2))
	    (split3 (@ partially-eval-sant (cdr split2) cons@
		      (lambda () '())))
	    (a3 (car split3))
	    )
      (map (lambda (subst)
             (concretize-subst/vars subst p1 p2))
	(list a1 a2 a3))))
  '(((p1.0 sam) (p2.0 rob)) ((p1.0 roz) (p2.0 sue)) ((p1.0 rob) (p2.0 sal))))


(define-syntax if/bc
  (syntax-rules ()
    [(_ #t conseq alt) conseq]
    [(_ #f conseq alt) alt]))

(define-syntax let-inject/everything
  (syntax-rules ()
    [(_ ([t ([var bool] ...) scheme-expression] ...) body ...)
     (lambda@ (sk fk subst)
       (@ (exists (t ...)
	    (all
	      (all!! (promise-one-answer
		       (== t (let ([var (let ([x (subst-in var subst)])
                                     (if/bc bool (nonvar! x) x))]
			      ...)
			  scheme-expression)))
		...)
	      body ...))
          sk fk subst))]))

(define-syntax let*-inject/everything
  (syntax-rules ()
    [(_ () body0 body1 ...) (all body0 body1 ...)]
    [(_ ([t0 ([var0 bool0] ...) scheme-expression0]
         [t1 ([var1 bool1] ...) scheme-expression1]
         ...)
       body0 body1 ...)
     (let-inject/everything ([t0 ([var0 bool0] ...) scheme-expression0])
       (let*-inject/everything ([t1 ([var1 bool1] ...) scheme-expression1] ...)
         body0 body1 ...))]))

(define-syntax let-inject
  (syntax-rules ()
    [(_ ([t (var ...) exp] ...) body ...)
     (let-inject/everything ([t ([var #t] ...) exp] ...) body ...)]))

(define-syntax let-inject/no-check
  (syntax-rules ()
    [(_ ([t (var ...) exp] ...) body ...)
     (let-inject/everything ([t ([var #f] ...) exp] ...) body ...)]))

(define-syntax let*-inject
  (syntax-rules ()
    [(_ ([t (var ...) exp] ...) body ...)
     (let*-inject/everything ([t ([var #t] ...) exp] ...) body ...)]))

(define-syntax let*-inject/no-check
  (syntax-rules ()
    [(_ ([t (var ...) exp] ...) body ...)
     (let*-inject/everything ([t ([var #f] ...) exp] ...) body ...)]))

(define-syntax predicate
  (syntax-rules ()
    [(_ (var ...) scheme-expression)
     (let-inject ([t (var ...) (not scheme-expression)])
       (== t #f))]))

(define-syntax predicate/no-check
  (syntax-rules ()
    [(_ (var ...) scheme-expression)
     (let*-inject/no-check ([t (var ...) (not scheme-expression)])
       (== t #f))]))

(define nonvar!
  (lambda (t)
    (if (var? t)
      (error 'nonvar! "Logic variable ~s found after substituting." (concretize t))
      t)))

(define grandpa
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all 
        (father grandad parent)
        (predicate (parent) (starts-with-r? parent))
        (father parent grandchild)))))

(define starts-with-r?
  (lambda (x)
    (and
      (symbol? x)
      (string=? (string (string-ref (symbol->string x) 0)) "r"))))

(test-check 'test-grandpa-11
  (solve 10 (x y) (grandpa x y))
  '(((x.0 sam) (y.0 sal)) ((x.0 sam) (y.0 pat))))

(define check
  (lambda (id f)
    (lambda term
      (if (not (procedure? f))
          (error id "Non-procedure found: ~s" f))
      (if (ormap var? term)
          (error id "Variable found: ~s" term))
      (apply f term))))

(test-check 'test-grandpa-12
  (solve 10 (x y) (grandpa x y))
  '(((x.0 sam) (y.0 sal)) ((x.0 sam) (y.0 pat))))

(define fun    
  (lambda (f)
    (fun-nocheck (check 'fun f))))

(define test1
  (lambda (x)
    (any (predicate () (< 4 5))
      (let-inject ([x^ () (< 6 7)])
        (== x x^)))))

;;;; Here is the definition of concretize.

(test-check 'test-test1
  (solution (x) (test1 x))
  '((x.0 x.0)))


(define test2
  (lambda (x)
    (any (predicate () (< 5 4))
      (let-inject ([x^ () (< 6 7)])
        (== x x^)))))

(test-check 'test-test2
  (solution (x) (test2 x))
  '((x.0 #t)))

(define test3
  (lambda (x y)
    (any
      (let-inject ([x^ () (< 5 4)])
        (== x x^))
      (let-inject ([y^ () (< 6 7)])
        (== y y^)))))

(test-check 'test-test3
  (solution (x y) (test3 x y))
  `((x.0 #f) (y.0 y.0)))

(define grandpa
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (fails (predicate (parent) (starts-with-r? parent)))
        (father parent grandchild)))))

(test-check 'test-grandpa-13
  (solve 10 (x y) (grandpa x y))
  '(((x.0 jon) (y.0 rob)) ((x.0 jon) (y.0 roz))))

(define instantiated
  (lambda (t)
    (predicate/no-check (t) (not (var? t)))))

(define view-subst
  (lambda (t)
    (lambda@ (sk fk subst)
      (pretty-print (subst-in t subst))
      (pretty-print (concretize-subst subst))
      (@ sk fk subst))))

(define grandpa
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (father parent grandchild)
        (view-subst grandchild)))))

(test-check 'test-grandpa-14/view-subst
  (solve 10 (x y) (grandpa x y))
  (begin
    'rob
    '((grandad.0 x.0)
      (grandchild.0 y.0)
      (x.0 jon)
      (parent.0 sam)
      (y.0 rob))
    'roz
    '((grandad.0 x.0)
      (grandchild.0 y.0)
      (x.0 jon)
      (parent.0 sam)
      (y.0 roz))
    'sal 
    '((grandad.0 x.0)
      (grandchild.0 y.0)
      (x.0 sam)
      (parent.0 rob)
      (y.0 sal))
    'pat
    '((grandad.0 x.0)
      (grandchild.0 y.0)
      (x.0 sam)
      (parent.0 rob)
      (y.0 pat))
    '(((x.0 jon) (y.0 rob))
      ((x.0 jon) (y.0 roz))
      ((x.0 sam) (y.0 sal))
      ((x.0 sam) (y.0 pat)))))

(define father
  (extend-relation (a1 a2) father
    (extend-relation (a1 a2) (fact () 'jon 'hal)
      (extend-relation (a1 a2) (fact () 'hal 'ted) (fact () 'sam 'jay)))))

(define ancestor
  (extend-relation (a1 a2)
    (relation (old young)
      (to-show old young)
      (father old young))
    (relation (old young)
      (to-show old young)
      (exists (not-so-old)
        (all (father old not-so-old) (ancestor not-so-old young))))))

(test-check 'test-ancestor
  (solve 21 (x) (ancestor 'jon x))
  '(((x.0 sam))
    ((x.0 hal))
    ((x.0 rob))
    ((x.0 roz))
    ((x.0 jay))
    ((x.0 sal))
    ((x.0 pat))
    ((x.0 ted))))

(define common-ancestor
  (relation (young-a young-b old)
    (to-show young-a young-b old)
    (all
      (ancestor old young-a)
      (ancestor old young-b))))

(test-check 'test-common-ancestor
  (solve 4 (x) (common-ancestor 'pat 'jay x))
  '(((x.0 jon)) ((x.0 sam))))

(define younger-common-ancestor
  (relation (young-a young-b old not-so-old)
    (to-show young-a young-b old not-so-old)
    (all
      (common-ancestor young-a young-b not-so-old)
      (common-ancestor young-a young-b old)
      (ancestor old not-so-old))))

(test-check 'test-younger-common-ancestor
  (solve 4 (x) (younger-common-ancestor 'pat 'jay 'jon x))
  '(((x.0 sam))))

(define youngest-common-ancestor
  (relation (young-a young-b not-so-old)
    (to-show young-a young-b not-so-old)
    (all
      (common-ancestor young-a young-b not-so-old)
      (exists (y)
        (fails (younger-common-ancestor young-a young-b not-so-old y))))))

(test-check 'test-youngest-common-ancestor
  (solve 4 (x) (youngest-common-ancestor 'pat 'jay x))
  '(((x.0 sam))))

(test-check 'test-Seres-Spivey
  (let ([father
	  (lambda (dad child)
	    (any
	      (all (== dad 'jon) (== child 'sam))
	      (all (== dad 'sam) (== child 'rob))
	      (all (== dad 'sam) (== child 'roz))
	      (all (== dad 'rob) (== child 'sal))
	      (all (== dad 'rob) (== child 'pat))
	      (all (== dad 'jon) (== child 'hal))
	      (all (== dad 'hal) (== child 'ted))
	      (all (== dad 'sam) (== child 'jay))))])
    (letrec
        ([ancestor
           (lambda (old young)
             (any
               (father old young)
               (exists (not-so-old)
                 (all
                   (father old not-so-old)
                   (ancestor not-so-old young)))))])
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
      ([move
         (extend-relation (a1 a2 a3 a4)
           (relation ()
             (to-show 0 _ _ _))
           (relation (n a b c)
             (to-show n a b c)
             (all
               (predicate (n) (positive? n))
               (let-inject ([m (n) (- n 1)])
                 (move m a c b)
                 (predicate (a b) (printf "Move a disk from ~s to ~s~n" a b))
                 (move m c b a)))))])
    (relation (n)
      (to-show n)
      (move n 'left 'middle 'right))))

(begin
  (printf "~s with 3 disks~n~n" 'test-towers-of-hanoi)
  (solution () (towers-of-hanoi 3))
  (void))

(define concretize-term
  (lambda (t env)
    (cond
      [(var? t) (concretize-var t env)]
      [(pair? t)
       (let-values (carct env) (concretize-term (car t) env)
         (let-values (cdrct env) (concretize-term (cdr t) env)
           (values (cons carct cdrct) env)))]
      [else (values t env)])))

(define relatively-ground?
  (lambda (term vars)
    (cond
      [(var? term) (not (memq term vars))]
      [(pair? term)
       (and (relatively-ground? (car term) vars)
            (relatively-ground? (cdr term) vars))]
      [else #t])))

(define subst-in
  (lambda (t subst)
    (cond
      [(var? t)
       (cond
         [(assq t subst) => commitment->term]
         [else t])]
      [(pair? t)
       (cons
         (subst-in (car t) subst)
         (subst-in (cdr t) subst))]
      [else t])))

(test-check 'test-compose-subst-5
  (let-lv (x y z)
    (equal?
      (let ([term `(p ,x ,y (g ,z))])
	(let ([s (compose-subst (unit-subst y z) (unit-subst x `(f ,y)))]
	      [r (compose-subst (unit-subst x 'a) (unit-subst z 'b))])
	  (let ([term1 (subst-in term s)])
	    (write term1)
	    (newline)
	    (let ([term2 (subst-in term1 r)])
	      (write term2)
	      (newline)
	      (let ([sr (compose-subst s r)])
		(write sr)
		(newline)
		(subst-in term sr))))))
      (begin
	`(p (f ,y) ,z (g ,z))
	`(p (f ,y) b (g b))
	`(,(commitment y 'b) ,(commitment x `(f ,y)) ,(commitment z 'b))
	`(p (f ,y) b (g b)))))
  #t)

(define unify*
  (lambda (t u)
    (cond
      [(trivially-equal? t u) empty-subst]
      [(var? t) (if (occurs? t u) #f (unit-subst t u))]
      [(var? u) (if (occurs? u t) #f (unit-subst u t))]
      [(and (pair? t) (pair? u))
       (cond
         [(unify* (car t) (car u)) =>
          (lambda (s-car)
            (cond
              [(unify* (subst-in (cdr t) s-car) (subst-in (cdr u) s-car))
               => (lambda (s-cdr)
                    (compose-subst s-car s-cdr))]
              [else #f]))]
         [else #f])]
      [else #f])))

(define occurs?
  (lambda (var term)
    (cond
      [(var? term) (eq? term var)]
      [(pair? term) (or (occurs? var (car term)) (occurs? var (cdr term)))]
      [else #f])))

(test-check 'test-unify/pairs
  (let-lv (w x y z u)
    (and
      (and
        (equal?
          (unify `(,x ,4) `(3 ,x) empty-subst)
          #f)
        (equal?
          (unify `(,x ,x) '(3 4) empty-subst)
          #f))
      (and
        (equal?
          (unify `(,x ,y) '(3 4) empty-subst)
          `(,(commitment x 3) ,(commitment y 4)))
        (equal?
          (unify `(,x 4) `(3 ,y) empty-subst)
          `(,(commitment x 3) ,(commitment y 4))))
      (and
        (equal?
          (unify `(,x 4 3 ,w) `(3 ,y ,x ,z) empty-subst)
          `(,(commitment x 3) ,(commitment y 4) ,(commitment w z)))
        (equal?
          (unify `(,x 4) `(,y ,y) empty-subst)
          `(,(commitment x 4) ,(commitment y 4)))
        (equal?
          (unify `(,x 4 3) `(,y ,y ,x) empty-subst)
          #f)
        (equal?
          (unify `(,w (,x (,y ,z) 8)) `(,w (,u (abc ,u) ,z)) empty-subst)
          `(,(commitment x 8)
            ,(commitment y 'abc)
            ,(commitment z 8)
            ,(commitment u 8)))
        (equal?
          (unify `(p (f a) (g ,x)) `(p ,x ,y) empty-subst)
          `(,(commitment x '(f a)) ,(commitment y '(g (f a)))))
        (equal?
          (unify `(p (g ,x) (f a)) `(p ,y ,x) empty-subst)
          `(,(commitment y '(g (f a))) ,(commitment x '(f a))))
        (equal?
          (unify `(p a ,x (h (g ,z))) `(p ,z (h ,y) (h ,y)) empty-subst)
          `(,(commitment z 'a)
            ,(commitment x '(h (g a)))
            ,(commitment y '(g a))))
        (equal? ;;; Oleg's succeeds on this.
          (unify `(p ,x ,x) `(p ,y (f ,y)) empty-subst)
          #f))))
  #t)

;Baader & Snyder
(test-check 'test-pathological
  (list
      (let-lv (x0 x1 y0 y1)
        (pretty-print
          (concretize-subst
            (unify
              `(h ,x1 (f ,y0 ,y0) ,y1)
              `(h (f ,x0 ,x0) ,y1 ,x1)
              empty-subst)))
        (newline))

      (let-lv (x0 x1 x2 y0 y1 y2)
        (pretty-print
          (concretize-subst
            (unify
              `(h ,x1 ,x2 (f ,y0 ,y0) (f ,y1 ,y1) ,y2)
              `(h (f ,x0 ,x0) (f ,x1 ,x1) ,y1 ,y2 ,x2)
              empty-subst)))
        (newline))

      (let-lv (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4)
        (pretty-print
          (concretize-subst
            (unify
              `(h ,x1 ,x2 ,x3 ,x4 (f ,y0 ,y0) (f ,y1 ,y1) (f ,y2 ,y2) (f ,y3 ,y3) ,y4)
              `(h (f ,x0 ,x0) (f ,x1 ,x1) (f ,x2 ,x2) (f ,x3 ,x3) ,y1 ,y2 ,y3 ,y4 ,x4)
              empty-subst)))))
  (list (void) (void) (void)))

(test-check 'test-fun-resubst
  (concretize
    (let ([j (relation (x w z)
	       (to-show z)
	       (let*-inject/no-check
                 ([x () 4]
                  [w () 3]
                  [z^ () (cons x w)])
                 (== z^ z)))])
      (solve 4 (q) (j q))))
  '(((q.0 (4 . 3)))))

(define towers-of-hanoi-path
  (let ([steps '()])
    (let ([push-step (lambda (x y) (set! steps (cons `(,x ,y) steps)))])
      (letrec
          ([move
             (extend-relation (a1 a2 a3 a4)
               (relation ()
                 (to-show 0 _ _ _))
               (relation (n a b c)
                 (to-show n a b c)
                 (all
                   (predicate (n) (positive? n))
                   (let-inject ([m (n) (- n 1)])
                     (move m a c b)
                     (predicate (a b) (push-step a b))
                     (move m c b a)))))])
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

(define unify
  (lambda (t u subst)
    (cond
      [(trivially-equal? t u) subst]
      [(var? t) (unify/var t (subst-in u subst) subst)]
      [(var? u) (unify/var u (subst-in t subst) subst)]
      [(and (pair? t) (pair? u))
       (cond
	 [(unify (car t) (car u) subst)
	  => (lambda (subst)
               (unify (cdr t) (cdr u) subst))]
	 [else #f])]
      [else #f])))

(define unify/var
  (lambda (t-var u subst)
    (cond
      [(assq t-var subst) (unify (subst-in t-var subst) u subst)] 
      [(occurs? t-var u) #f]
      [else (compose-subst subst (unit-subst t-var u))])))

(test-check 'test-unify/pairs-lazy
  (let-lv (w x y z u)
    (and
      (and
        (equal?
          (unify `(,x ,4) `(3 ,x) empty-subst)
          #f)
        (equal?
          (unify `(,x ,x) '(3 4) empty-subst)
          #f))
      (and
        (equal?
          (unify `(,x ,y) '(3 4) empty-subst)
          `(,(commitment x 3) ,(commitment y 4)))
        (equal?
          (unify `(,x 4) `(3 ,y) empty-subst)
          `(,(commitment x 3) ,(commitment y 4))))
      (and
        (equal?
          (unify `(,x 4 3 ,w) `(3 ,y ,x ,z) empty-subst)
          `(,(commitment x 3) ,(commitment y 4) ,(commitment w z)))
        (equal?
          (unify `(,x 4) `(,y ,y) empty-subst)
          `(,(commitment x 4) ,(commitment y 4)))
        (equal?
          (unify `(,x 4 3) `(,y ,y ,x) empty-subst)
          #f)
        (equal?            
          (unify `(,w (,x (,y ,z) 8)) `(,w (,u (abc ,u) ,z)) empty-subst)
          `(,(commitment x 8)
            ,(commitment y 'abc)
            ,(commitment z 8)
            ,(commitment u 8)))
        (equal?
          (unify `(p (f a) (g ,x)) `(p ,x ,y) empty-subst)
          `(,(commitment x '(f a)) ,(commitment y '(g (f a)))))
        (equal?
          (unify `(p (g ,x) (f a)) `(p ,y ,x) empty-subst)
          `(,(commitment y '(g (f a))) ,(commitment x '(f a))))
        (equal?
          (unify `(p a ,x (h (g ,z))) `(p ,z (h ,y) (h ,y)) empty-subst)            
          `(,(commitment z 'a)
            ,(commitment x '(h (g a)))
            ,(commitment y '(g a))))
        (equal? ;;; Oleg's succeeds on this.
          (unify `(p ,x ,x) `(p ,y (f ,y)) empty-subst)
          #f))))
  #t)

(test-check 'test-fun-resubst-lazy
  (concretize
    (let ([j (relation (x w z)
	       (to-show z)
	       (let*-inject/no-check
                 ([x () 4]
                  [w () 3]
                  [z^ () (cons x w)])
                 (== z z^)))])
      (solve 4 (q) (j q))))
  '(((q.0 (4 . 3)))))

(test-check 'test-pathological-lazy
  (list
      (let-lv (x0 x1 y0 y1)
        (pretty-print
          (concretize-subst
            (unify
              `(h ,x1 (f ,y0 ,y0) ,y1)
              `(h (f ,x0 ,x0) ,y1 ,x1)
              empty-subst)))
        (newline))

      (let-lv (x0 x1 x2 y0 y1 y2)
        (pretty-print
          (concretize-subst
            (unify
              `(h ,x1 ,x2 (f ,y0 ,y0) (f ,y1 ,y1) ,y2)
              `(h (f ,x0 ,x0) (f ,x1 ,x1) ,y1 ,y2 ,x2)
              empty-subst)))
        (newline))

      (let-lv (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4)
        (pretty-print
          (concretize-subst
            (unify
              `(h ,x1 ,x2 ,x3 ,x4 (f ,y0 ,y0) (f ,y1 ,y1) (f ,y2 ,y2) (f ,y3 ,y3) ,y4)
              `(h (f ,x0 ,x0) (f ,x1 ,x1) (f ,x2 ,x2) (f ,x3 ,x3) ,y1 ,y2 ,y3 ,y4 ,x4)
              empty-subst)))))
  (list (void) (void) (void)))

;;; ;-------------------------------------------------------
;;; This is the unifier of Oleg Kiselov
;;; These two definitions are for displaying purposes, only
;;; They have nothing to do with unification.

(define normalize-subst
  (lambda (subst)
    (map (lambda (c)
           (commitment (commitment->var c)
             (subst-vars-recursively (commitment->term c) subst)))
      subst)))

(define subst-vars-recursively
  (lambda (t subst)
    (cond
      [(var? t)
       (cond
         [(assq t subst) =>
          (lambda (c)
            (subst-vars-recursively
              (commitment->term c) (remq c subst)))]
         [else t])]
      [(pair? t)
       (cons
         (subst-vars-recursively (car t) subst)
         (subst-vars-recursively (cdr t) subst))]
      [else t])))

;;;; ------------------------------------------------------

;;;; This new subst-in is essential to Oleg's unifier.
(define subst-in
  (lambda (t subst)
    (cond
      [(var? t)
       (cond
         [(assq t subst)
	  => (lambda (c)
	       (subst-in (commitment->term c) subst))]
         [else t])]
      [(pair? t)
       (cons
         (subst-in (car t) subst)
         (subst-in (cdr t) subst))]
      [else t])))

;;;; This is Oleg's unifier

(define unify
  (lambda (t u subst)
    (cond
      [(eq? t u) subst]
      [(eq? t _) subst]
      [(eq? u _) subst]
      [(var? t) (if (var? u) (unify-var/var t u subst) (unify-var/value t u subst))]
      [(var? u) (unify-var/value u t subst)]
      [(and (pair? t) (pair? u))
       (cond
         [(unify (car t) (car u) subst)
          => (lambda (car-subst)
               (unify (cdr t) (cdr u) car-subst))]
         [else #f])]
      [else (and (equal? t u) subst)])))

(define unify-var/var
  (lambda (t-var u-var s)
    (cond
;       [(assq t-var s)
;        => (lambda (ct) ;;; This is bound/var
;             (let ([t-term (commitment->term ct)])
;               (unify u-var t-term s)))]
      
      [(assq t-var s)
       => (lambda (ct) ;;; This is bound/var
            (cond
              [(assq u-var s)
               => (lambda (cu)
                    (let ([u-term (commitment->term cu)]
                          [t-term (commitment->term ct)])
                      (unify t-term u-term s)))]
              [else ((unbound/bound u-var s) ct)]))]
;     [(assq u-var s) ;;; This is bound/unbound.
;      => (lambda (cu)
;           (let ([u-term (commitment->term cu)])
;             (compose-subst (unit-subst t-var u-term) s)))]
      [(assq u-var s) => (unbound/bound t-var s)]
      [else (extend-subst t-var u-var s)])))

(define unbound/bound
  (lambda (t-var s)
    (lambda (cu)
      (let loop ([cm cu])
        (let ([u-term (commitment->term cm)])
          (cond
            [(eq? u-term t-var) s]
            [(var? u-term)
             (cond
               [(assq u-term s) => loop]
               [else (unify-var/value t-var u-term s)])]
            [else (extend-subst t-var u-term s)]))))))
  
; ((and (pattern-var? tree2) (assq tree2 env)) => ; tree2 is a bound var
;        ; binding a free variable to a bound. Search for a substantial binding
;        ; or a loop. If we find a loop tree1->tree2->...->tree1
;        ; then we do not enter the binding to tree1, because tree1 is not
;        ; actually constrained.
;       (lambda (tree2-binding)
; 	(let loop ((binding tree2-binding))
; 	  (cond
; 	    ((eq? tree1 (cdr binding)) env)  ; loop: no binding needed
; 	    ((and (pattern-var? (cdr binding)) (assq (cdr binding) env))
; 	      => loop)
; 	    (else (cons (cons tree1 (cdr binding)) env))))))

;;; Don't add the commitment of an uncommited variable x to a pair (a . b)
; instead, add the commitment x = (var1 . var2) and
; unify var1 with a and var2 with b.

;;; Don't add the commitment of an uncommitted variable x to a pair (a . b)
; instead, add the commitment x = (var1 . var2) and
; unify var1 with a and var2 with b.
; However, if either 'a' or 'b' are atomic values (that is, do not contain
; variables), we can avoid introducing var1 or var2 and bind x
; to the correspondingly specvialized pair,
; Note, if either 'a' or 'b' are _, the current algorithm _effectively_
; replaces _ with a fresh variable. We do a lazy replacement.
; A neat accident!

(define ground?
  (lambda (t)
    (cond
      [(var? t) #f]
      [(pair? t) (and (ground? (car t)) (ground? (cdr t)))]
      [else #t])))

(define unify-var/value
  (lambda (t-var u-value subst)
    (cond
      [(assq t-var subst)
       => (lambda (ct)
            (unify (commitment->term ct) u-value subst))]
      [(ground? u-value) (extend-subst t-var u-value subst)]
      [(pair? u-value)
       (let ([car-val (car u-value)]
             [cdr-val (cdr u-value)])
         (cond
           [(ground? car-val)
            (cond
              [(ground? cdr-val)
               (extend-subst t-var (cons car-val cdr-val) subst)]
              [else (let ([d-var (var 'd*)])
                      (unify d-var cdr-val
                        (extend-subst t-var
                          (cons car-val d-var) subst)))])]
           [else
             (let ([a-var (var 'a*)]
		   [cdr-val (cdr u-value)])
               (cond
                 [(ground? cdr-val)
                  (unify a-var car-val
                    (extend-subst t-var (cons a-var cdr-val) subst))]
                 [else (let ([d-var (var 'd*)])
                         (cond
                           [(unify a-var car-val
                              (extend-subst t-var (cons a-var d-var) subst))
                            => (lambda (subst)
                                 (unify d-var cdr-val subst))]
                           [else #f]))]))]))]
      [else (extend-subst t-var u-value subst)])))
;------------------------------------------------------------------------
(test-check 'test-unify/pairs-oleg1
  (let-lv (x y)
    (unify `(,x ,4) `(3 ,x) empty-subst))
  #f)

(test-check 'test-unify/pairs-oleg2
  (let-lv (x y)
    (unify `(,x ,x) '(3 4) empty-subst))
  #f)

(let-lv (x y)
  (test-check 'test-unify/pairs-oleg3
    (unify `(,x ,y) '(3 4) empty-subst)
    `(,(commitment y 4) ,(commitment x 3))))

(let-lv (x y)
  (test-check 'test-unify/pairs-oleg4
    (unify `(,x 4) `(3 ,y) empty-subst)
    `(,(commitment y 4) ,(commitment x 3))))

(let-lv (x y w z)
  (test-check 'test-unify/pairs-oleg5
    (let ([s (normalize-subst
	       (unify `(,x 4 3 ,w) `(3 ,y ,x ,z) empty-subst))])
      (let ([vars (list w y x)])
	(map commitment
	  vars
	  (subst-vars-recursively vars s))))
    `(,(commitment w z)
       ,(commitment y 4)
       ,(commitment x 3))))

(let-lv (x y w z)
  (test-check 'test-unify/pairs-oleg6
    (let ([s (normalize-subst
	       (unify `(,x 4) `(,y ,y) empty-subst))])
      (let ([vars (list y x)])
	(map commitment
	  vars
	  (subst-vars-recursively vars s))))
    `(,(commitment y 4) ,(commitment x 4))))

(test-check 'test-unify/pairs-oleg7
  (let-lv (x y)
    (unify `(,x 4 3) `(,y ,y ,x) empty-subst))
    #f)

(let-lv (x y w z u)
  (test-check 'test-unify/pairs-oleg8
    (let ([s (normalize-subst
	       (unify
		 `(,w (,x (,y ,z) 8))
		 `(,w (,u (abc ,u) ,z))
		 empty-subst))])
      (let ([vars (list u z y x)])
	(map commitment
	  vars
	  (subst-vars-recursively vars s))))
    `(,(commitment u 8)
       ,(commitment z 8)
       ,(commitment y 'abc)
       ,(commitment x 8))))

(let-lv (x y w z u)
  (test-check 'test-unify/pairs-oleg8
    (let ([s (normalize-subst
	       (unify `(p (f a) (g ,x)) `(p ,x ,y) empty-subst))])
      (let ([vars (list y x)])
	(map commitment
	  vars
	  (subst-vars-recursively vars s))))
    `(,(commitment y '(g (f a)))
       ,(commitment x '(f a)))))

(let-lv (x y w z u)
  (test-check 'test-unify/pairs-oleg10
    (let ([s (normalize-subst
	       (unify `(p (g ,x) (f a)) `(p ,y ,x) empty-subst))])
      (let ([vars (list x y)])
	(map commitment
	  vars
	  (subst-vars-recursively vars s))))
    `(,(commitment x '(f a))
       ,(commitment y '(g (f a))))))

(let-lv (x y w z u)
  (test-check 'test-unify/pairs-oleg11
    (let ([s (normalize-subst
	       (unify
		 `(p a ,x (h (g ,z)))
		 `(p ,z (h ,y) (h ,y))
		 empty-subst))])
      (let ([vars (list y x z)])
	(map commitment
	  vars
	  (subst-vars-recursively vars s))))
    `(,(commitment y '(g a))
       ,(commitment x '(h (g a)))
       ,(commitment z 'a))))

; (let-lv (x y w z u)
;   (test-check 'test-unify/pairs-oleg12
;     (concretize-subst ;;; was #f
;       (let ([s (unify `(p ,x ,x) `(p ,y (f ,y)) empty-subst)])
; 	(let ([var (map commitment->var s)])
; 	  (map commitment
; 	    var
; 	    (subst-vars-recursively var s)))))
;     `(;,(commitment '*d.0 '())
;        ,(commitment '*a.0 '(f *a.0))
;        ;,(commitment '*d.1 '((f . *d.1)))
;        ,(commitment '*d.0 '((f . *d.0)))
;        ;,(commitment '*a.1 'f)
;        ;,(commitment 'y.0  '(f (f . *d.1)))
;        ,(commitment 'y.0  '(f (f . *d.0)))
;        ,(commitment 'x.0  '(f (f . *d.0))))))

; (let-lv (x y w z u)
;   (test-check 'test-unify/pairs-oleg13
;     (concretize-subst ;;; was #f
;       (let ([s (unify `(p ,x ,x) `(p ,y (f ,y)) empty-subst)])
; 	(let ([var (map commitment->var s)])
; 	  (map commitment
; 	    var
; 	    (subst-vars-recursively var s)))))
;     `(;,(commitment '*d.0 '())
;        ,(commitment '*a.0 '(f *a.0))
;        ;,(commitment '*d.1 '((f . *d.1)))
;        ,(commitment '*d.0 '((f . *d.0)))
;        ;,(commitment '*a.1 'f)
;        ;,(commitment 'y.0  '(f (f . *d.1)))
;        ,(commitment 'y.0  '(f (f . *d.0)))
;        ,(commitment 'x.0  '(f (f . *d.0))))))

(test-check 'test-fun-resubst-oleg
  (concretize
    (let ([j (relation (x w z)
	       (to-show z)
	       (let*-inject/no-check
                 ([x () 4]
                  [w () 3]
                  [z^ () (cons x w)])
                 (== z z^)))])
      (solve 4 (q) (j q))))
  '(((q.0 (4 . 3)))))
          
;Baader & Snyder
(test-check 'test-pathological-oleg
  (list
    (let-lv (x0 x1 y0 y1)
      (pretty-print
	(concretize-subst
	  (let ([s (unify
		     `(h ,x1 (f ,y0 ,y0) ,y1)
		     `(h (f ,x0 ,x0) ,y1 ,x1)
		     empty-subst)])
	    (let ([vars (map commitment->var s)])
	      (map commitment
		vars
		(subst-vars-recursively vars s))))))
      (newline))

    (let-lv (x0 x1 x2 y0 y1 y2)
      (pretty-print
	(concretize-subst
	  (let ([s (unify
		     `(h ,x1 ,x2 (f ,y0 ,y0) (f ,y1 ,y1) ,y2)
		     `(h (f ,x0 ,x0) (f ,x1 ,x1) ,y1 ,y2 ,x2)
		     empty-subst)])
	    (let ([vars (map commitment->var s)])
	      (map commitment
		vars
		(subst-vars-recursively vars s))))))
      (newline))

    (let-lv (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4)
      (pretty-print
	(concretize-subst
	  (let ([s (unify
		     `(h ,x1 ,x2 ,x3 ,x4 (f ,y0 ,y0) (f ,y1 ,y1)
			(f ,y2 ,y2) (f ,y3 ,y3) ,y4)
		     `(h (f ,x0 ,x0) (f ,x1 ,x1) (f ,x2 ,x2)
			(f ,x3 ,x3) ,y1 ,y2 ,y3 ,y4 ,x4)
		     empty-subst)])
	    (let ([vars (map commitment->var s)])
	      (map commitment
		vars
		(subst-vars-recursively vars s))))))))
  (list (void) (void) (void)))

(define concat
  (lambda (xs ys)
    (cond
      [(null? xs) ys]
      [else (cons (car xs) (concat (cdr xs) ys))])))

(test-check 'test-concat-as-function
  (concat '(a b c) '(u v))
  '(a b c u v))

(test-check 'test-fun-concat
  (solve 1 (q)
    (let-inject ([t () (concat '(a b c) '(u v))])
      (== q t)))
  '(((q.0 (a b c u v)))))

(define concat
  (extend-relation (a1 a2 a3)
    (fact (xs) '() xs xs)
    (relation (x xs ys zs)
      (to-show `(,x . ,xs) ys `(,x . ,zs))
      (concat xs ys zs))))

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
        '(((q.0 ()) (r.0 xs.0) (s.0 xs.0))
          ((q.0 (x.0)) (r.0 xs.0) (s.0 (x.0 . xs.0)))
          ((q.0 (x.0 x.1)) (r.0 xs.0) (s.0 (x.0 x.1 . xs.0)))
          ((q.0 (x.0 x.1 x.2)) (r.0 xs.0) (s.0 (x.0 x.1 x.2 . xs.0)))
          ((q.0 (x.0 x.1 x.2 x.3))
           (r.0 xs.0)
           (s.0 (x.0 x.1 x.2 x.3 . xs.0)))
          ((q.0 (x.0 x.1 x.2 x.3 x.4))
           (r.0 xs.0)
           (s.0 (x.0 x.1 x.2 x.3 x.4 . xs.0)))))
      (equal?
        (solve 6 (q r) (concat q '(u v) `(a b c . ,r)))
        '(((q.0 (a b c)) (r.0 (u v)))
          ((q.0 (a b c x.0)) (r.0 (x.0 u v)))
          ((q.0 (a b c x.0 x.1)) (r.0 (x.0 x.1 u v)))
          ((q.0 (a b c x.0 x.1 x.2)) (r.0 (x.0 x.1 x.2 u v)))
          ((q.0 (a b c x.0 x.1 x.2 x.3)) (r.0 (x.0 x.1 x.2 x.3 u v)))
          ((q.0 (a b c x.0 x.1 x.2 x.3 x.4))
           (r.0 (x.0 x.1 x.2 x.3 x.4 u v)))))
      (equal?
        (solve 6 (q) (concat q '() q))
        '(((q.0 ()))
          ((q.0 (x.0)))
          ((q.0 (x.0 x.1)))
          ((q.0 (x.0 x.1 x.2)))
          ((q.0 (x.0 x.1 x.2 x.3)))
          ((q.0 (x.0 x.1 x.2 x.3 x.4)))))))
  #t)


;;;; Types from here on out.

(define parse
  (lambda (e)
    (cond
      [(symbol? e) `(var ,e)]
      [(number? e) `(intc ,e)]
      [(boolean? e) `(boolc ,e)]
      [else (case (car e)
              [(zero?) `(zero? ,(parse (cadr e)))]
              [(sub1) `(sub1 ,(parse (cadr e)))]
              [(+) `(+ ,(parse (cadr e)) ,(parse (caddr e)))]
              [(if) `(if ,(parse (cadr e)) ,(parse (caddr e)) ,(parse (cadddr e)))]
              [(fix) `(fix ,(parse (cadr e)))]
              [(lambda) `(lambda ,(cadr e) ,(parse (caddr e)))]
              [(let) `(let ([,(car (car (cadr e))) ,(parse (cadr (car (cadr e))))])
                        ,(parse (caddr e)))]
              [else `(app ,(parse (car e)) ,(parse (cadr e)))])])))

(define unparse
  (lambda (e)
    (case (car e)
      [(var) (cadr e)]
      [(intc) (cadr e)]
      [(boolc) (cadr e)]
      [(zero?) `(zero? ,(unparse (cadr e)))]
      [(sub1) `(sub1 ,(unparse (cadr e)))]
      [(+) `(+ ,(unparse (cadr e)) ,(unparse (caddr e)))]
      [(if) `(if ,(unparse (cadr e)) ,(unparse (caddr e)) ,(unparse (cadddr e)))]
      [(fix) `(fix ,(unparse (cadr e)))]
      [(lambda) `(lambda (,(car (cadr e))) ,(unparse (caddr e)))]
      [(let) 
       `(let ([,(car (car (cadr e)))
               ,(unparse (cadr (car (cadr e))))])
          ,(unparse (caddr e)))]
      [(app) `(,(unparse (cadr e)) ,(unparse (caddr e)))])))

(define-syntax infer-type
  (syntax-rules ()
    [(_ g term type)
     (cond
       [(solution (g type) (!- g (parse term) type))
        => (lambda (result)
             `(!- ,(cadr (car result)) ,term ,(cadr (cadr result))))]
       [else #f])]))

;;; This is environments.

(define non-generic-match-env
  (fact (g v t) `(non-generic ,v ,t ,g) v t))

(define non-generic-recursive-env
  (relation (g v t)
    (to-show `(non-generic ,_ ,_ ,g) v t)
    (all!! (instantiated g) (env g v t))))

(define env (extend-relation (a1 a2 a3)
              non-generic-match-env non-generic-recursive-env))

(define fix  ;;; this is so that students can see what happens
  (lambda (e)
    (e (lambda (z) ((fix e) z)))))

(define generic-base-env
  (relation (g v targ tresult t)
    (to-show `(generic ,v (--> ,targ ,tresult) ,g) v t)
    (let-inject/no-check ([t^ (targ tresult) (instantiate `(--> ,targ ,tresult))])
      (== t t^))))

(define generic-recursive-env
  (relation (g v t)
    (to-show `(generic ,_ ,_ ,g) v t)
    (all! (env g v t))))

(define generic-env
  (extend-relation (a1 a2 a3) generic-base-env generic-recursive-env))

(define instantiate
  (letrec
      ([instantiate-term
         (lambda (t env)
           (cond
             [(var? t)
              (cond
                [(assq t env)
                 => (lambda (pr)
                      (values (cdr pr) env))]
                [else (let ([new-var (var (var-id t))])
                        (values new-var (cons `(,t . ,new-var) env)))])]
             [(pair? t)
              (let-values (a-t env) (instantiate-term (car t) env)
                (let-values (d-t env) (instantiate-term (cdr t) env)
                  (values (cons a-t d-t) env)))]
             [else (values t env)]))])
    (lambda (t)
      (let-values (ct env) (instantiate-term t '())
        ct))))

(define env (extend-relation (a1 a2 a3) env generic-env))

;;;; This starts the rules

(define int 'int)
(define bool 'bool)

(define var-rel
  (relation (g v t)
    (to-show g `(var ,v) t)
    (all! (env g v t))))

(define int-rel
  (fact (g x) g `(intc ,x) int))

(define bool-rel
  (fact (g x) g `(boolc ,x) bool))

(define zero?-rel
  (relation (g x)
    (to-show g `(zero? ,x) bool)
    (all! (!- g x int))))

(define sub1-rel
  (relation (g x)
    (to-show g `(sub1 ,x) int)
    (all! (!- g x int))))

(define +-rel
  (relation (g x y)
    (to-show g `(+ ,x ,y) int)
    (all!! (!- g x int) (!- g y int))))

(define if-rel
  (relation (g t test conseq alt)
    (to-show g `(if ,test ,conseq ,alt) t)
    (all!! (!- g test bool) (!- g conseq t) (!- g alt t))))

(define lambda-rel
  (relation (g v t body type-v)
    (to-show g `(lambda (,v) ,body) `(--> ,type-v ,t))
    (all! (!- `(non-generic ,v ,type-v ,g) body t))))

(define app-rel
  (relation (g t rand rator)
    (to-show g `(app ,rator ,rand) t)
    (let-lv (t-rand)
      (all!! (!- g rator `(--> ,t-rand ,t)) (!- g rand t-rand)))))

(define fix-rel
  (relation (g rand t)
    (to-show g `(fix ,rand) t)
    (all! (!- g rand `(--> ,t ,t)))))

(define polylet-rel
  (relation (g v rand body t)
    (to-show g `(let ([,v ,rand]) ,body) t)
    (let-lv (t-rand)
      (all!!
        (!- g rand t-rand)
        (!- `(generic ,v ,t-rand ,g) body t)))))

(define !-
  (extend-relation (a1 a2 a3)
    var-rel int-rel bool-rel zero?-rel sub1-rel +-rel 
    if-rel lambda-rel app-rel fix-rel polylet-rel))

(test-check 'test-!-1
  (and
    (equal?
      (solution () (exists (g) (!- g '(intc 17) int)))
      '())
    (equal?
      (solution (?) (exists (g) (!- g '(intc 17) ?)))
      '((?.0 int))))
  #t)

(test-check 'arithmetic-primitives
  (solution (?) (exists (g)  (!- g '(zero? (intc 24)) ?)))
  '((?.0 bool)))

(test-check 'test-!-sub1
  (solution (?) (exists (g) (!- g '(zero? (sub1 (intc 24))) ?)))
  '((?.0 bool)))

(test-check 'test-!-+
  (solution (?)
    (exists (g)
      (!- g '(zero? (sub1 (+ (intc 18) (+ (intc 24) (intc 50))))) ?)))
  '((?.0 bool)))

(test-check 'test-!-2
  (and
    (equal?
      (solution (?) (exists (g) (!- g '(zero? (intc 24)) ?)))
      '((?.0 bool)))
    (equal?
      (solution (?) (exists (g) (!- g '(zero? (+ (intc 24) (intc 50))) ?)))
      '((?.0 bool)))
    (equal?
      (solution (?)
        (exists (g)
          (!- g '(zero? (sub1 (+ (intc 18) (+ (intc 24) (intc 50))))) ?)))
      '((?.0 bool))))
  #t)

(test-check 'test-!-3
  (solution (?) (!- '() '(if (zero? (intc 24)) (intc 3) (intc 4)) ?))
  '((?.0 int)))

(test-check 'if-expressions
  (solution (?)
    (exists (g) (!- g '(if (zero? (intc 24)) (zero? (intc 3)) (zero? (intc 4))) ?)))
  '((?.0 bool)))

(test-check 'variables
  (and
    (equal?
      (solution (?)
        (exists (g)
          (env `(non-generic b int (non-generic a bool ,g)) 'a ?)))
      '((?.0 bool)))
    (equal?
      (solution (?)
        (exists (g)
          (!- `(non-generic a int ,g) '(zero? (var a)) ?)))
      '((?.0 bool)))
    (equal?
      (solution (?)
        (exists (g)
          (!- `(non-generic b bool (non-generic a int ,g))
            '(zero? (var a))
            ?)))
      '((?.0 bool))))
  #t)

(test-check 'variables-4a
  (solution (?)
    (exists (g)
      (!- `(non-generic b bool (non-generic a int ,g))
        '(lambda (x) (+ (var x) (intc 5)))
        ?)))
  '((?.0 (--> int int))))

(test-check 'variables-4b
  (solution (?)
    (exists (g)
      (!- `(non-generic b bool (non-generic a int ,g))
        '(lambda (x) (+ (var x) (var a)))
        ?)))
  '((?.0 (--> int int))))

(test-check 'variables-4c
  (solution (?)
    (exists (g) 
      (!- g '(lambda (a) (lambda (x) (+ (var x) (var a)))) ?)))
  '((?.0 (--> int (--> int int)))))

(test-check 'everything-but-polymorphic-let
  (solution (?)
    (exists (g)
      (!- g (parse
              '(lambda (f)
                 (lambda (x)
                   ((f x) x))))
        ?)))
  '((?.0 (-->
           (--> type-v.0 (--> type-v.0 t.0))
           (--> type-v.0 t.0)))))

(test-check 'everything-but-polymorphic-let
  (solution (?)
    (exists (g)
      (!- g
        (parse
          '((fix (lambda (sum)
                   (lambda (n)
                     (if (zero? n)
                         0
                         (+ n (sum (sub1 n)))))))
            10))
        ?)))
  '((?.0 int)))

(test-check 'everything-but-polymorphic-let
  (solution (?)
    (exists (g)
      (!- g
        (parse
          '((fix (lambda (sum)
                   (lambda (n)
                     (+ n (sum (sub1 n))))))
            10))
        ?)))
  '((?.0 int)))

(test-check 'everything-but-polymorphic-let
  (solution (?)
    (exists (g)
      (!- g
        (parse '((lambda (f)
                   (if (f (zero? 5))
                       (+ (f 4) 8)
                       (+ (f 3) 7)))
                 (lambda (x) x)))
        ?)))
  #f)

(test-check 'polymorphic-let
  (solution (?)
    (exists (g)
      (!- g
        (parse
          '(let ([f (lambda (x) x)])
             (if (f (zero? 5))
                 (+ (f 4) 8)
                 (+ (f 3) 7))))
        ?)))
  '((?.0 int)))

(test-check 'with-robust-syntax
  (solution (?)
    (exists (g)
      (!- g
        '(app
           (fix
             (lambda (sum)
               (lambda (n)
                 (if (if (zero? (var n)) (boolc #t) (boolc #f))
                     (intc 0)
                     (+ (var n) (app (var sum) (sub1 (var n))))))))
           (intc 10))
        ?)))
  '((?.0 int)))

(test-check 'with-robust-syntax-but-long-jumps/poly-let
  (solution (?)
    (exists (g)
      (!- g
        '(let ([f (lambda (x) (var x))])
           (if (app (var f) (zero? (intc 5)))
               (+ (app (var f) (intc 4)) (intc 8))
               (+ (app (var f) (intc 3)) (intc 7))))
        ?)))
  '((?.0 int)))

(test-check 'type-habitation
  (and
    (equal?
      (solution (g ?)
        (!- g ? '(--> int int)))
      '((g.0 (non-generic v.0 (--> int int) g.1)) (?.0 (var v.0))))
    (equal?
      (solution (la f b)
        (exists (g)
          (!- g `(,la (,f) ,b) '(--> int int))))
      '((la.0 lambda) (f.0 v.0) (b.0 (var v.0))))
    (equal?
      (solution (g h r q z y t)
        (!- g `(,h ,r (,q ,z ,y)) t))
      '((g.0 (non-generic v.0 int g.1))
        (h.0 +)
        (r.0 (var v.0))
        (q.0 +)
        (z.0 (var v.0))
        (y.0 (var v.0))
        (t.0 int)))
    (equal?
      (solution (h r q z y t u v)
        (exists (g)
          (!- g `(,h ,r (,q ,z ,y)) `(,t ,u ,v))))
      '((h.0 lambda)
        (r.0 (v.0))
        (q.0 +)
        (z.0 (var v.0))
        (y.0 (var v.0))
        (t.0 -->)
        (u.0 int)
        (v.1 int))))
  #t)

;;; long cuts
;;; No cuts are needed any more
; (define !-generator
;   (lambda (long-cut)
;     (letrec
;       ([!- (extend-relation (a1 a2 a3)
;              (relation (g v t)
;                (to-show g `(var ,v) t)
;                (all long-cut (env g v t)))
;              (fact (g x) g `(intc ,x) int)
;              (fact (g x) g `(boolc ,x) bool)
;              (relation (g x)
;                (to-show g `(zero? ,x) bool)
;                (all long-cut (!- g x int)))
;              (relation (g x)
;                (to-show g `(sub1 ,x) int)
;                (all long-cut (!- g x int)))
;              (relation (g x y)
;                (to-show g `(+ ,x ,y) int)
;                (all long-cut (all! (!- g x int) (!- g y int))))
;              (relation (g t test conseq alt)
;                (to-show g `(if ,test ,conseq ,alt) t)
;                (all long-cut
; 		 (all! (!- g test bool) (!- g conseq t) (!- g alt t))))
;              (relation (g v t body type-v)
;                (to-show g `(lambda (,v) ,body) `(--> ,type-v ,t))
;                (all long-cut (!- `(non-generic ,v ,type-v ,g) body t)))
;              (relation (g t rand rator)
;                (to-show g `(app ,rator ,rand) t)
;                (exists (t-rand)
;                  (all long-cut
; 		   (all!
;                      (!- g rator `(--> ,t-rand ,t))
;                      (!- g rand t-rand)))))
;              (relation (g rand t)
;                (to-show g `(fix ,rand) t)
;                (all long-cut (!- g rand `(--> ,t ,t))))
;              (relation (g v rand body t)
;                (to-show g `(let ([,v ,rand]) ,body) t)
;                (exists (t-rand)
;                  (all long-cut
; 		   (all!
;                      (!- g rand t-rand)
;                      (!- `(generic ,v ,t-rand ,g) body t))))))])
;       !-)))
;
; (define !-
;   (relation/cut cut (g exp t)
;     (to-show g exp t)
;     ((!-generator cut) g exp t)))


; (relation-cond vars clause ...)
; clause::= ((local-var...) (condition ...) (conseq ...))

(define-syntax relation-cond
  (syntax-rules ()
    ((_ (global-var ...) clause0 clause1 ...)
      (lambda (global-var ...)
	(lambda@ (sk fk subst)
	  (relation-cond-clause (sk fk subst)
	    clause0 clause1 ...))))))

(define-syntax relation-cond-clause
  (syntax-rules ()
    ((_ (sk fk subst)) (fk)) ; no more choices: fail
    ((_ (sk fk subst) 
       (local-vars (condition ...) conseq)
       clause ...)
      (let-lv local-vars			; a bit sloppy, need exists...
	(printf "running ~a~n" '(condition ...))
	(@ (all!! condition ...)
	; sk
	  (lambda@ (fk-ign)
	    (@ conseq sk fk))
	; fk
	  (lambda () (relation-cond-clause (sk fk subst) clause ...))
	  subst)))))


; (define !-
;     (letrec
;       ([!- (extend-relation (a1 a2 a3)
;              (relation (g v t)
;                (to-show g `(var ,v) t)
;                (all long-cut (env g v t)))
;              (fact (g x) g `(intc ,x) int)
;              (fact (g x) g `(boolc ,x) bool)
;              (relation (g x)
;                (to-show g `(zero? ,x) bool)
;                (all long-cut (!- g x int)))
;              (relation (g x)
;                (to-show g `(sub1 ,x) int)
;                (all long-cut (!- g x int)))
;              (relation (g x y)
;                (to-show g `(+ ,x ,y) int)
;                (all long-cut (all! (!- g x int) (!- g y int))))
;              (relation (g t test conseq alt)
;                (to-show g `(if ,test ,conseq ,alt) t)
;                (all long-cut
; 		 (all! (!- g test bool) (!- g conseq t) (!- g alt t))))
;              (relation (g v t body type-v)
;                (to-show g `(lambda (,v) ,body) `(--> ,type-v ,t))
;                (all long-cut (!- `(non-generic ,v ,type-v ,g) body t)))
;              (relation (g t rand rator)
;                (to-show g `(app ,rator ,rand) t)
;                (exists (t-rand)
;                  (all long-cut
; 		   (all!
;                      (!- g rator `(--> ,t-rand ,t))
;                      (!- g rand t-rand)))))
;              (relation (g rand t)
;                (to-show g `(fix ,rand) t)
;                (all long-cut (!- g rand `(--> ,t ,t))))
;              (relation (g v rand body t)
;                (to-show g `(let ([,v ,rand]) ,body) t)
;                (exists (t-rand)
;                  (all long-cut
; 		   (all!
;                      (!- g rand t-rand)
;                      (!- `(generic ,v ,t-rand ,g) body t))))))])
;       !-)))

(define !-
  (relation-cond (g exp t)
    ((v) ((== exp `(var ,v)))
      (env g v t))
    (() ((== exp `(intc ,_)) (== t int)) succeed)
    (() ((== exp `(boolc ,_)) (== t bool)) succeed)
    ((x) ((== exp `(zero? ,x)) (== t bool))
      (!- g x int))
    ((x) ((== exp `(sub1 ,x)) (== t int))
      (!- g x int))
    ((x y) ((== exp `(+ ,x ,y)) (== t int))
      (all!! (!- g x int) (!- g y int)))
    ((test conseq alt) ((== exp `(if ,test ,conseq ,alt)))
      (all!! (!- g test bool) (!- g conseq t) (!- g alt t)))
    ((body type-v v t1) ((== exp `(lambda (,v) ,body)) 
			 (== t `(--> ,type-v ,t1)))
      (!- `(non-generic ,v ,type-v ,g) body t1))
    ((rand rator) ((== exp `(app ,rator ,rand)))
      (exists (t-rand)
	(all!!
	  (!- g rator `(--> ,t-rand ,t))
	  (!- g rand t-rand))))
    ((rand) ((== exp `(fix ,rand)))
      (!- g rand `(--> ,t ,t)))
    ((v rand body) ((== exp `(let ([,v ,rand]) ,body)))
      (exists (t-rand)
	(all!!
	  (!- g rand t-rand)
	  (!- `(generic ,v ,t-rand ,g) body t))))))

'(define !-
  (relation-cond (g exp t)
    ((v) ((== exp `(var ,v)))
      succeed)))

(pretty-print (expand '(relation-cond (g exp t)
    ((v) ((== exp `(var ,v)))
      succeed))))

(test-check 'with-robust-syntax-but-long-jumps/poly-let
  (solution (?)
    (exists (g)
      (!- g
        '(let ([f (lambda (x) (var x))])
           (if (app (var f) (zero? (intc 5)))
               (+ (app (var f) (intc 4)) (intc 8))
               (+ (app (var f) (intc 3)) (intc 7))))
        ?)))
  '((?.0 int)))


(define invertible-binary-function->ternary-relation
  (lambda (op inverted-op)
    (extend-relation (a1 a2 a3)
      (relation (x y z)
        (to-show x y z)
        (all (fails (instantiated z))
          (let-inject ([z^ (x y) (op x y)])
            (== z z^))))
      (relation (x y z)
        (to-show x y z)
        (all (fails (instantiated y))
          (let-inject ([y^ (z x) (inverted-op z x)])
            (== y y^))))
      (relation (x y z)
        (to-show x y z)
        (all (fails (instantiated x))
          (let-inject ([x^ (z y) (inverted-op z y)])
            (== x x^))))
      (relation (x y z)
        (to-show x y z)
        (let-inject ([z^ (x y) (op x y)])
          (== z z^))))))

(define ++ (invertible-binary-function->ternary-relation + -))
(define -- (invertible-binary-function->ternary-relation - +))
(define ** (invertible-binary-function->ternary-relation * /))
(define // (invertible-binary-function->ternary-relation / *))

(test-check 'test-instantiated-1
  (and
    (equal?
      (solution (x) (++ x 16.0 8))
      '((x.0 -8.0)))
    (equal?
      (solution (x) (++ 10 16.0 x))
      '((x.0 26.0)))
    (equal?
      (solution (x) (-- 10 x 3))
      '((x.0 13))))
  #t)

(define symbol->lnum
  (lambda (sym)
    (map char->integer (string->list (symbol->string sym)))))

(define lnum->symbol
  (lambda (lnums)
    (string->symbol (list->string (map integer->char lnums)))))

(define invertible-unary-function->binary-relation
  (lambda (op inverted-op)
    (extend-relation (a1 a2)
      (relation (x y)
        (to-show x y)
        (all (fails (instantiated y))
          (let-inject ([y^ (x) (op x)])
            (== y y^))))
      (relation (x y)
        (to-show x y)
        (all (fails (instantiated x))
          (let-inject ([x^ (y) (inverted-op y)])
            (== x x^))))
      (relation (x y)
        (to-show x y)
        (begin
          (pretty-print "Third rule")
          (let-inject ([y^ (x) (op x)])
            (== y y^)))))))

(define name
  (invertible-unary-function->binary-relation symbol->lnum lnum->symbol))

(test-check 'test-instantiated-2
  (and
    (equal?
      (solution (x) (name 'sleep x))
      '((x.0 (115 108 101 101 112))))
    (equal?
      (solution (x) (name x '(115 108 101 101 112)))
      '((x.0 sleep))))
  #t)

;;;; *****************************************************************
;;;; This is the start of a different perspective on logic programming.
;;;; Unitl I saw (!! fk), it was not possible to do the things that I
;;;; wanted to do.  This does obviate the need for unify-sequence, so
;;;; that is good.

(define father
  (lambda (dad child)
    (all!!
      (== dad 'jon)
      (== child 'sam))))

(define father
  (extend-relation (a1 a2) father
    (lambda (dad child)
      (all!! 
	(== dad 'sam)
	(== child 'rob)))))

(define father
  (extend-relation (a1 a2) father
    (lambda (dad child)
      (all!!
	(== dad 'rob)
	(== child 'sal)))))

(define grandpa
  (lambda (grandfather child)
    (exists (x)
      (all (father grandfather x) (father x child)))))

(test-check 'grandpa-ng
  (solve 5 (x y) (grandpa x y))
  '(((x.0 jon) (y.0 rob)) ((x.0 sam) (y.0 sal))))

(define father-rob-sal (fact () 'rob 'sal))
(define father-sam-rob (fact () 'sam 'rob))
(define father-jon-sam (fact () 'jon 'sam))
(define father
  (extend-relation (a1 a2) father-jon-sam father-sam-rob father-rob-sal))

(test-check 'grandpa-ng-1
  (solve 5 (x y) (grandpa x y))
  '(((x.0 jon) (y.0 rob)) ((x.0 sam) (y.0 sal))))

(test-check 'grandpa-ng-2
  (solve 5 (y) (grandpa 'sam y))
  '(((y.0 sal))))

(test-check 'grandpa-ng-2
  (solve 5 (x) (grandpa x 'sal))
  '(((x.0 sam))))

; No need for the following any more...
; (define grandpa-sam
;   (lambda (child)
;     (lambda@ (sk fk subst)
;       (let ([next (!! fk)]
;             [cut (!! cutk)])
;         (let-lv (grandfather)
;           (@ (all
;                (all next (== grandfather 'sam))
;                cut
;                (exists (x)
;                  (all (father grandfather x) (father x child))))
;              sk fk subst ))))))

(define grandpa-sam
  (lambda (child)
    (exists (grandfather)
      (if-only (== grandfather 'sam)
	(exists (x)
	  (all (father grandfather x) (father x child)))))))

(test-check 'grandpa-sam-1
  (solve 5 () (grandpa-sam 'sal))
  '(()))

(define grandpa-sam
  (relation (child)
    (to-show child)
    (exists (x)
      (all (father 'sam x) (father x child)))))

(test-check 'grandpa-sam-2
  (solve 5 () (grandpa-sam 'sal))
  '(()))

(define father-rob-sal (fact () 'rob 'sal))
(define father-sam-rob (fact () 'sam 'rob))
(define father-jon-sam (fact () 'jon 'sam))
(define father 
  (extend-relation (a1 a2) father-jon-sam father-sam-rob father-rob-sal))

(test-check 'grandpa-sam-3
  (solve 5 () (grandpa-sam 'sal))
  '(()))

(define father-rob-sal
  (relation () (to-show 'rob 'sal)))

(define father-sam-rob
  (relation () (to-show 'sam 'rob)))

(define father-johh-sam
  (relation () (to-show 'jon 'sam)))

(define father 
  (extend-relation (a1 a2) father-jon-sam father-sam-rob father-rob-sal))

(test-check 'grandpa-sam-4
  (solve 5 () (grandpa-sam 'sal))
  '(()))

;;;; This verifies that the idea works.  Now, to run the book through this
;;;; system.

; Extending relations in truly mathematical sense.
; First, why do we need this.

(define fact1 (fact () 'x1 'y1))
(define fact2 (fact () 'x2 'y2))
(define fact3 (fact () 'x3 'y3))
(define fact4 (fact () 'x4 'y4))

; R1 and R2 are overlapping
(define R1 (extend-relation (a1 a2) fact1 fact2))
(define R2 (extend-relation (a1 a2) fact1 fact3)) 

(printf "~%R1:~%")
(pretty-print (solve 10 (x y) (R1 x y)))
(printf "~%R2:~%")
(pretty-print (solve 10 (x y) (R2 x y)))
(printf "~%R1+R2:~%")
(pretty-print 
  (solve 10 (x y)
    ((extend-relation (a1 a2) R1 R2) x y)))

; Infinitary relation
; r(z,z).
; r(s(X),s(Y)) :- r(X,Y).

(define Rinf
  (extend-relation (a1 a2)
    (fact () 'z 'z)
    (relation (x y t1 t2)
      (to-show t1 t2)
      (== t1 `(s ,x))
      (== t2 `(s ,y))
      (Rinf x y))))
(printf "~%Rinf:~%")
(time (pretty-print (solve 5 (x y) (Rinf x y))))
(printf "~%Rinf+R1: Rinf starves R1:~%")
(time
  (pretty-print 
    (solve 5 (x y)
      ((extend-relation (a1 a2) Rinf R1) x y))))

; Solving starvation problem: extend R1 and R2 so that they
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

;;; Test for nonoverlapping.

(printf "~%any-union~%")
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

(define Rinf2
  (extend-relation (a1 a2)
    (fact () 'z 'z)
    (relation (x y t1 t2)
      (to-show t1 t2)
      (== t1 `(s (s ,x)))
      (== t2 `(s (s ,y)))
      (Rinf2 x y))))

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

; nrev([],[]).
; nrev([X|Rest],Ans) :- nrev(Rest,L), extend(L,[X],Ans).

; extend([],L,L).
; extend([X|L1],L2,[X|L3]) :- extend(L1,L2,L3).


; data([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
;                            21,22,23,24,25,26,27,28,29,30]).


(define nrev
  (extend-relation (a1 a2)
    (fact () '() '())
    (relation (x rest ans)
      (to-show `(,x . ,rest) ans)
      (exists (ls)
        (all
          (nrev rest ls)
          (concat ls `(,x) ans))))))

(let ((lst '(1 2 3 4 5 6 7 8 9
              10 11 12 13 14 15 16 17 18
              19 20 21 22 23 24 25 26 27
              28 29 30)))
  (test-check 'test-nrev
    (time
      (solution (x) (nrev lst x)))
    `((x.0 ,(reverse lst)))))

(define get_cpu_time
  (lambda ()
    (vector-ref (statistics) 1)))

(define lots
  (extend-relation ()
    (relation ()
      (to-show)
      (exists (count)
        (all
          (predicate () (newline))
          (predicate () (newline))
          (eg_count count)
          (bench count)
          fail)))
    (fact ())))

(define test-lots
  (lambda ()
    (solve 1000 () (lots))))

(define eg_count
  (extend-relation (a1)
    (fact () 10)
    (fact () 20)
    (fact () 50)
    (fact () 100)
    (fact () 200)
    (fact () 500)
    (fact () 1000)
    (fact () 2000)
    (fact () 5000)
    (fact () 10000)))

(define bench
  (relation (count)
    (to-show count)
    (let-inject ([t0 () (get_cpu_time)])
      (dodummy count)
      (let-inject ([t1 () (get_cpu_time)])
        (dobench count)
        (let-inject ([t2 () (get_cpu_time)])
          (report count t0 t1 t2))))))

(define dobench
  (extend-relation (a1)
    (relation (count)
      (to-show count)
      (repeat count)
      (nrev '(1 2 3 4 5 6 7 8 9
               10 11 12 13 14 15 16 17 18
               19 20 21 22 23 24 25 26 27
               28 29 30)
        _)
      fail)
    (fact () _)))

(define dodummy
  (extend-relation (a1)
    (relation (count)
      (to-show count)
      (repeat count)
      (dummy _)
      fail)
    (fact () _)))

(define dummy
  (relation ()
    (to-show _)))

(define repeat
  (extend-relation (a1)
    (fact (n) n)
    (relation (n)
      (to-show n)
      (all
        (predicate (n) (> n 1))
        (let-inject ([n1 (n) (- n 1)])
          (repeat n1))))))

(define report
  (relation (count t0 t1 t2)
    (to-show count t0 t1 t2)
    (exists (lips units)
      (let*-inject ([time1 (t0 t1) (- t1 t0)]
                    [time2 (t1 t2) (- t2 t1)]
                    [time () (- time2 time1)])
        (calculate_lips count time lips units)
        (predicate (lips count) (printf "~n~s lips for ~s" lips count))
        (predicate (time units)
          (printf " Iterations taking ~s  ~s ( ~s )~n " time units time))))))

(define calculate_lips
  (extend-relation (a1 a2 a3 a4)
    (relation (count time lips)
      (to-show count time lips 'msecs)
      (if-only (== time 0) (== lips 0))
      (let*-inject ([t1 (count) (* 496 count 1000)]
                    [t2 (time) (+ time 0.0)]
                    [lips^ () (/ t1 t2)])
        (== lips lips^)))))

;(test-lots)

(printf "Checking for dependency satisfaction in Haskell typeclasses~%")

; 	c(A,tuple(A,C,B),C,dict2).
; 	c(A,tuple(X,Y,B),C,dict1) :- c(A,B,C,_).
; Had I switched the order,
; 	c(A,tuple(X,Y,B),C,dict1) :- c(A,B,C,_).
; 	c(A,tuple(A,C,B),C,dict2).
; the queries would have never terminated. That's where our
; extend-relation-interleave would be quite handy.

;Complete code:
; Suppose we have the following Haskell class and instance declarations
;      class C a b c | a b -> c 
;      instance C a b c => C a (x,y,b) c
;      instance C a (a,c,b) c
;
; They will be compiled into the following database of instances,
; which define the class membership.
(define typeclass-C-instance-1
  (relation (a b c x y)
    (to-show a `(,x ,y ,b) c)
    (typeclass-C a b c)))

(define typeclass-C-instance-2
  (relation (a b c)
    (to-show a `(,a ,c ,b) c)))

(define typeclass-C
  (extend-relation (a b c) 
    typeclass-C-instance-2
    typeclass-C-instance-1))

; Run the checker for the dependency a b -> c
; Try to find the counter-example, that is, two members of (C a b c)
; such that a's and b's are the same but the c's are different.

;equality predicate: X == Y in Prolog
;if X is a var, then X == Y holds only if Y
;is the same var
(define *equal?
  (lambda (x y)
    (cond
      [(and (var? x) (var? y)) (eq? x y)]
      [(var? x) #f]                     ; y is not a var
      [(var? y) #f]                     ; x is not a var
      [else (equal? x y)])))
  
(define typeclass-counter-example-query
  (lambda (a b c1 c2)
    (all 
      (typeclass-C a b c1)
      (typeclass-C a b c2)
      (fails (predicate/no-check (c1 c2) (*equal? c1 c2))))))

(printf "~%Counter-example: ~s~%"
  (solution (a b c1 c2)
    (typeclass-counter-example-query a b c1 c2)))

(define depth-counter-var (let-lv (*depth-counter-var*) *depth-counter-var*))

; Run the antecedent no more than n times, recursively
(define with-depth
  (lambda (limit ant)
    (lambda@ (sk fk subst)
      (cond
        [(assq depth-counter-var subst)
         => (lambda (cmt)
              (let ([counter (commitment->term cmt)])
                (if (= counter limit)
                  (fk)
                  (let ([s (extend-subst depth-counter-var (+ counter 1) subst)])
                    (@ ant sk fk s)))))]
        [else
          (let ([s (extend-subst depth-counter-var 0 subst)])
            (@ ant sk fk s))]))))

; This does loop
'(define typeclass-C
   (extend-relation (a b c) 
     typeclass-C-instance-1
     typeclass-C-instance-2))

(define typeclass-C
  (lambda (a b c)
    (with-depth 2
      (any
	(typeclass-C-instance-1 a b c)
        (typeclass-C-instance-2 a b c)))))

(printf "~%Counter-example: ~s~%"
  (solution (a b c1 c2)
    (typeclass-counter-example-query a b c1 c2)))

(printf "~%Counter-example: ~s~%"
  (solve 4 (a b c1 c2)
    (typeclass-counter-example-query a b c1 c2)))

(printf "~%Append with limited depth~%")
; In Prolog, we normally write:
; append([],L,L).
; append([X|L1],L2,[X|L3]) :- append(L1,L2,L3).
;
; If we switch the clauses, we get non-termination.
; In our system, it doesn't matter!

(define extend-clause-1
  (relation (l)
    (to-show '() l l)))

(define extend-clause-2
  (relation (x l1 l2 l3)
    (to-show `(,x . ,l1) l2 `(,x . ,l3))
    (extend-rel l1 l2 l3)))

(define extend-rel
  (lambda (a b c)
    (with-depth 5
      (any
	(extend-clause-1 a b c)
        (extend-clause-2 a b c)))))

; Note (solve 100 ...)
; Here 100 is just a large number: we want to print all solutions
(printf "~%Extend: clause1 first: ~s~%" 
  (solve 100 (a b c) (extend-rel a b c)))

(define extend-rel
  (lambda (a b c)
    (with-depth 3
      (any
	(extend-clause-2 a b c)
        (extend-clause-1 a b c)))))

(printf "~%Extend: clause2 first. In Prolog, it would diverge!: ~s~%" 
  (solve 100 (a b c) (extend-rel a b c)))


; Extendix 1A
(printf "~%Test: checking dependency satisfaction: Another example.~%")
; Suppose we have the following Haskell class and instance declarations
;	class F a b | a->b
;	instance F a b => F [a] [b]
;	instance F [a] a
;

(define typeclass-F
  (lambda (a b)
    (with-depth 10
      (any
	((relation (a b)
	   (to-show `(list ,a) `(list ,b))
	   (typeclass-F a b)) a b)
	((relation (a)
	   (to-show `(list ,a) a)) a b)))))


; Run the checker for the dependency a -> b
; Try to find the counter-example, that is, two members of (F a b)
; such that as is the same but bs are different.
(define typeclass-F-counter-example-query
  (lambda (a b1 b2)
    (all 
      (typeclass-F a b1)
      (typeclass-F a b2)
      (fails (predicate/no-check (b1 b2) (*equal? b1 b2))))))

 (printf "~%Counter-example: ~s~%" 
   (solve 4 (a b1 b2) (typeclass-F-counter-example-query a b1 b2)))

 
(printf "~%Overloading resolution in Haskell.~%")
; Suppose we have the following Haskell class and instance declarations
;	class F a b | a->b where f :: a->b->Bool
;	instance F a b => F [a] [b]
;
; we need to typecheck
;   g x = f [x] x
; which says that f:: [a] -> a -> Bool
; In general, we need to figure out which instance to choose for f.
; In other words, we need to find out which subset of F to use.
; Here's only one instance. So we need to figure out if it applies.

(define typeclass-F-instance-1
  (relation (a b)
    (to-show `(list ,a) `(list ,b))
    (typeclass-F a b)))

; This is a closed-world assumption
(define typeclass-F
  (lambda (a b)
    (with-depth 10
      (any
	(typeclass-F-instance-1 a b)
	))))

(test-check "Typechecking (closed world)" 
  (solve 4 (a)
    (typeclass-F-instance-1 `(list ,a) a))
  '())					; meaning: does not typecheck!

; This is an open-world assumption
(define typeclass-F
  (lambda (a b)
    (with-depth 2
      (any
	(typeclass-F-instance-1 a b)
	((relation (a b1 b2)	; a relation under constraint a->b
	   (to-show a b1)
	   (fails
	     (all!
	       (typeclass-F a b2)
	       (fails (predicate/no-check (b1 b2) (*equal? b1 b2))))))
         a b)))))

(printf "~%Typechecking (open world): ~s~%" 
  (solve 4 (a) (typeclass-F-instance-1 `(list ,a) a)))

(test-check "Typechecking (open world) f [x] int" 
  (solve 4 (a) (typeclass-F-instance-1 `(list ,a) 'int))
  '())					; meaning: does not typecheck!

; Extendix B.

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

(printf "~%Inductive proof~%")


; First we need an extendible database of relations.
; We should be able to add to the database later on -- extend
; it with assumptions.
;
; One approach for the database is a finite map (hash table, assoc
; list) from the name of a relation to the procedure that is a relation
; in our system. Or, to make it even better, from a tuple
; (name arity) to the body of the relation.
; This is the approach of Prolog.
; Suppose we have a term (foo ?a ?b ?c) where ?a, ?b and ?c are arbitrary
; terms (logical variables, constants, expressions, etc). 
; We would like to check if this term is consistent with (i.e., can
; be proven by) a particular instance of the database.
; First, we need to look up a key (foo 3) in the database. If the
; lookup fails, so does our query. If the lookup succeeds, we get
; a procedure of three arguments. We apply this procedure to
; ?a, ?b, and ?c and obtain an antecedent, which we can 'solve'
; as usual.

; In the following, we chose a different approach. We represent the database
; of relations as a relation itself -- we will call it KB. That
; relation takes one argument -- the term to prove, and returns an antecedent
; that represents the answer (that antecedent may be 'fail').
; A database of one fact
;  foo(a,b,c).
; in Prolog notation will be represented in our approach as a relation
;   (relation _ () (to-show `(foo a b c)))
; If we want to add another relation, say
; bar(X,X).
; we need to _extend_ the above relation with
;  (relation _ (x) (to-show `(bar x x))).
;
; This approach is probably less efficient than the first one. It has
; however a redeeming value -- we do not need a separate procedure
; to look up names/arities of relations. We don't need separate procedures
; for extending our database. We can use the existing machinery of
; 'solving' relations for 'solving' the database of relations.
; This approach seems reminiscent of the Futamura projections:
; we use the same engine for meta-evaluations. Bootstrapping.

; First we define the inductive structure

; In Athena:
;  (structure (BTree S)
;     (leaf S)
;     (root (BTree S) (BTree S)))

; In Prolog
; btree(leaf(S)).
; btree(root(T1,T2)) :- btree(T1),btree(T2).

; Note, our trees here (as well as those in Prolog) are polytypic
; (polymorphic): leaves can have values of different sorts.

; When we attempt to translate
;	btree(root(T1,T2)) :- btree(T1),btree(T2).
; into our system, we encounter the first difficulty. To find out
; if a term btree(root(T1,T2)) is consistent with our database of relations,
; we need to check if terms  btree(T1) and  btree(T2) are consistent.
; Thus, to add btree(root(T1,T2)) to our database, we need to use
; the database itself to verify btree(T1) and btree(T2). Clearly,
; we need a fixpoint. The need for the fixpoint exists no matter what is
; the representation of the database -- a finite map or a relation.
; Prolog solves the fixpoint problem by making the database global
; and using mutations (similar to the way letrec is implemented in Scheme).
; If we attempt to be purely functional, we must make the fixpoint explicit
; and employ Y.

; Note, the kb variable below represents the "current" database.
; In our approach, the database is a relation of one argument,
; which is a term to prove. A Second-order relation???

(define btree
  (lambda (kb)
    (extend-relation (t)
      (fact (val) `(btree (leaf ,val)))
      (relation (t1 t2)
	(to-show `(btree (root ,t1 ,t2)))
	(predicate (t1 t2) (printf "btree ~s ~s ~n" t1 t2))
	(kb `(btree ,t1))
	(kb `(btree ,t2))))))

;%> (declare mirror ((S) -> ((BTree S)) (BTree S)))

; Introduce an equality predicate and the first axiom for mirror
; In Athena:
; (define mirror-axiom-1
;   (forall ?x
;     (= (mirror (leaf ?x)) (leaf ?x))))

; In Prolog
; myeq(leaf(X),mirror(leaf(X))).

(define mirror-axiom-eq-1
  (lambda (kb)
    (fact (val) `(myeq (leaf ,val) (mirror (leaf ,val))))))

; The second axiom
; In Athena:
; (define mirror-axiom-eq-2
;   (forall ?t1 ?t2
;     (= (mirror (root ?t1 ?t2))
;       (root (mirror ?t2) (mirror ?t1)))))

; In Prolog
; myeq(root(B,A),mirror(root(T1,T2))) :- myeq(A,mirror(T1)),myeq(B,mirror(T2)).

; implicitly the axiom in Prolog and the one below assume
; the transitivity of myeq. Indeed, one may think that the direct
; translation from Athena to Prolog would be
;
;   myeq(mirror(root(T1,T2)),root(mirror(T2),mirror(T1)))
; or
;   myeq(mirror(root(T1,T2)),root(B,A)) :- B = T2, A = T1.
; However, Athena actually assumes that B and T2 can be myeq rather
; than merely identical. We also switched the order of arguments
; in myeq, assuming symmetry of myeq.
; It really helped in Prolog. In our system, we could have used
; the same order as in Athena and add:
;    myeq(A,A).   % reflexivity: identity implies equality
;    myeq(A,B) :- myeq(B,A). % symmetry
; Clearly if we add these relations to Prolog code, it will diverge.
; In our system, we can use with-depth to keep divergence in check.
; Still, for simplicity and clarity we will simply model the Prolog solution
; in our code.

(define mirror-axiom-eq-2
  (lambda (kb)
    (relation  (a b t1 t2)
      (to-show `(myeq (root ,b ,a) (mirror (root ,t1 ,t2))))
      (kb `(myeq ,a (mirror ,t1)))
      (kb `(myeq ,b (mirror ,t2))))))

; we could also add reflexivity and transitivity and symmetry axioms
; and with-depth to keep them from diverging.

; Define the goal
; In Athena:
;  (define (goal t)
;     (= (mirror (mirror t)) t))

; In Prolog
; Note, the goal is _equivalent_ to the conjunction of the
; predicates. That's why we couldn't use the standard Prolog
; notation goal(T) :- btree(T), ...
; because the latter would give us only the implication.
; goal(T,[btree(T),myeq(T,mirror(T1)),myeq(T1,mirror(T))]).

(define goal
  (lambda (t)
    (let-lv (t1)
      (list
	`(btree ,t)
	`(myeq ,t  (mirror ,t1))
	`(myeq ,t1 (mirror ,t))))))

; For clarity, the above predicate can be written as two (prolog) relations
; The forward relation:
; (goal t) is implied by (btree t), (myeq t (mirror t1)) and 
;                        (myeq t1 (mirror t))
; In the above, t is universally quantified and t1 is existentially
; quantified

(define goal-fwd
  (lambda (kb)
    (relation (t t1)
      (to-show `(goal ,t))
      (kb `(btree ,t))
      (kb `(myeq ,t  (mirror ,t1)))
      (kb `(myeq ,t1 (mirror ,t))))))

; The reverse relation for the goal:
; (goal t) implies (btree t), (myeq t (mirror t1)) and 
;                             (myeq t1 (mirror t))
; In the above, t is universally quantified and t1 is existentially
; quantified
; Because t1 now appears on the left-hand side, it is represented
; as an eigenvariable (skolem function) rather than a logical variable

(define symbol-append
  (lambda symbs
    (string->symbol
      (apply string-append
        (map symbol->string symbs)))))

(define goal-rev
  (let* ((sk (symbol-append 'sk ': (gensym)))
	 (t1-sk (lambda (t) `(,sk ,t))))
    (lambda (kb)
      (extend-relation (t)
	(relation (t)			; (goal t) => (btree t)
	  (to-show `(btree ,t))
	  (kb `(goal ,t)))
	(relation (t)			; (goal t) => (myeq t  (mirror t1))
	  (to-show `(myeq ,t  (mirror ,(t1-sk t))))
	  (kb `(goal ,t)))
	(relation (t)			; (goal t) => (myeq t1 (mirror t))
	  (to-show `(myeq ,(t1-sk t) (mirror ,t)))
	  (kb `(goal ,t)))
	))))
      
      
      
(define Y
  (lambda (f)
    ((lambda (u) (u (lambda (x) (lambda (n) ((f (u x)) n)))))
     (lambda (x) (x x)))))

; The initial assumptions: just the btree
(define init-kb (Y btree))

; Verification engine
;	verify-goal PREDS KB
; returns a nullary relation that is the conjunction of preds against the
; assumption base kb
(define verify-goal
  (lambda (preds kb)
    (cond
      [(null? (cdr preds)) (kb (car preds))]
      [else (all
              (kb (car preds))
              (verify-goal (cdr preds) kb))])))

; A better version of concretize that replaces each variable
; with a _unique_! symbol. The unique symbol symbolizes universal
; quantification, as usual.

; get the free vars of term
(define free-vars
  (lambda (term)
    (let loop ([term term] [fv '()])
      (cond
        [(var? term) (if (memq term fv) fv (cons term fv))]
        [(pair? term) (loop (cdr term) (loop (car term) fv))]
        [else fv]))))

(define concretize*
  (lambda (term)
    (let ([fv (free-vars term)])
      (let ([subst
              (map
                (lambda (v)
                  (commitment v
                    (symbol-append (var-id v) ': (gensym))))
                fv)])
        (subst-in term subst)))))

; extend the kb with the list of assumptions
; this is just like 'any' only it's a procedure rather than a syntax
; Why we need concretize*?
; Suppose, the list of facts includes
;	(fact (x) (foo x)) and (fact (x) (bar x))
; definitely, we do not want to imply that facts foo and bar _share_
; the same logical variable. The facts are independent and should
; not have any variables in common.
; Furthermore, we do not want to add
;	(fact (x) (foo x))
; because that would mean exist x. foo x
; We want our facts to be universally quantified. So, we add
;	(fact () (foo 'unique-symbol))
; See the distinction between sigma and pi in Lambda-Prolog.
; We use extend-kb to extend the database with assumptions, which most
; often are universally quantified.

(define extend-kb
  (lambda (facts kb)
    (let ([facts (concretize* facts)])
      (printf "Extending KB with ~s~%" facts)
      (let loop ([facts facts])
        (if (null? facts) kb
            (extend-relation (t)
              (fact () (car facts))
              (loop (cdr facts))))))))

; Here's Athena's induction proof.
;
; (by-induction-on ?t (goal ?t)
;   ((leaf x) (!pf (goal (leaf x)) [mirror-axiom-1]))
;   ((root t1 t2) 
;     (!pf (goal (root t1 t2)) [(goal t1) (goal t2)  mirror-axiom-2])))

; The first part of it, the base case, can be expressed in Prolog
; as follows.
; ?- goal(leaf(X),C),verify(C,[]).
; Here how it looks in our system:
(printf "~%First check the base case ~s~%"
  (query
    (verify-goal (goal '(leaf x))
      (extend-relation (t) (mirror-axiom-eq-1 init-kb) init-kb))))

(printf "~%First check the base case, using goal-fwd ~s~%"
  (query
    (let ((kb0
	    (extend-relation (t) (mirror-axiom-eq-1 init-kb) init-kb)))
      (let ((kb1
	      (extend-relation (t) (goal-fwd kb0) kb0)))
	(kb1 '(goal (leaf x))))))) ; note, x is an eigenvariable!


; that is, we obtain the list of subgoals to verify '(leaf x)
; by invoking the function 'goal'.
; we extend the initial database (which contains btree facts)
; with mirror-axiom-eq-1. Thus, mirror-axiom-eq-1 and btree form
; the assumptions. We then verify the subgoals against the assumptions.
; Note that we wrote
;    '(leaf x)
; rather than
;    (let-lv (x) `(leaf ,x))
; because we want to prove that (goal '(leaf x)) holds for _all_ x
; rather than for some particular x.
;
; non-empty result printed by the above expressions means success...


; The inductive case.
; Now, assume the goal holds for t1 and t2 and check if it holds
; for root(t1,t2)
;?- goal(t1,A1),goal(t2,A2), append(A1,A2,A), goal(root(t1,t2),C), verify(C,A).

(printf "~%Some preliminary checks ~s~%"
  (query
    (verify-goal '((btree t2)) ; (goal t2) => (btree t2)
      (let ((kb0
	      (extend-kb (goal 't1) 
		(extend-kb (goal 't2) init-kb))))
	kb0))))

(printf "~%Some preliminary checks, using goal-rev ~s~%"
  (query
    (let ((kb
	    (Y
	      (lambda (kb)
		(extend-relation (t)
		  (btree kb)
		  (goal-rev kb)
		  (fact () '(goal t1))
		  (fact () '(goal t2)))))))
      (kb '(btree t2)))))

; the above two expressions should give the same result: a non-empty stream
; (with an empty substitution: no variables leak)

(printf "~%Another check ~s~%"
  (query
	;(goal t1), (goal t2) => (btree (root t1 t2))
    (verify-goal '((btree t1) (btree t2)
		   (btree (root t1 t2)))
      (let ((kb0
	      (extend-kb (goal 't1) 
		(extend-kb (goal 't2) 
		  (fact () 'nothing)))))
	(Y
	  (lambda (kb)
	    (extend-relation (t)
	      kb0
	      (btree kb)
	      (mirror-axiom-eq-2 kb))))))))

(printf "~%Another checks, using goal-rev ~s~%"
  (query
    (let ((kb
	    (Y
	      (lambda (kb)
		(extend-relation (t)
		  (btree kb)
		  (goal-rev kb)
		  (mirror-axiom-eq-2 kb)
		  (fact () '(goal t1))
		  (fact () '(goal t2)))))))
      (kb '(btree (root t1 t2))))))

; now we really need Y because we rely on the clause
;	btree(root(T1,T2)) :- btree(T1),btree(T2).
; which is recursive.

(printf "~%Check the inductive case ~s~%"
  (query
    (verify-goal (goal '(root t1 t2))
      (let ((kb0
	      (extend-kb (goal 't1) 
		(extend-kb (goal 't2) 
		  (fact () 'initial)))))
	(Y
	  (lambda (kb)
	    (extend-relation (t)
	      kb0
	      (btree kb)
	      (mirror-axiom-eq-2 kb))))))))

(printf "~%Check particulars of the inductive case, using goal-rev, goal-fwd ~s~%"
  (let ((kb
          (Y
            (lambda (kb)
              (extend-relation (t)
                (btree kb)
                (fact () '(goal t1))
                (fact () '(goal t2))
                (mirror-axiom-eq-2 kb)
                (goal-rev kb)
                )))))
    (list
      (solve 1 (x) (kb `(myeq (root t1 t2)  (mirror ,x))))
      (solve 1 (x) (kb `(myeq ,x (mirror (root t1 t2))))))))

(printf "~%Check the inductive case, using goal-rev, goal-fwd ~s~%"
  (query
    (let ((kb
	    (Y
	      (lambda (kb)
		(extend-relation (t)
		  (btree kb)
		  (fact () '(goal t1))
		  (fact () '(goal t2))
		  (mirror-axiom-eq-2 kb)
		  (goal-rev kb))))))
      (let ((kb1 (goal-fwd kb)))
	(kb1 '(goal (root t1 t2)))))))

; Again, we use Y because btree and mirror-axiom-eq-2 are recursive.
; We need the database that is the fixpoint of all constituent
; relations.
; The output above is a non-empty list: meaning that the inductive
; phase of the proof checks.

;(exit 0)

(define base-+-as-relation
  (fact (n) 'zero n n))

(define recursive-+-as-relation
  (relation (n1 n2 n3)
    (to-show `(succ ,n1) n2 `(succ ,n3))
    (+-as-relation n1 n2 n3)))

(define +-as-relation
  (extend-relation (a1 a2 a3)
    base-+-as-relation
    recursive-+-as-relation))

(newline)

;   1. There are five houses in a row, each of a different color<BR>
;       and inhabited by men of different nationalities,<BR>
;       with different pets, drinks, and cigarettes.<BR>
;   2. The Englishman lives in the red house.<BR>
;   3. The Spaniard owns a dog.<BR>
;   4. Coffee is drunk in the green house.<BR>
;   5. The Ukrainian drinks tea.<BR>
;   6. The green house is directly to the right of the ivory house.<BR>
;   7. The Old Gold smoker owns snails.<BR>
;   8. Kools are being smoked in the yellow house.<BR>
;   9. Milk is drunk in the middle house.<BR>
;  10. The Norwegian lives in the first house on the left.<BR>
;  11. The Chesterfield smoker lives next to the fox owner.<BR>
;  12. Kools are smoked in the house next to the house where the horse is kept.<BR>
;  13. The Lucky Strike smoker drinks orange juice.<BR>
;  14. The Japanese smokes Parliaments.<BR>
;  15. The Norwegian lives next to the blue house.<BR><BR>

(define member 
  (extend-relation (a1 a2)
    (fact (item) item `(,item . ,_))
    (relation (item rest) (to-show item `(,_ . ,rest)) (member item rest))))

(define next-to
  (relation (item1 item2 rest)
    (to-show item1 item2 rest)
    (any (on-right item1 item2 rest) (on-right item2 item1 rest))))

(define on-right
  (extend-relation (a0 a1 a2)
    (fact (item1 item2) item1 item2 `(,item1 ,item2 . ,_))
    (relation (item1 item2 rest)
      (to-show item1 item2 `(,_ . ,rest))
      (on-right item1 item2 rest))))
        
(define zebra
  (relation (h)
    (to-show h)
    (if-all!
      ((== h `((norwegian ,_ ,_ ,_ ,_) ,_ (,_ ,_ milk ,_ ,_) ,_ ,_))
       (member `(englishman ,_ ,_ ,_ red) h)
       (on-right `(,_ ,_ ,_ ,_ ivory) `(,_ ,_ ,_ ,_ green) h)
       (next-to `(norwegian ,_ ,_ ,_ ,_) `(,_ ,_ ,_ ,_ blue) h)
       (member `(,_ kools ,_ ,_ yellow) h)
       (member `(spaniard ,_ ,_ dog ,_) h)
       (member `(,_ ,_ coffee ,_ green) h) 
       (member `(ukrainian ,_ tea ,_ ,_) h)
       (member `(,_ luckystrikes oj ,_ ,_) h)
       (member `(japanese parliaments ,_ ,_ ,_) h)
       (member `(,_ oldgolds ,_ snails ,_) h)
       (next-to `(,_ ,_ ,_ horse ,_) `(,_ kools ,_ ,_ ,_) h)
       (next-to `(,_ ,_ ,_ fox ,_) `(,_ chesterfields ,_ ,_ ,_) h)
      )
      (all (member `(,_ ,_ water ,_ ,_) h)
	(member `(,_ ,_ ,_ zebra ,_) h)))))

(test-check "Addition"
  (solve 20 (x y)
    (+-as-relation x y '(succ (succ (succ (succ (succ zero)))))))
  '(((x.0 zero) (y.0 (succ (succ (succ (succ (succ zero)))))))
    ((x.0 (succ zero)) (y.0 (succ (succ (succ (succ zero))))))
    ((x.0 (succ (succ zero))) (y.0 (succ (succ (succ zero)))))
    ((x.0 (succ (succ (succ zero)))) (y.0 (succ (succ zero))))
    ((x.0 (succ (succ (succ (succ zero))))) (y.0 (succ zero)))
    ((x.0 (succ (succ (succ (succ (succ zero)))))) (y.0 zero))))

(test-check "Zebra"
  (time (solution (h) (zebra h)))
  '((h.0 ((norwegian kools water fox yellow)
          (ukrainian chesterfields tea horse blue)
          (englishman oldgolds milk snails red)
          (spaniard luckystrikes oj dog ivory)
          (japanese parliaments coffee zebra green)))))

; mirror with the equational theory

(define myeq-axioms
  (lambda (kb)
    (extend-relation (t)
      (fact (val) `(myeq ,val ,val)) ; reflexivity
      (relation (a b)
	(to-show `(myeq ,a ,b))		; symmetry
	(predicate/no-check (a b) (printf "symmetry: ~a ~a ~n" a b))
	(kb `(myeq ,b ,a)))
      (relation (a b)			; transitivity
	(to-show `(myeq ,a ,b))
	(exists (c)
	  (all
	    (kb `(myeq ,a ,c))
	    (kb `(myeq ,c ,b)))))
      )))

(define myeq-axioms-trees		; equational theory of trees
  (lambda (kb)				; equality commutes with root
    (extend-relation (t)
      (relation (a b c d)
	(to-show `(myeq (root ,a ,b) (root ,c ,d)))
	(predicate/no-check (a b) (printf "trees: ~a ~a ~a ~a ~n" a b c d))
	(kb `(myeq ,a ,c))
	(kb `(myeq ,b ,d))))))
  
; equality on leaves follows from the reflexivity of equality

(define myeq-axioms-mirror		; equational theory of mirror
  (lambda (kb)				; equality commutes with root
    (extend-relation (t)
      (relation (a b)
	(to-show `(myeq (mirror ,a) ,b))
	(predicate/no-check (a b) (printf "mirror: ~a ~a~n" a b))
	(exists (c)
	  (all (kb `(myeq ,b (mirror ,c)))
	       (kb `(myeq ,a ,c))))))))
 
; The second axiom
; In Athena:
; (define mirror-axiom-eq-2
;   (forall ?t1 ?t2
;     (= (mirror (root ?t1 ?t2))
;       (root (mirror ?t2) (mirror ?t1)))))


(define mirror-axiom-eq-2
  (lambda (kb)
    (fact (t1 t2) `(myeq (root ,t1 ,t2) (root (mirror ,t2) (mirror ,t1))))))

(define mirror-axiom-eq-2
  (lambda (kb)
    (relation (t1 t2) 
      (to-show `(myeq (mirror (root ,t1 ,t2)) (root (mirror ,t2) (mirror ,t1))))
      (predicate/no-check (t1 t2)
	(printf "mirror ax2: ~a~n"
	  `(myeq (root ,t1 ,t2) (root (mirror ,t2) (mirror ,t1))))))))

; Define the goal
; In Athena:
;  (define (goal t)
;     (= (mirror (mirror t)) t))

(define goal
  (lambda (t)
    (list 
      `(btree ,t)
      `(myeq (mirror (mirror ,t)) ,t))))

(define goal-fwd
  (lambda (kb)
    (relation (t)
      (to-show `(goal ,t))
      (kb `(btree ,t))
      (kb `(myeq (mirror (mirror ,t)) ,t)))))

(define goal-rev
  (lambda (kb)
    (extend-relation (t)
      (relation (t)			; (goal t) => (btree t)
	(to-show `(btree ,t))
	(kb `(goal ,t)))
      (relation (t)		; (goal t) => (myeq (mirror (mirror t)) t)
	(to-show `(myeq (mirror (mirror ,t)) ,t))
	(kb `(goal ,t))))))

; (by-induction-on ?t (goal ?t)
;   ((leaf x) (!pf (goal (leaf x)) [mirror-axiom-1]))
;   ((root t1 t2) 
;     (!pf (goal (root t1 t2)) [(goal t1) (goal t2)  mirror-axiom-2])))


'(define mirror-axiom-eq-1
  (lambda (kb)
    (relation (val)
      (to-show `(myeq (leaf ,val) (mirror (leaf ,val))))
      (predicate/no-check () (printf "mirror-axiom-eq-1: ~a~n" val)))))

; The initial assumptions: just the btree
;(define init-kb (Y btree))
(define init-kb-coll
  (lambda (kb)
    (lambda (t)
      (with-depth 5
	(any
	  ((btree kb) t)
	  ((myeq-axioms kb) t)
	  ((myeq-axioms-mirror kb) t)
	  ((myeq-axioms-trees kb) t)
	)))))


(printf "~%First check the base case, using goal-fwd ~s~%"
  (query
    (let ((kb0
	    (Y (lambda (kb)
		 (extend-relation (t) 
		   (mirror-axiom-eq-1 kb)
		   (init-kb-coll kb))))))
      (let ((kb1
	      (extend-relation (t) (goal-fwd kb0) kb0)))
	(kb1 '(goal (leaf x))))))) ; note, x is an eigenvariable!


(printf "~%Some preliminary checks, using goal-rev ~s~%"
; (goal t2) => (btree t2)
  (query
    (let ((kb
	    (Y
	      (lambda (kb)
		(extend-relation (t)
		  (init-kb-coll kb)
		  (goal-rev kb)
		  (fact () '(goal t1))
		  (fact () '(goal t2)))))))
      (kb '(btree t2)))))

(printf "~%Another check, using goal-rev ~s~%"
  (query
	;(goal t1), (goal t2) => (btree (root t1 t2))
    (let ((kb
	    (Y
	      (lambda (kb)
		(extend-relation (t)
		  (init-kb-coll kb)
		  (goal-rev kb)
		  (mirror-axiom-eq-2 kb)
		  (fact () '(goal t1))
		  (fact () '(goal t2)))))))
      (kb '(btree (root t1 t2))))))

'(printf "~%Check particulars of the inductive case, using goal-rev, goal-fwd ~s~%"
  (let ((kb
          (Y
            (lambda (kb)
              (extend-relation (t)
                (init-kb-coll kb)
                (fact () '(goal t1))
                (fact () '(goal t2))
                (mirror-axiom-eq-2 kb)
                (goal-rev kb)
                )))))
    (list
      ;(solve 1 (x) (kb `(myeq (root t1 t2)  (mirror ,x))))
      (solve 1 (x) (kb `(myeq ,x (mirror (root t1 t2)))))
      )))

(printf "~%Check the inductive case, using goal-rev, goal-fwd ~s~%"
  (query
    (let ((kb
	    (Y
	      (lambda (kb)
		(extend-relation (t)
		  (init-kb-coll kb)
		  (fact () '(goal t1))
		  (fact () '(goal t2))
		  (mirror-axiom-eq-2 kb)
		  (goal-rev kb))))))
      (let ((kb1 (goal-fwd kb)))
	(kb1 '(goal (root t1 t2)))))))

(define-syntax nabla
  (syntax-rules ()
    [(_ () ant0 ant1 ...)
     (all ant0 ant1 ...)]
    [(_ (id ...) ant0 ant1 ...)
     (let-lv (id ...)
       (lambda@ (sk fk in-subst)
	 (@ (all ant0 ant1 ...)
            (lambda@ (fk out-subst)
              (let ([ps (prune-subst (list id ...) in-subst out-subst)])
                (if (ormap (lambda (cmt)
                             (or (occurs-check? id (commitment->term cmt))
                                 ...))
                      ps)
		  (fk)
		  (@ sk fk ps))))
            fk in-subst)))]))


(exit 0)
