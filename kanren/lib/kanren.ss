;Soon to create two load-alls.
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

; LET*-AND: a simplified and streamlined AND-LET*.
; The latter is defined in SRFI-2 <http://srfi.schemers.org/srfi-2/>

(define-syntax let*-and
  (syntax-rules ()
    [(_ false-exp () body0 body1 ...) (begin body0 body1 ...)]
    [(_ false-exp ([var0 exp0] [var1 exp1] ...) body0 body1 ...)
     (let ([var0 exp0])
       (if var0
         (let*-and false-exp ([var1 exp1] ...) body0 body1 ...)
         false-exp))]))

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

;------------------------------------------------------------------------
; Logical variables, substitutions, and commitments (aka bindings)
   
(define-record var (id) ())
(define var make-var)

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

; relatively-ground? TERM (VAR ...) -> BOOL
; Returns #t if none of the VARs occur in TERM
(define relatively-ground?
  (lambda (term vars)
    (cond
      [(var? term) (not (memq term vars))]
      [(pair? term)
       (and (relatively-ground? (car term) vars)
            (relatively-ground? (cdr term) vars))]
      [else #t])))


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


'(define == 
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


;  Fk  = () -> Ans
;  Ans =  Nil + [Subst,Fk]
;  Sk = Fk -> Subst -> Ans  
;  Antecedent = Sk -> Sk
;  Rule = Antecedent -> [Goal-fn,Int] -> Antecedent

;  relation: Term -> Antecedent
;  to-show: Term -> Antecedent -> Rule
;  initial-sk : Sk
;  initial-fk : Fk

(define initial-fk (lambda () '()))
(define initial-sk (lambda@ (fk subst)
		     ;(pretty-print subst)
		     (cons subst fk)))

;------------------------------------------------------------------------
; Making logical variables "scoped" and garbage-collected

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

; PRUNE IN-SUBST SUBST ID ....
; remove the bindings of ID ... from SUBST (by composing with the
; rest of subst). IN-SUBST is the mark.
; If we locate IN-SUBST in SUBST, we know that everything below the
; mark can't possibly contain ID ...

(define rev-append
  (lambda (ls1 ls2)
    (cond
      [(null? ls1) ls2]
      [else (rev-append (cdr ls1) (cons (car ls1) ls2))])))

(define prune-subst
  (lambda (vars in-subst subst)
    (if (eq? subst in-subst)
        subst
        (let loop ([current subst] [to-remove '()] [clean '()] [to-subst '()])
          (cond
            [(null? current) (compose-subst/own-survivors to-subst to-remove clean)]
            [(eq? current in-subst)
             (compose-subst/own-survivors to-subst to-remove (rev-append clean current))]
            [(memq (commitment->var (car current)) vars)
             (loop (cdr current) (cons (car current) to-remove) clean to-subst)]
            [(relatively-ground? (commitment->term (car current)) vars)
             (loop (cdr current) to-remove (cons (car current) clean) to-subst)]
            [else (loop (cdr current) to-remove clean (cons (car current) to-subst))])))))

; when the unifier is moved up, move prune-subst test from below up...



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
      (lambda@ (sk fk subst)
	(@ condition
	  (lambda@ (fk-ign) (@ then sk fk))
	  (lambda () (@ else sk fk subst))
	  subst)))
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
  (syntax-rules (to-show head-let)
    [(_ (head-let head-term ...) ant)
     (relation-head-let (head-term ...) ant)]
    [(_ (head-let head-term ...))	; not particularly useful without body
     (relation-head-let (head-term ...))]
    [(_ () (to-show x ...) ant)		; pattern with no vars _is_ linear
     (relation-head-let (`,x ...) ant)]
    [(_ () (to-show x ...))		; the same without body: not too useful
     (relation-head-let (`,x ...))]
    [(_ (ex-id ...) (to-show x ...) ant)  ; body present
     (relation (ex-id ...) () (x ...) (x ...) ant)]
    [(_ (ex-id ...) (to-show x ...))      ; no body
     (relation (ex-id ...) () (x ...) (x ...))]
    [(_ (ex-id ...) (var ...) (x0 x1 ...) xs ant ...) 
     (relation (ex-id ...) (var ... g) (x1 ...) xs ant ...)]
    [(_ (ex-id ...) () () () ant)	; no arguments (no head-tests)
      (lambda ()
	(exists (ex-id ...) ant))]
    [(_ (ex-id ...) (g ...) () (x ...)) ; no body
     (lambda (g ...)
       (exists (ex-id ...)
 	 (all!! (promise-one-answer (== g x)) ...)))]
    [(_ (ex-id ...) (g ...) () (x ...) ant) ; the most general
     (lambda (g ...)
       (exists (ex-id ...)
 	 (if-all! ((promise-one-answer (== g x)) ...) ant)))]
    ))


; relation-head-let (head-term ...) ant
; A simpler, and more efficient kind of relation. The simplicity
; comes from a simpler pattern at the head of the relation. The pattern
; must be linear and shallow with respect to introduced variables.
; The ant is optional (although omitting it doesn't make much sense
; in practice)
; There are two kinds of head-terms.
; One kind is an identifier. This identifier is taken to be a logical
; identifier, to be unified with the corresponding actual argument.
; Each logical identifier must occur exactly once.
; Another kind of a head-terms is anything else. That anything 
; else may be a constant, a scheme variable, or a complex term that
; may even include logical variables such as _ -- but not logical
; variables defined in the same head-let pattern.
; To make the task of distinguishing logical identifiers from anything else
; easier, we require that anything else of a sort of a manifest constant
; be explicitly quoted or quasiquoted. It would be OK to add `, to each
; 'anything else' term.
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

(define-syntax relation-head-let
  (syntax-rules ()
    [(_ (head-term ...) . ants)
     (relation-head-let "g" () (head-term ...) (head-term ...) . ants)]
    ; generate names of formal parameters
    [(_ "g" (genvar ...)  (head-term . ht-rest) head-terms . ants)
     (relation-head-let "g" (genvar ... g) ht-rest head-terms . ants)]
    [(_ "g" genvars  () head-terms . ants)
     (relation-head-let "d" () () genvars head-terms genvars . ants)]
    ; partition head-terms into vars and others
    [(_ "d" vars others (gv . gv-rest) ((hth . htt) . ht-rest) gvs . ants)
     (relation-head-let "d" vars ((gv (hth . htt)) . others)
       gv-rest ht-rest gvs . ants)]
    [(_ "d" vars others (gv . gv-rest) (htv . ht-rest) gvs . ants)
     (relation-head-let "d" ((gv htv) . vars) others
       gv-rest ht-rest gvs . ants)]
    [(_ "d" vars others () () gvs . ants)
     (relation-head-let "f" vars others gvs . ants)]

    ; final generation
    [(_ "f" vars ((gv term) ...) gvs) ; no body
     (lambda gvs                                     ; don't bother bind vars
       (lambda@ (sk fk subst)
	 (let*-and (fk) ([subst (unify gv term subst)] ...)
	   (@ sk fk subst))))]

    [(_ "f" ((gvv var) ...) ((gvo term) ...) gvs ant)
     (lambda gvs
       (lambda@ (sk fk subst)			; first unify the constants
	 (let*-and (fk) ([subst (unify gvo term subst)] ...)
	   (let ([var (if (eq? gvv _) (var '?) gvv)] ...)
	     (@ ant sk fk subst)))))]))

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

(test-check 'test-grandpa-10-1
  (solve 10 (x) (grandpa x 'sue))
  '(((x.0 sam))))

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

; TRACE-VARS TITLE (VAR ...)
; Is a deterministic antecedent that prints the current values of VARS
; TITLE is any displayable thing.

(define-syntax trace-vars
  (syntax-rules ()
    ((trace-vars title (var ...))
      (promise-one-answer
	(predicate/no-check (var ...)
	  (begin (display title) (display " ")
	    (display '(var ...)) (display " ") (display (list var ...))
	    (newline)))))))


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

; Either t or u may be:
; _
; free-var
; bound-var
; pair
; other-value
; So, we have in general 25 possibilities to consider.
; actually, a pair or components of a pair can be variable-free
; or not. In the latter case, we have got to traverse them.

(define unify
  (lambda (t u subst)
    (cond
      [(eq? t u) subst]			; quick tests first
      [(eq? t _) subst]
      [(eq? u _) subst]
      [(var? t)
	(let ((ct (assq t subst)))
	  (if ct (unify-bound/any ct u subst)
	    (unify-free/any t u subst)))]
      [(var? u)				; t is not a variable...
	(let ((cu (assq u subst)))
	  (if cu
	    (unify (commitment->term cu) t subst)
	    (if (pair? t)
	      (unify-free/list u t subst)
              ; t is not a var and is not a pair: it's atomic
	      (extend-subst u t subst))))]
      [(and (pair? t) (pair? u))
       (cond
         [(unify (car t) (car u) subst)
          => (lambda (car-subst)
               (unify (cdr t) (cdr u) car-subst))]
         [else #f])]
      [else (and (equal? t u) subst)])))

; t-var is a free variable, u can be anything
(define unify-free/any
  (lambda (t-var u subst)
    (cond
      ((eq? u _) subst)
      ((var? u)
	(let ((cu (assq u subst)))
	  (if cu (unify-free/bound t-var cu subst)
	    (extend-subst t-var u subst))  ; t-var and u are both free
	))
      ((pair? u)
	(unify-free/list t-var u subst))
      (else ; u is not a var and is not a pair: it's atomic
	(extend-subst t-var u subst)))))

; ct is a commitment to a bound variable, u can be anything
(define unify-bound/any
  (lambda (ct u subst)
    (cond
      ((eq? u _) subst)
      ((var? u) 
	(let ((cu (assq u subst)))
	  (if cu
	    ; both t and u are bound...
	    (unify (commitment->term ct) (commitment->term cu) subst)
	    ; t is bound, u is free
	    (unify-free/bound u ct subst))))
      (else ; unify bound and a value
	(unify (commitment->term ct) u subst)))))

; On entrance: t-var is free.
; we are trying to unify it with a bound variable (commitment->var cu)
; Chase the binding chain, see below for comments
; This also works somewhat like union-find...
(define unify-free/bound
  (lambda (t-var cu s)
    (let loop ([cm cu])
      (let ([u-term (commitment->term cm)])
	(cond
	  [(eq? u-term t-var) s]
	  [(var? u-term)
	    (cond
	      [(assq u-term s) => loop]
	      [else (extend-subst t-var u-term s)])] ; u-term is free here
	  [else (extend-subst t-var u-term s)])))))

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

; t-var is a free variable, u-value is a proper or improper
; list, which may be either fully or partially grounded (or not at all).
; We replace all non-grounded components of the list with fresh variables,
; bind t-var to the resulting list, and proceed unifying the introduced
; variables with the corresponding components of the original list.
; NB: in the general case, if more than one component of u-value
; is replaced by fresh variables, we must use the full unify rather
; than unify-free/any because some component of u-value may
; mention t-var (and so, after the first unification, fresh variables
; may become ground).

    ; return the list of assoc of fresh variables with
    ; non-ground cells of lst-src (which may be improper!)
(define ufl-analyze-list
  (lambda (lst-src)
    (if (pair? lst-src)
      (if (ground? (car lst-src))
	(ufl-analyze-list (cdr lst-src))
	(let ((fresh-var (var 'a*)))
	  (cons (cons fresh-var (car lst-src))
	    (ufl-analyze-list (cdr lst-src)))))
      ; lst-src is either null? or the end of an improper list
      (if (or (null? lst-src) (ground? lst-src))
	'()
	(cons (cons (var 'd*) lst-src) '())))))

      ; Given a proper or improper list lst,
      ; return a list in which some of the cells are replaced with
      ; the corresponding variables
      ; term-assoc is an assoc list of variables _to_ cells
      ; (note the reverse association!).
      ; We are guaranteed however that term-assoc is properly ordered.
(define ufl-rebuild-with-vars
  (lambda (term-assoc lst)
    (cond
      ((null? term-assoc) lst)
      ((pair? lst)
	(if (eq? (cdar term-assoc) (car lst))
	  (cons (caar term-assoc)
	    (ufl-rebuild-with-vars (cdr term-assoc) (cdr lst)))
	  (cons (car lst)
	    (ufl-rebuild-with-vars term-assoc (cdr lst)))))
      (else (caar term-assoc)))))

(define unify-free/list
  (lambda (t-var u-value subst)
    (let ((to-unify (ufl-analyze-list u-value)))
      (cond 
	((null? to-unify)		; u-value was totally ground
	  (extend-subst t-var u-value subst))
	((null? (cdr to-unify))	; only one non-ground component
	  (unify-free/any (caar to-unify) (cdar to-unify)
	    (extend-subst t-var (ufl-rebuild-with-vars to-unify u-value)
	      subst)))
	(else			; general case
	  (let loop ((subst
		       (unify-free/any (caar to-unify) (cdar to-unify)
			 (extend-subst t-var 
			   (ufl-rebuild-with-vars to-unify u-value)
			   subst)))
		      (to-unify (cdr to-unify)))
	    (and subst
	      (if (null? to-unify) subst
		(loop (unify (caar to-unify) (cdar to-unify) subst)
		  (cdr to-unify)))))))))
  )

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

; Using the properties of the unifier to do the proper garbage
; collection of logical vars

(test-check 'prune-subst-1
  (concretize
    (let-lv (x z dummy)
      (@ 
	(exists (y)
	  (== `(,x ,z ,y) `(5 9 ,x)))
	(lambda@ (fk subst) subst)
	initial-fk
	(unit-subst dummy 'dummy))))
  '((z.0 . 9) (x.0 . 5) (dummy.0 . dummy)))

(test-check 'prune-subst-2
  (concretize
    (let-lv (x dummy)
      (@ 
	(exists (y)
	  (== `(,x ,y) `((5 ,y) ,7)))
	(lambda@ (fk subst) subst)
	initial-fk
	(unit-subst dummy 'dummy))))
  '((a*.0 . 7) (x.0 5 a*.0) (dummy.0 . dummy)))

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
      (all
	(== t1 `(s ,x))
	(== t2 `(s ,y))
	(Rinf x y)))))
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
      (all
	(== t1 `(s (s ,x)))
	(== t2 `(s (s ,y)))
	(Rinf2 x y)))))

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

;(exit 0)

