;(load "plshared.ss")

(define-syntax let-values
  (syntax-rules ()
    [(_ (x ...) vs body0 body1 ...)
     (call-with-values (lambda () vs) (lambda (x ...) body0 body1 ...))]))

(define-syntax exists
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
	(let* ((expected expected-result)
		(produced tested-expression))
	  (or (equal? expected produced)
	    (error 'test-check
	      "Failed: ~s~%Expected: ~s~%Computed: ~s~%"
	      'tested-expression expected produced)))))))

(test-check 'test-@-lambda@
  (@ (lambda@ (x y z) (+ x (+ y z))) 1 2 3)
  6)

'(test-check 'test-@-lambda@
  (@ (lambda@ (x y z) (+ x (+ y z))) 1 2 3)
  42)
   


(define-record var (id) ())
(define var make-var)

; A framework to remove introduced variables beyond their scope.
; To make it removing variables easier, we consider the list
; of subst as a "stack". Before we add a new variable, we put a mark
; on the stack. Mark is a special variable binding, whose term is 
; the current subst. When we about to remove added variables after
; their scope is ended, we locate the mark (using eq?) and check that
; the term bound to the mark is indeed the subst after the mark.
; If it so, then the subst list wasn't perturbed, and we know that
; anything below the mark can't possibly contain the reference to the
; variable we're about to remove.

(define-syntax introduce-vars
  (syntax-rules ()
    [(_ () body) body]
    [(_ () body0 body1 body2 ...)
     (all body0 body1 body2 ...)]
    [(_ (id ...) body0 body1 ...)
     (let ([id (var 'id)] ...)
       (lambda@ (sk fk in-subst)
	 (@ (all body0 body1 ...)
            (lambda@ (fk subst) (@ sk fk (prune in-subst subst id ...)))
	   fk in-subst)))]))


; check if any of vars occur in a term
; perhaps we should use memq and eq when applied to vars ...
(define (occur-vars? term vars)
  (cond
    ((var? term) (memv term vars))
    ((pair? term) (or (occur-vars? (car term) vars)
		      (occur-vars? (cdr term) vars)))
    (else #f)))

; PRUNE IN-SUBST SUBST ID ....
; remove the bindings of ID ... from SUBST (by composing with the
; rest of subst). IN-SUBST is the mark.
; If we locate IN-SUBST in SUBST, we know that everything below the
; mark can't possibly contain ID ...

(define-syntax prune
  (syntax-rules ()
    [(_ in-subst subst) subst]
    [(_ in-subst subst id ...)
      (let ((vars (list id ...))
	     (do-subst
	      (lambda (clean to-remove to-subst)
		(let loop ((result clean) (to-subst to-subst))
		  (if (null? to-subst) result
		    (loop
		      (cons-if-real-commitment
			(commitment->var (car to-subst))
			(subst-in (commitment->term (car to-subst))
			  to-remove)
			result)
		      (cdr to-subst)))))))
	(if (eq? subst in-subst) subst ; no bindings to remove
	  (let loop ((clean '()) (to-remove '())
		     (to-subst '()) (current subst))
	    (cond
	      ((eq? current in-subst)	; found the mark
		;(printf "found the mark~%")
		(do-subst (append clean current) to-remove to-subst))
	      ((null? current) 
		(do-subst clean to-remove to-subst))
	      ((memv (commitment->var (car current)) vars)
		(loop clean (cons (car current) to-remove) to-subst 
		  (cdr current)))
	      ((occur-vars? (commitment->term (car current)) vars)
		(loop clean to-remove (cons (car current) to-subst)
		  (cdr current)))
	      (else
		(loop (cons (car current) clean) to-remove to-subst
		  (cdr current)))))))]))


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
    (if (and (var? t) (eqv? t _)) empty-subst (list (commitment var t)))))

(define compose-subst
  (lambda (base refining)
    (let refine ([base base] [survivors refining])
      (cond
        [(null? base) survivors]
        [else (cons-if-real-commitment
                (commitment->var (car base))
                (subst-in (commitment->term (car base)) refining)
                (refine (cdr base)
                  (cond
                    [(assv (commitment->var (car base)) survivors)
                     => (lambda (c) (remv c survivors))]
                    [else survivors])))]))))

(define extend-subst
  (lambda (unbound-var contains-no-bound-vars subst)
    (cons (commitment unbound-var contains-no-bound-vars) subst)))

(define cons-if-real-commitment
  (lambda (var term subst)
    (cond
      [(eqv? term var) subst]
      [else (cons (commitment var term) subst)])))

(define subst-in  ;;; This definition will change several times.
  (lambda (t subst)
    (cond
      [(var? t)
       (cond
         [(assv t subst) => commitment->term]
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
    (or (eqv? t u)
        (and (string? t) (string? u) (string=? t u))
        (eqv? t _)
        (eqv? u _))))

(define _ (exists (_) _))

(test-check 'test-nonrecursive-unify
  (exists (x y)
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
    (lambda@ (sk fk subst cutk)
      (cond
        [(unify x y subst)
         => (lambda (subst)
              (@ sk fk subst cutk))]
        [else (fk)]))))

(define-syntax ==
  (syntax-rules ()
    [(_ t u)
     (lambda@ (sk fk subst cutk)
       (cond
         [(unify t u subst)
          => (lambda (subst)
               (@ sk fk subst cutk))]
         [else (fk)]))]))

;(load "plprelims.ss")

;  Fk  = () -> Ans
;  Cutk = Fk
;  Ans =  Nil + [Subst,Fk]
;  Sk = Fk -> Subst -> Cutk -> Ans  
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

(define-syntax concretize-sequence
  (syntax-rules ()
    [(_ t0 ...) (concretize-sequence-aux '() t0 ...)]))

(define-syntax concretize-sequence-aux
  (syntax-rules ()
    [(_ env) '()]
    [(_ env t0 t1 ...)
     (let-values (ct new-env) (concretize-term t0 env)
       (cons ct (concretize-sequence-aux new-env t1 ...)))]))

(define concretize-var    ;;; returns two values
  (lambda (var env)
    (cond
      [(assv var env)
       => (lambda (var-c)
            (values (artificial-id var-c) env))]
      [else (let ([var-c `(,var . ,(cond
                                     [(assv/var-id (var-id var) env)
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

(define assv/var-id
  (lambda (id env)
    (cond
      [(null? env) #f]
      [(eqv? (var-id (caar env)) id) (car env)]
      [else (assv/var-id id (cdr env))])))

(define-syntax trace-lambda@
  (syntax-rules ()
    [(_ id () body0 body1 ...) (begin body0 body1 ...)]
    [(_ id (formal0 formal1 ...) body0 body1 ...)
     (trace-lambda id (formal0)
       (trace-lambda@ id (formal1 ...) body0 body1 ...))]))

(define empty-subst? null?)

(exists (x y)
  (test-check 'test-compose-subst-0
    (append (unit-subst x y) (unit-subst y 52))
    `(,(commitment x y) ,(commitment y 52))))


(test-check 'test-compose-subst-1
  (exists (x y)
    (equal?
      (compose-subst (unit-subst x y) (unit-subst y 52))
      `(,(commitment x 52) ,(commitment y 52))))
  #t)

(test-check 'test-compose-subst-2
  (exists (w x y)
    (equal?
      (let ([s (compose-subst (unit-subst y w) (unit-subst w 52))])
	(compose-subst (unit-subst x y) s))
      `(,(commitment x 52) ,(commitment y 52) ,(commitment w 52))))
  #t)

(test-check 'test-compose-subst-3
  (exists (w x y)
    (equal?
      (let ([s (compose-subst (unit-subst w 52) (unit-subst y w))])
	(compose-subst (unit-subst x y) s))
      `(,(commitment x w) ,(commitment w 52) ,(commitment y w))))
  #t)

(test-check 'test-compose-subst-4
  (exists (x y z)
    (equal?
      (let ([s (compose-subst (unit-subst y z) (unit-subst x y))]
	    [r (compose-subst
		 (compose-subst (unit-subst x 'a) (unit-subst y 'b))
		 (unit-subst z y))])
	(compose-subst s r))
      `(,(commitment x 'b) ,(commitment z y))))
  #t)


(define initial-fk (lambda () '()))
(define initial-cutk initial-fk)
(define initial-sk (lambda@ (fk subst cutk)
		     ;(pretty-print subst)
		     (cons (cons subst cutk) fk)))

(define-syntax binary-extend-relation
  (syntax-rules ()
    [(_ (id ...) rel-exp1 rel-exp2)
     (let ([rel1 rel-exp1] [rel2 rel-exp2])
       (lambda (id ...)
         (lambda@ (sk fk subst cutk)
           (@ (rel1 id ...)
              sk
              (lambda () (@ (rel2 id ...) sk fk subst cutk))
              subst
              cutk))))]))

;;; one thing suspicious about this code is that it needs both
;;; relations to return before it ever enters interleave, so
;;; if the first one goes into an infinite loop before the other
;;; then we have a problem.  I don't know if that is related
;;; to the problem, or not.

(define-syntax binary-extend-relation-interleave
  (syntax-rules ()
    [(_ (id ...) rel-exp1 rel-exp2)
     (let ([rel1 rel-exp1] [rel2 rel-exp2])
       (lambda (id ...)
         (lambda@ (sk fk subst cutk)
           (let ([ant1 (rel1 id ...)] [ant2 (rel2 id ...)])
             ((interleave sk fk (finish-interleave sk fk))
              (@ ant1 initial-sk initial-fk subst cutk)
              (@ ant2 initial-sk initial-fk subst cutk))))))]))

(define finish-interleave
  (lambda (sk fk)
    (letrec
      ([finish
         (lambda (q)
           (cond
             [(null? q) (fk)]
             [else (let ([fk (cdr q)] [subst (caar q)] [cutk (cdar q)])
                     (@ sk (lambda () (finish (fk))) subst cutk))]))])
      finish)))

(define interleave
  (lambda (sk fk finish)
    (letrec
      ([interleave
         (lambda (q1 q2)
           (cond
             [(null? q1) (if (null? q2) (fk) (finish q2))]
             [else (let ([fk (cdr q1)] [subst (caar q1)] [cutk (cdar q1)])
                     (@ sk (lambda () (interleave q2 (fk))) subst cutk))]))])
      interleave)))

(define-syntax binary-extend-relation-interleave-non-overlap
  (syntax-rules ()
    [(_ (id ...) rel-exp1 rel-exp2)
     (let ([rel1 rel-exp1] [rel2 rel-exp2])
       (lambda (id ...)
         (lambda@ (sk fk subst cutk)
           (let ([ant1 (rel1 id ...)][ant2 (rel2 id ...)])
             ((interleave-non-overlap sk fk)
              (@ ant1 initial-sk initial-fk subst cutk)
              (@ ant2 initial-sk initial-fk subst cutk)
                  ; means in case of overlap, prefer ant2 over ant1
              fail
              ant2)))))]))

(define interleave-non-overlap
  (lambda (sk fk)
    (letrec
      ([finish
         (lambda (q)
           (cond
             [(null? q) (fk)]
             [else (let ([fk (cdr q)] [subst (caar q)] [cutk (cdar q)])
                     (@ sk (lambda () (finish (fk))) subst cutk))]))]
       [interleave
         (lambda (q1 q2 ant1 ant2)
           (cond
             [(null? q1) (if (null? q2) (fk) (finish q2))]
             [else (let ([fk (cdr q1)] [subst (caar q1)] [cutk (cdar q1)])
		(if (satisfied? ant2 subst) ; the solution of q1
   					    ; satisfies ant2. Skip it
		  (interleave q2 (fk) ant2 ant1)
		  (@ sk (lambda () (interleave q2 (fk) ant2 ant1)) subst cutk)))]))])
      interleave)))

(define (satisfied? ant subst)
  (not (null? (@ ant initial-sk initial-fk subst initial-fk))))

(define-syntax extend-relation
  (syntax-rules ()
    [(_ (id ...) rel-exp) rel-exp]
    [(_ (id ...) rel-exp0 rel-exp1 rel-exp2 ...)
     (binary-extend-relation (id ...) rel-exp0
       (extend-relation (id ...) rel-exp1 rel-exp2 ...))]))

(define-syntax all
  (syntax-rules ()
    [(_) (lambda (sk) sk)]
    [(_ ant) ant]
    [(_ ant0 ant1 ant2 ...)
     (lambda@ (sk)
       (ant0 (splice-in-ants/all sk ant1 ant2 ...)))]))

(define-syntax splice-in-ants/all
  (syntax-rules ()
    [(_ sk ant) (ant sk)]
    [(_ sk ant0 ant1 ...)
     (ant0 (splice-in-ants/all sk ant1 ...))]))

(define-syntax all!
  (syntax-rules ()
    [(_) (lambda (sk) sk)]
    [(_ ant) ant]
    [(_ ant0 ant1 ant2 ...)
     (lambda@ (sk fk)
       (@ ant0 (splice-in-ants/all! sk fk ant1 ant2 ...) fk))]))

(define-syntax splice-in-ants/all!
  (syntax-rules ()
    [(_ sk fk ant)
     (lambda (ign-fk)
       (@ ant sk fk))]
    [(_ sk fk ant0 ant1 ...)
     (lambda (ign-fk)
       (@ ant0 (splice-in-ants/all! sk fk ant1 ...) fk))]))

(define-syntax relation
  (syntax-rules (to-show)
    [(_  (ex-id ...) (to-show x ...) ant ...)
     (relation (ex-id ...) () (x ...) (x ...) ant ...)]
    [(_ (ex-id ...) (g ...) () (x ...))
     (lambda (g ...)
       (introduce-vars (ex-id ...)
	 (all! (== g x) ...)))]
    [(_ (ex-id ...) (g ...) () (x ...) ant ...)
     (lambda (g ...)
       (introduce-vars (ex-id ...)
	 (all! (== g x) ... (all ant ...))))]
    [(_ ex-ids (var ...) (x0 x1 ...) xs ant ...)
     (relation ex-ids (var ... g) (x1 ...) xs ant ...)]))

(define-syntax relation/cut
  (syntax-rules (to-show)
    [(_ cut-id (ex-id ...) (to-show x ...) ant ...)
     (relation/cut cut-id (ex-id ...) () (x ...) (x ...) ant ...)]
    [(_ cut-id (ex-id ...) (g ...) () (x ...))
     (lambda (g ...)
       (introduce-vars (ex-id ...)
	 (all! (== g x) ...)))]
    [(_ cut-id (ex-id ...) (g ...) () (x ...) ant ...)
     (lambda (g ...)
       (introduce-vars (ex-id ...)
         (all! (== g x) ...
           (lambda@ (sk fk subst cutk)
             (let ([cut-id (!! cutk)])
               (@ (all ant ...) sk fk subst cutk))))))]
    [(_ cut-id ex-ids (var ...) (x0 x1 ...) xs ant ...)
     (relation/cut cut-id ex-ids (var ... g) (x1 ...) xs ant ...)]))

(define-syntax fact
  (syntax-rules ()
    [(_ (ex-id ...) x ...)
     (relation (ex-id ...) (to-show x ...))]))

(define !!
  (lambda (exiting-fk)
    (lambda@ (sk fk)
      (@ sk exiting-fk))))

; (define initial-fk (lambda () '()))
; (define initial-sk
;   (lambda@ (fk subst cutk)
;     (cons (cons subst cutk) fk)))

;;;;; Starts the real work of the system.

(define father  
  (relation ()
    (to-show 'john 'sam)))

(test-check 'test-father0
  (let ([result
          (@ (father 'john 'sam)
             initial-sk initial-fk empty-subst initial-fk)])
    (and
      (equal? (caar result) '())
      (equal? ((cdr result)) '())))
  #t)

;;; Now we need concretize-subst about here.

(define child-of-male
  (relation (child dad)
    (to-show child dad)
    (father dad child)))

(test-check 'test-child-of-male-0
  (concretize-subst
    (caar (@ (child-of-male 'sam 'john)
	    initial-sk initial-fk empty-subst initial-fk)))
  ;`(,(commitment 'child.0 'sam) ,(commitment 'dad.0 'john)))))
  '())  ; variables shouldn't leak


; The mark should be found here...
(define child-of-male-1
  (relation (child dad)
    (to-show child dad)
    (child-of-male dad child)))
(test-check 'test-child-of-male-1
  (concretize-subst
    (caar (@ (child-of-male 'sam 'john)
	    initial-sk initial-fk empty-subst initial-fk)))
  ;`(,(commitment 'child.0 'sam) ,(commitment 'dad.0 'john)))))
  '())


(define pete/sal
  (relation ()
    (to-show 'pete 'sal)))

(define new-father
  (extend-relation (a1 a2) father pete/sal))

(test-check 'test-father-1
  (let ([result
	  (@ (new-father 'pete 'sal)
	    initial-sk initial-fk empty-subst initial-fk)])
    (and
      (equal? (caar result) '())
      (equal? ((cdr result)) '())))
  #t)


(define query
  (let ([initial-fk (lambda () '())]
        [initial-sk (lambda@ (fk subst cutk) (cons (cons subst cutk) fk))])
    (lambda (antecedent)
      (@ antecedent initial-sk initial-fk empty-subst initial-fk))))

(test-check 'test-father-2
  (exists (x)
    (let ([result (query (new-father 'pete x))])
      (and
	(equal? (caar result) `(,(commitment x 'sal)))
	(equal? ((cdr result)) '()))))
  #t)

(test-check 'test-father-3
  (exists (x)
    (equal?
      (let ([answer (query (new-father 'pete x))])
	(let ([subst (caar answer)])
	  (concretize-sequence (subst-in 'pete subst) (subst-in x subst))))
        '(pete sal)))
  #t)

(test-check 'test-father-4
  (exists (x y)
    (equal?
      (let ([answer (query (new-father x y))])
	(let ([subst (caar answer)])
	  (concretize-sequence (subst-in x subst) (subst-in y subst))))
      '(john sam)))
  #t)

(define pete/pat
  (relation ()
    (to-show 'pete 'pat)))

(define newer-father
  (extend-relation (a1 a2) new-father pete/pat))

(test-check 'test-father-5
  (exists (x)
    (and
      (equal?
	(let ([answer1 (query (newer-father 'pete x))])
	  (pretty-print answer1)
	  (let ([subst (caar answer1)])
	    (list
	      (concretize-sequence
		(subst-in 'pete subst) (subst-in x subst))
	      (let ([answer2 ((cdr answer1))])
		(pretty-print answer2)
		(let ([subst (caar answer2)])
		  (concretize-sequence
		    (subst-in 'pete subst) (subst-in x subst)))))))
	'((pete sal) (pete pat)))
      (equal?
	(let ([answer1 (query (newer-father 'pete x))])
	  (let ([subst (caar answer1)])
	    (cons
	      (concretize-sequence
		(subst-in 'pete subst) (subst-in x subst))
	      (let ([answer2 ((cdr answer1))])
		(let ([subst (caar answer2)])
		  (cons
		    (concretize-sequence
		      (subst-in 'pete subst) (subst-in x subst))
		    (let ([answer3 ((cdr answer2))])
		      (if (null? answer3)
			'()
			(let ([subst (car answer3)])
			  (cons
			    (concretize-sequence
			      (subst-in 'pete subst) (subst-in x subst))
			    '()))))))))))
	'((pete sal) (pete pat)))))
  #t)
      
(define stream-prefix
  (lambda (n strm)
    (if (null? strm) '()
      (cons (car strm)
        (if (zero? n) '()
          (stream-prefix (- n 1) ((cdr strm))))))))

(define-syntax solve
  (syntax-rules ()
    [(_ n (rel t0 ...))
     (map (lambda (subst/cutk)
	    ;(pretty-print (car subst/cutk))
            (concretize-sequence (subst-in t0 (car subst/cutk)) ...))
       (stream-prefix (- n 1) (query (rel t0 ...))))]))

(define sam/pete
  (relation ()
    (to-show 'sam 'pete)))

(define newest-father (extend-relation (a1 a2) newer-father sam/pete))

(test-check 'test-father-6/solve
  (exists (x y)
    (and
      (equal?
	(solve 5 (newest-father 'pete x))
	'((pete sal) (pete pat)))
      (equal?
	(solve 6 (newest-father x y))
	'((john sam) (pete sal) (pete pat) (sam pete)))))
  #t)
            

(define-syntax binary-intersect-relation
  (syntax-rules ()
    [(_ (id ...) rel-exp1 rel-exp2)
     (let ([rel1 rel-exp1] [rel2 rel-exp2])
       (lambda (id ...)
         (lambda (sk)
           ((rel1 id ...) ((rel2 id ...) sk)))))]))

(define-syntax binary-intersect-relation
  (syntax-rules ()
    [(_ (id ...) rel-exp1 rel-exp2)
     (let ([rel1 rel-exp1] [rel2 rel-exp2])
       (lambda (id ...)
         (lambda@ (sk fk subst cutk)
           (@ (rel1 id ...)
              (lambda@ (fk subst cutk)
                (@ (rel2 id ...) sk fk subst cutk))
              fk subst cutk))))]))

(define fathers-of-cubscouts
  (extend-relation (a1 a2)
    (fact () 'sam 'bob)
    (fact () 'tom 'adam)
    (fact () 'tad 'carl)))

(define fathers-of-little-leaguers
  (extend-relation (a1 a2)
    (fact () 'sam 'bobo)
    (fact () 'tom 'adam)
    (fact () 'tad 'carl)))

(define busy-fathers
  (binary-intersect-relation (a1 a2) 
    fathers-of-cubscouts fathers-of-little-leaguers))

(test-check 'test-busy-fathers
  (exists (x y)
    (solve 5 (busy-fathers x y)))
  '((tom adam) (tad carl)))
            

(define-syntax intersect-relation
  (syntax-rules ()
    [(_ (id ...) rel-exp) rel-exp]
    [(_ (id ...) rel-exp0 rel-exp1 rel-exp2 ...)
     (binary-intersect-relation (id ...) rel-exp0
       (intersect-relation (id ...) rel-exp1 rel-exp2 ...))]))

(define busy-fathers
  (intersect-relation (a1 a2) fathers-of-cubscouts fathers-of-little-leaguers))

(define conscientious-fathers
  (extend-relation (a1 a2) fathers-of-cubscouts fathers-of-little-leaguers))

(test-check 'test-conscientious-fathers
  (exists (x y)
    (solve 7 (conscientious-fathers x y)))
  '((sam bob) (tom adam) (tad carl) (sam bobo) (tom adam) (tad carl)))


(define-syntax solution
  (syntax-rules ()
    [(_ x)
     (let ([ls (solve 1 x)])
       (if (null? ls) #f (car ls)))]))

(test-check 'test-father-7/solution
  (exists (x) (solution (newest-father 'pete x)))
  '(pete sal))


(define grandpa-sam
  (relation (grandchild)
    (to-show grandchild)
    (exists (parent)
      (lambda (sk)
        ((newest-father 'sam parent)
         ((newest-father parent grandchild) sk))))))

(test-check 'test-grandpa-sam-1
  (exists (y)
    (solve 6 (grandpa-sam y)))
  '((sal) (pat)))


(define-syntax any
  (syntax-rules ()
    [(_) (lambda@ (sk fk subst cutk) (fk))]
    [(_ ant) ant]
    [(_ ant0 ant1 ...)
     (lambda@ (sk fk subst cutk)
       (letrec-syntax
         ([splice-in-ants 
            (syntax-rules ()
              [(_) fk]
              [(_ ant . other-ants)
               (lambda ()
                 (@ ant sk (splice-in-ants . other-ants) subst cutk))])])
         (@ ant0 sk (splice-in-ants ant1 ...) subst cutk)))]))

(define-syntax any
  (syntax-rules ()
    [(_ ant ...)
     ((extend-relation () (relation () (to-show) ant) ...))]))

(define child
  (relation (child dad)
    (to-show child dad)
    (newest-father dad child)))

(test-check 'test-child-1
  (exists (x y)
    (solve 10 (child x y)))
  '((sam john) (sal pete) (pat pete) (pete sam)))

(define grandpa-sam
  (relation (grandchild)
    (to-show grandchild)
    (exists (parent)
      (all
        (newest-father 'sam parent)
        (newest-father parent grandchild)))))

(test-check 'test-grandpa-sam-2
  (exists (y)
    (solve 6 (grandpa-sam y)))
  '((sal) (pat)))


(define grandpa-maker
  (lambda (grandad)
    (relation (grandchild)
      (to-show grandchild)
      (exists (parent)
        (all
          (newest-father grandad parent)
          (newest-father parent grandchild))))))

(test-check 'test-grandpa-maker-1
  (exists (x)
    (solve 6 ((grandpa-maker 'sam) x)))
  '((sal) (pat)))


(define grandpa-maker
  (lambda (guide* grandad*)
    (relation (grandchild)
      (to-show grandchild)
      (exists (parent)
        (all
          (guide* grandad* parent)
          (guide* parent grandchild))))))

(test-check 'test-grandpa-maker-2
  (exists (x)
    (solve 4 ((grandpa-maker newest-father 'sam) x)))
  '((sal) (pat)))


(define grandpa
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (newest-father grandad parent)
        (newest-father parent grandchild)))))

(test-check 'test-grandpa-1
  (exists (x)
    (solve 4 (grandpa 'sam x)))
  '((sam sal) (sam pat)))


(define-syntax fact
  (syntax-rules ()
    [(_ (var ...) x ...) (relation (var ...) (to-show x ...))]))

(define-syntax trace-fact
  (syntax-rules ()
    [(_ id (var ...) x ...) (trace-relation id (to-show (var ...) x ...))]))

(define father
  (extend-relation (a1 a2)
    (fact () 'john 'sam)
    (extend-relation (a1 a2)
      (fact () 'sam 'pete)
      (extend-relation (a1 a2)
        (fact () 'sam 'polly)
        (extend-relation (a1 a2)
          (fact () 'pete 'sal)
          (fact () 'pete 'pat))))))

(define mother
  (extend-relation (a1 a2)
    (fact () 'polly 'betty)
    (fact () 'polly 'david)))

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
  (exists (x y)
    (solve 10 (grandpa 'sam y)))
  '((sam sal) (sam pat) (sam betty) (sam david)))


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
  (exists (x y)
    (solve 10 (grandpa 'sam y)))
  '((sam sal) (sam pat) (sam betty) (sam david)))


'(define grandpa-sam
  (let ([r (relation (child)
             (to-show child)
             (exists (parent)
               (all
                 (father 'sam parent)
                 (father parent child))))])
    (relation (child)
      (to-show child)
      (r child))))

'(define test-grandpa-sam-4
  (lambda ()
    (exists (y)
      (equal?
        (solve 6 (grandpa-sam y))
        '((sal) (pat))))))

;(printf "~s ~s~%" 'test-grandpa-sam-4 (test-grandpa-sam-4))  

(define grandpa/father
  (relation/cut cut (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (father parent grandchild)
        cut))))

(define grandpa/mother
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (mother parent grandchild)))))

(define grandpa
  (extend-relation (a1 a2) grandpa/father grandpa/mother))

(test-check 'test-grandpa-8
  (exists (x y)
    (solve 10 (grandpa x y)))
  '((john pete)))


(define grandpa/father
  (relation/cut cut (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all cut (father grandad parent) (father parent grandchild)))))

(define grandpa
  (extend-relation (a1 a2) grandpa/father grandpa/mother))

(test-check 'test-grandpa-10
  (exists (x y)
    (solve 10 (grandpa x y)))
    '((john pete) (john polly) (sam sal) (sam pat)))


(define fail
  (lambda@ (sk fk subst cutk) (fk)))

(define no-grandma
  (relation/cut cut (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all (mother grandad parent) cut fail))))

(define no-grandma-grandpa
  (extend-relation (a1 a2) no-grandma grandpa))

(test-check 'test-no-grandma-grandpa-1
  (exists (x)
    (solve 1 (no-grandma-grandpa 'polly x)))
  '())


(define-syntax pred-call
  (syntax-rules ()
    [(_ p t ...)
     (lambda@ (sk fk subst cutk)
       (if ((nonvar! (subst-in p subst)) (nonvar! (subst-in t subst)) ...)
         (@ sk fk subst cutk)
         (fk)))]))

(define-syntax pred-call/no-check
  (syntax-rules ()
    [(_ p t ...)
     (lambda@ (sk fk subst cutk)
       (if ((subst-in p subst) (subst-in t subst) ...)
         (@ sk fk subst cutk)
         (fk)))]))

(define-syntax fun-call
  (syntax-rules ()
    [(_ f t u ...)
     (lambda@ (sk fk subst cutk)
       (cond
         [(unify t ((nonvar! (subst-in f subst)) 
		    (nonvar! (subst-in u subst)) ...) subst)
          => (lambda (subst)
               (@ sk fk subst cutk))]
         [else (fk)]))]))

(define-syntax fun-call/no-check
  (syntax-rules ()
    [(_ f t u ...)
     (lambda@ (sk fk subst cutk)
       (cond
         [(unify t ((subst-in f subst) (subst-in u subst) ...) subst)
          => (lambda (subst)
               (@ sk fk subst cutk))]
         [else (fk)]))]))

(define nonvar!
  (lambda (t)
    (if (var? t)
      (error 'nonvar! "Variable found in call: ~s"
        (let-values (cvar env) (concretize-var t '()) cvar))
      t)))

(define grandpa
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all 
        (father grandad parent)
        (pred-call starts-with-p? parent)
        (father parent grandchild)))))

(define starts-with-p?
  (lambda (x)
    (and
      (symbol? x)
      (string=? (string (string-ref (symbol->string x) 0)) "p"))))

(test-check 'test-grandpa-11
  (exists (x y)
    (solve 10 (grandpa x y)))
  '((sam sal) (sam pat)))


(define check
  (lambda (id f)
    (lambda term
      (if (not (procedure? f))
          (error id "Non-procedure found: ~s" f))
      (if (ormap var? term)
          (error id "Variable found: ~s" term))
      (apply f term))))

(test-check 'test-grandpa-12
  (exists (x y)
    (solve 10 (grandpa x y)))
  '((sam sal) (sam pat)))


(define fun    
  (lambda (f)
    (fun-nocheck (check 'fun f))))

(test-check 'test-fun-*  
  (exists (q)
    (solve 3 (fun-call * q 3 5)))
  `((,* 15 3 5)))


(define test1
  (lambda (x)
    (any (pred-call < 4 5) (fun-call < x 6 7))))

;;;; Here is the definition of concretize.

(define concretize
  (lambda (t)
    (let-values (ct new-env) (concretize-term t '())
      ct)))

(test-check 'test-test1
  (exists (x)
    (equal?
      (solution (test1 x))
      `(,(concretize x))))
  #t)

(define test2
  (lambda (x)
    (any (pred-call < 5 4) (fun-call < x 6 7))))

(test-check 'test-test2
  (exists (x)
    (solution (test2 x)))
  '(#t))

(define test3
  (lambda (x y)
    (any (fun-call < x 5 4) (fun-call < y 6 7))))

(test-check 'test-test3
  (exists (x y)
    (equal?
      (solution (test3 x y))
      `(#f ,(concretize y))))
  #t)


(define fails
  (lambda (ant)
    (lambda@ (sk fk subst cutk)
      (@ ant
        (lambda@ (current-fk subst cutk) (fk))
        (lambda () (@ sk fk subst cutk))
        subst cutk))))

(define grandpa
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (fails (pred-call starts-with-p? parent))
        (father parent grandchild)))))

(test-check 'test-grandpa-13
  (exists (x y)
    (solve 10 (grandpa x y)))
  '((john pete) (john polly)))


(define instantiated
  (lambda (t)
    (pred-call/no-check (lambda (x) (not (var? x))) t)))

(define view-subst
  (lambda (t)
    (lambda@ (sk fk subst cutk)
      (pretty-print (subst-in t subst))
      (pretty-print (concretize-subst subst))
      (@ sk fk subst cutk))))

(define grandpa
  (relation (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (father parent grandchild)
        (view-subst grandchild)))))

(test-check 'test-grandpa-14/view-subst
  (exists (x y)
    (equal?
      (solve 10 (grandpa x y))
      (begin
	'pete
	'((grandad.0 x.0)
	   (grandchild.0 y.0)
	   (x.0 john)
	   (parent.0 sam)
	   (y.0 pete))
	'polly
	'((grandad.0 x.0)
	   (grandchild.0 y.0)
	   (x.0 john)
	   (parent.0 sam)
	   (y.0 polly))
	'sal 
	'((grandad.0 x.0)
	   (grandchild.0 y.0)
	   (x.0 sam)
	   (parent.0 pete)
	   (y.0 sal))
	'pat
	'((grandad.0 x.0)
	   (grandchild.0 y.0)
	   (x.0 sam)
	   (parent.0 pete)
	   (y.0 pat))
	'((john pete) (john polly) (sam sal) (sam pat)))))
  #t)


(define father
  (extend-relation (a1 a2) father
    (extend-relation (a1 a2) (fact () 'john 'harry)
      (extend-relation (a1 a2) (fact () 'harry 'carl) (fact () 'sam 'ed)))))

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
  (exists (x)
    (solve 21 (ancestor 'john x)))
  '((john sam)
    (john harry)
    (john pete)
    (john polly)
    (john ed)
    (john sal)
    (john pat)
    (john carl)))

(define common-ancestor
  (relation (young-a young-b old)
    (to-show young-a young-b old)
    (all
      (ancestor old young-a)
      (ancestor old young-b))))

(test-check 'test-common-ancestor
  (exists (x)
    (solve 4 (common-ancestor 'pat 'ed x)))
  '((pat ed john) (pat ed sam)))

(define younger-common-ancestor
  (relation (young-a young-b old not-so-old)
    (to-show young-a young-b old not-so-old)
    (all
      (common-ancestor young-a young-b not-so-old)
      (common-ancestor young-a young-b old)
      (ancestor old not-so-old))))

(test-check 'test-younger-common-ancestor
  (exists (x)
    (solve 4 (younger-common-ancestor 'pat 'ed 'john x)))
  '((pat ed john sam)))

(define youngest-common-ancestor
  (relation (young-a young-b not-so-old)
    (to-show young-a young-b not-so-old)
    (all
      (common-ancestor young-a young-b not-so-old)
      (exists (y)
        (fails (younger-common-ancestor young-a young-b not-so-old y))))))

(test-check 'test-youngest-common-ancestor
  (exists (x)
    (solve 4 (youngest-common-ancestor 'pat 'ed x)))
  '((pat ed sam)))

(test-check 'test-Seres-Spivey
  (let ([father
	  (lambda (dad child)
	    (any
	      (all (== dad 'john) (== child 'sam))
	      (all (== dad 'sam) (== child 'pete))
	      (all (== dad 'sam) (== child 'polly))
	      (all (== dad 'pete) (== child 'sal))
	      (all (== dad 'pete) (== child 'pat))
	      (all (== dad 'john) (== child 'harry))
	      (all (== dad 'harry) (== child 'carl))
	      (all (== dad 'sam) (== child 'ed))))])
    (letrec
      ([ancestor
	 (lambda (old young)
	   (any
	     (father old young)
	     (exists (not-so-old)
	       (all
		 (father old not-so-old)
		 (ancestor not-so-old young)))))])
      (exists (x) (solve 20 (ancestor 'john x)))))
  '((john sam)
    (john harry)
    (john pete)
    (john polly)
    (john ed)
    (john sal)
    (john pat)
    (john carl)))


(define towers-of-hanoi
  (letrec
      ([move
         (extend-relation (a1 a2 a3 a4)
           (relation/cut cut ()
             (to-show 0 _ _ _)
             cut)
           (relation (n a b c)
             (to-show n a b c)
             (exists (m)
               (all
                 (pred-call positive? n)
                 (fun-call - m n 1)
                 (move m a c b)
                 (pred-call printf "Move a disk from ~s to ~s~n" a b)
                 (move m c b a)))))])
    (relation (n)
      (to-show n)
      (move n 'left 'middle 'right))))

(begin
  (printf "~s with 3 disks~n~n" 'test-towers-of-hanoi)
  (solution (towers-of-hanoi 3))
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
         [(assv t subst) => commitment->term]
         [else t])]
      [(pair? t)
       (cons
         (subst-in (car t) subst)
         (subst-in (cdr t) subst))]
      [else t])))

(test-check 'test-compose-subst-5
  (exists (x y z)
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
      [(var? term) (eqv? term var)]
      [(pair? term) (or (occurs? var (car term)) (occurs? var (cdr term)))]
      [else #f])))

(test-check 'test-unify/pairs
  (exists (w x y z u)
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
      (exists (x0 x1 y0 y1)
        (pretty-print
          (concretize-subst
            (unify
              `(h ,x1 (f ,y0 ,y0) ,y1)
              `(h (f ,x0 ,x0) ,y1 ,x1)
              empty-subst)))
        (newline))

      (exists (x0 x1 x2 y0 y1 y2)
        (pretty-print
          (concretize-subst
            (unify
              `(h ,x1 ,x2 (f ,y0 ,y0) (f ,y1 ,y1) ,y2)
              `(h (f ,x0 ,x0) (f ,x1 ,x1) ,y1 ,y2 ,x2)
              empty-subst)))
        (newline))

      (exists (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4)
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
	       (all
		 (fun-call (lambda () 4) x)
		 (fun-call (lambda () 3) w)
		 (fun-call (lambda (y) (cons x y)) z w)))])
      (exists (q) (solve 4 (j q)))))
  '(((4 . 3))))


(define towers-of-hanoi-path
  (let ([steps '()])
    (let ([push-step (lambda (x y) (set! steps (cons `(,x ,y) steps)))])
      (letrec
        ([move
           (extend-relation (a1 a2 a3 a4)
             (relation/cut cut ()
               (to-show 0 _ _ _)
               cut)
             (relation (n a b c)
               (to-show n a b c)
               (exists (m)
                 (all
                   (pred-call positive? n)
                   (fun-call - m n 1)
                   (move m a c b)
                   (pred-call push-step a b)
                   (move m c b a)))))])
        (relation (n path)
          (to-show n path)
          (begin
            (set! steps '())
            (any
              (fails (move n 'l 'm 'r))
              (== path (reverse steps)))))))))

(test-check 'test-towers-of-hanoi-path
  (exists (path)
    (solution (towers-of-hanoi-path 3 path)))
  '(3 ((l m) (l r) (m r) (l m) (r l) (r m) (l m))))


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
      [(assv t-var subst) (unify (subst-in t-var subst) u subst)] 
      [(occurs? t-var u) #f]
      [else (compose-subst subst (unit-subst t-var u))])))

(test-check 'test-unify/pairs-lazy
  (exists (w x y z u)
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
	       (all
		 (fun-call (lambda () 4) x)
		 (fun-call (lambda () 3) w)
		 (fun-call (lambda (y) (cons x y)) z w)))])
      (exists (q) (solve 4 (j q)))))
  '(((4 . 3))))

(test-check 'test-pathological-lazy
  (list
      (exists (x0 x1 y0 y1)
        (pretty-print
          (concretize-subst
            (unify
              `(h ,x1 (f ,y0 ,y0) ,y1)
              `(h (f ,x0 ,x0) ,y1 ,x1)
              empty-subst)))
        (newline))

      (exists (x0 x1 x2 y0 y1 y2)
        (pretty-print
          (concretize-subst
            (unify
              `(h ,x1 ,x2 (f ,y0 ,y0) (f ,y1 ,y1) ,y2)
              `(h (f ,x0 ,x0) (f ,x1 ,x1) ,y1 ,y2 ,x2)
              empty-subst)))
        (newline))

      (exists (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4)
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
         [(assv t subst) =>
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
         [(assv t subst)
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
      [(trivially-equal? t u) subst]
      [(var? t) (if (var? u) (unify-var/var t u subst) (unify-var/value t u subst))]
      [(var? u) (unify-var/value u t subst)]
      [(and (pair? t) (pair? u))
       (cond
         [(unify (car t) (car u) subst)
          => (lambda (car-subst)
               (unify (cdr t) (cdr u) car-subst))]
         [else #f])]
      [else #f])))

(define unify-var/var
  (lambda (t-var u-var s)
    (cond
;       [(assv t-var s)
;        => (lambda (ct) ;;; This is bound/var
;             (let ([t-term (commitment->term ct)])
;               (unify u-var t-term s)))]
      
      [(assv t-var s)
       => (lambda (ct) ;;; This is bound/var
            (cond
              [(assv u-var s)
               => (lambda (cu)
                    (let ([u-term (commitment->term cu)]
                          [t-term (commitment->term ct)])
                      (unify t-term u-term s)))]
              [else ((unbound/bound u-var s) ct)]))]
;     [(assv u-var s) ;;; This is bound/unbound.
;      => (lambda (cu)
;           (let ([u-term (commitment->term cu)])
;             (compose-subst (unit-subst t-var u-term) s)))]
      [(assv u-var s) => (unbound/bound t-var s)]
      [else (extend-subst t-var u-var s)])))

(define unbound/bound
  (lambda (t-var s)
    (lambda (cu)
      (let loop ([cm cu])
        (let ([u-term (commitment->term cm)])
          (cond
            [(eqv? u-term t-var) s]
            [(var? u-term)
             (cond
               [(assv u-term s) => loop]
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

(define unify-var/value
  (lambda (t-var u-value s)
    (cond
      [(assv t-var s)
       => (lambda (ct)
            (let ([t-term (commitment->term ct)]) 
              (unify t-term u-value s)))]
      [(pair? u-value)
       (let ([car-var (var '*a)]
             [cdr-var (var '*d)])
         (cond
           [(unify car-var (car u-value)
              (extend-subst t-var (cons car-var cdr-var) s))
            => (lambda (s)
                 (unify cdr-var (cdr u-value) s))]
           [else #f]))]
      [else (extend-subst t-var u-value s)])))

;------------------------------------------------------------------------
(test-check 'test-unify/pairs-oleg
  (exists (w x y z u)
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
            `(,(commitment y 4) ,(commitment x 3)))
          (equal?
            (unify `(,x 4) `(3 ,y) empty-subst)
            `(,(commitment y 4) ,(commitment x 3))))
        (and
          (equal?
            (let ([s (normalize-subst
                       (unify `(,x 4 3 ,w) `(3 ,y ,x ,z) empty-subst))])
              (let ([vars (list w y x)])
                (map commitment
                  vars
                  (subst-vars-recursively vars s))))
            `(,(commitment w z)
              ,(commitment y 4)
              ,(commitment x 3)))
          (equal?
            (let ([s (normalize-subst
                       (unify `(,x 4) `(,y ,y) empty-subst))])
              (let ([vars (list y x)])
                (map commitment
                  vars
                  (subst-vars-recursively vars s))))
            `(,(commitment y 4) ,(commitment x 4)))
          (equal?
            (unify `(,x 4 3) `(,y ,y ,x) empty-subst)
            #f)
          (equal?
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
              ,(commitment x 8)))
          (equal?
            (let ([s (normalize-subst
                       (unify `(p (f a) (g ,x)) `(p ,x ,y) empty-subst))])
              (let ([vars (list y x)])
                (map commitment
                  vars
                  (subst-vars-recursively vars s))))
            `(,(commitment y '(g (f a)))
              ,(commitment x '(f a))))
          (equal?
            (let ([s (normalize-subst
                       (unify `(p (g ,x) (f a)) `(p ,y ,x) empty-subst))])
              (let ([vars (list x y)])
                (map commitment
                  vars
                  (subst-vars-recursively vars s))))
            `(,(commitment x '(f a))
              ,(commitment y '(g (f a)))))
          (equal?
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
              ,(commitment z 'a)))
          (equal?
            (concretize-subst ;;; was #f
              (let ([s (unify `(p ,x ,x) `(p ,y (f ,y)) empty-subst)])
                (let ([var (map commitment->var s)])
                  (map commitment
                    var
                    (subst-vars-recursively var s)))))
            `(,(commitment '*d.0 '())
              ,(commitment '*a.0 '(f *a.0))
              ,(commitment '*d.1 '((f . *d.1)))
              ,(commitment '*a.1 'f)
              ,(commitment 'y.0  '(f (f . *d.1)))
              ,(commitment 'x.0  '(f (f . *d.1)))))
          #t)))
  #t)

(test-check 'test-fun-resubst-oleg
  (concretize
    (let ([j (relation (x w z)
	       (to-show z)
	       (all
		 (fun-call (lambda () 4) x)
		 (fun-call (lambda () 3) w)
		 (fun-call (lambda (y) (cons x y)) z w)))])
      (exists (q) (solve 4 (j q)))))
  '(((4 . 3))))
          

;Baader & Snyder
(test-check 'test-pathological-oleg
  (list
    (exists (x0 x1 y0 y1)
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

    (exists (x0 x1 x2 y0 y1 y2)
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

    (exists (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4)
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

'(test-check 'test-fun-concat
  (exists (q)
    (solve 1 (fun-call concat q '(a b c) '(u v))))
    '(((a b c u v) (a b c) (u v))))

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
        (exists (q) (solve 6 (concat '(a b c) '(u v) q)))
        '(((a b c) (u v) (a b c u v))))
      (equal?
        (exists (q) (solve 6 (concat '(a b c) q '(a b c u v))))
        '(((a b c) (u v) (a b c u v))))
      (equal? 
        (exists (q) (solve 6 (concat q '(u v) '(a b c u v))))     
        '(((a b c) (u v) (a b c u v))))
      (equal? 
        (exists (q r) (solve 6 (concat q r '(a b c u v))))
        '((() (a b c u v) (a b c u v))
          ((a) (b c u v) (a b c u v))
          ((a b) (c u v) (a b c u v))
          ((a b c) (u v) (a b c u v))
          ((a b c u) (v) (a b c u v))
          ((a b c u v) () (a b c u v))))
      (equal?
        (exists (q r s) (solve 6 (concat q r s)))
	'((() xs.0 xs.0)
          ((x.0) xs.0 (x.0 . xs.0))
          ((x.0 x.1) xs.0 (x.0 x.1 . xs.0))
          ((x.0 x.1 x.2) xs.0 (x.0 x.1 x.2 . xs.0))
          ((x.0 x.1 x.2 x.3) xs.0 (x.0 x.1 x.2 x.3 . xs.0))
          ((x.0 x.1 x.2 x.3 x.4) xs.0 (x.0 x.1 x.2 x.3 x.4 . xs.0))))
      (equal?
        (exists (q r) (solve 6 (concat q '(u v) `(a b c . ,r))))
        '(((a b c) (u v) (a b c u v))
          ((a b c x.0) (u v) (a b c x.0 u v))
          ((a b c x.0 x.1) (u v) (a b c x.0 x.1 u v))
          ((a b c x.0 x.1 x.2) (u v) (a b c x.0 x.1 x.2 u v))
          ((a b c x.0 x.1 x.2 x.3) (u v) (a b c x.0 x.1 x.2 x.3 u v))
          ((a b c x.0 x.1 x.2 x.3 x.4)
           (u v)
           (a b c x.0 x.1 x.2 x.3 x.4 u v))))
      (equal?
        (exists (q) (solve 6 (concat q '() q)))
        '((() () ())
          ((x.0) () (x.0))
          ((x.0 x.1) () (x.0 x.1))
          ((x.0 x.1 x.2) () (x.0 x.1 x.2))
          ((x.0 x.1 x.2 x.3) () (x.0 x.1 x.2 x.3))
          ((x.0 x.1 x.2 x.3 x.4) () (x.0 x.1 x.2 x.3 x.4))))))
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
    [(infer g term type)
     (cond
       [(solution (!- g (parse term) type))
        => (lambda (result)
             `(!- ,(car result) ,(unparse (cadr result)) ,(caddr result)))]
       [else #f])]))

;;; This is environments.

(define non-generic-match-env
  (fact (g v t) `(non-generic ,v ,t ,g) v t))

(define non-generic-recursive-env
  (relation (g v t w type-w)
    (to-show `(non-generic ,w ,type-w ,g) v t)
    (all! (unequal? w v) (instantiated g) (env g v t))))

(define env (extend-relation (a1 a2 a3)
              non-generic-match-env non-generic-recursive-env))

(define unequal?
  (extend-relation (a1 a2)
    (relation/cut cut (a)
      (to-show a a)
      (all cut fail))
    (relation (a b)
      (to-show a b)
      (fails fail))))

(define fix  ;;; this is so that students can see what happens
  (lambda (e)
    (e (lambda (z) ((fix e) z)))))

(define generic-base-env
  (relation (g v targ tresult t)
    (to-show `(generic ,v (--> ,targ ,tresult) ,g) v t)
    (all! (fun-call instantiate t `(--> ,targ ,tresult)))))

(define generic-recursive-env
  (relation/cut cut (g v w type-w t)
    (to-show `(generic ,w ,type-w ,g) v t)
    (all! (cut) (env g v t))))

(define generic-env
  (extend-relation (a1 a2 a3) generic-base-env generic-recursive-env))

(define instantiate
  (letrec
      ([instantiate-term
         (lambda (t env)
           (cond
             [(var? t)
              (cond
                [(assv t env)
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
    (all! (!- g x int) (!- g y int))))

(define if-rel
  (relation (g t test conseq alt)
    (to-show g `(if ,test ,conseq ,alt) t)
    (all! (!- g test bool) (!- g conseq t) (!- g alt t))))

(define lambda-rel
  (relation (g v t body type-v)
    (to-show g `(lambda (,v) ,body) `(--> ,type-v ,t))
    (all! (!- `(non-generic ,v ,type-v ,g) body t))))

(define app-rel
  (relation (g t rand rator)
    (to-show g `(app ,rator ,rand) t)
    (exists (t-rand)
      (all! (!- g rator `(--> ,t-rand ,t)) (!- g rand t-rand)))))

(define fix-rel
  (relation (g rand t)
    (to-show g `(fix ,rand) t)
    (all! (!- g rand `(--> ,t ,t)))))

(define polylet-rel
  (relation (g v rand body t)
    (to-show g `(let ([,v ,rand]) ,body) t)
    (exists (t-rand)
      (all!
        (!- g rand t-rand)
        (!- `(generic ,v ,t-rand ,g) body t)))))

(define !-
  (extend-relation (a1 a2 a3)
    var-rel int-rel bool-rel zero?-rel sub1-rel +-rel 
    if-rel lambda-rel app-rel fix-rel polylet-rel))

(test-check 'test-!-1
  (and
    (equal?
      (exists (g) (solution (!- g '(intc 17) int)))
      '(g.0 (intc 17) int))
    (equal?
      (exists (g ?) (solution (!- g '(intc 17) ?)))
      '(g.0 (intc 17) int)))
  #t)

(test-check 'arithmetic-primitives
  (equal?
    (exists (g ?) (solution (!- g '(zero? (intc 24)) ?)))
    '(g.0 (zero? (intc 24)) bool))
  #t)

(test-check 'test-!-sub1
  (equal?
      (exists (g ?) (solution (!- g '(zero? (sub1 (intc 24))) ?)))
      '(g.0 (zero? (sub1 (intc 24))) bool))
  #t)
    
(test-check 'test-!-+
  (equal?
    (exists (g ?)
      (solution
	(!- g '(zero? (sub1 (+ (intc 18) (+ (intc 24) (intc 50))))) ?)))
    '(g.0 (zero? (sub1 (+ (intc 18) (+ (intc 24) (intc 50))))) bool))
  #t)

(test-check 'test-!-2
  (and
      (equal?
        (exists (g ?) (solution (!- g '(zero? (intc 24)) ?)))
        '(g.0 (zero? (intc 24)) bool))
      (equal?
        (exists (g ?) (solution (!- g '(zero? (+ (intc 24) (intc 50))) ?)))
        '(g.0 (zero? (+ (intc 24) (intc 50))) bool))
      (equal?
        (exists (g ?)
          (solution
            (!- g '(zero? (sub1 (+ (intc 18) (+ (intc 24) (intc 50))))) ?)))
        '(g.0 (zero? (sub1 (+ (intc 18) (+ (intc 24) (intc 50))))) bool)))
  #t)

(test-check 'test-!-3
  (exists (?)
    (solution (!- '() '(if (zero? (intc 24)) (intc 3) (intc 4)) ?)))
  '(() (if (zero? (intc 24)) (intc 3) (intc 4)) int))

(test-check 'if-expressions
  (exists (g ?)
    (solution (!- g '(if (zero? (intc 24)) (zero? (intc 3)) (zero? (intc 4))) ?)))
  '(g.0 (if (zero? (intc 24)) (zero? (intc 3)) (zero? (intc 4))) bool))
  
(test-check 'variables
  (and
    (equal?
      (exists (g ?)
	(solution
	  (env `(non-generic b int (non-generic a bool ,g)) 'a ?)))
      '((non-generic b int (non-generic a bool g.0)) a bool))
    (equal?
      (exists (g ?)
	(solution 
	  (!- `(non-generic a int ,g) '(zero? (var a)) ?)))
      '((non-generic a int g.0) (zero? (var a)) bool))
    (equal?
      (exists (g ?)
	(solution
	  (!- `(non-generic b bool (non-generic a int ,g))
	    '(zero? (var a))
	    ?)))
      '((non-generic b bool (non-generic a int g.0)) (zero? (var a)) bool)))
  #t)

(test-check 'variables-4a
  (exists (g ?)
    (solution 
      (!- `(non-generic b bool (non-generic a int ,g))
	'(lambda (x) (+ (var x) (intc 5)))
	?)))
  '((non-generic b bool (non-generic a int g.0))
     (lambda (x) (+ (var x) (intc 5)))
     (--> int int)))

(test-check 'variables-4b
  (exists (g ?)
    (solution 
      (!- `(non-generic b bool (non-generic a int ,g))
	'(lambda (x) (+ (var x) (var a)))
	?)))
  '((non-generic b bool (non-generic a int g.0))
     (lambda (x) (+ (var x) (var a)))
     (--> int int)))

(test-check 'variables-4c
  (exists (g ?)
    (solution
      (!- g '(lambda (a) (lambda (x) (+ (var x) (var a)))) ?)))
  '(g.0 
     (lambda (a) (lambda (x) (+ (var x) (var a))))
     (--> int (--> int int))))

(test-check 'everything-but-polymorphic-let
  (and
    (equal?
      (exists (g ?)
	(solution
            (!- g (parse
                    '(lambda (f)
                       (lambda (x)
                         ((f x) x))))
              ?)))
        '(g.0 (lambda (f)
                (lambda (x) (app (app (var f) (var x)) (var x))))
              (-->
                (--> type-v.0
                  (--> type-v.0 t.0))
                (--> type-v.0 t.0))))
      (equal?
        (exists (g ?)
          (solution
            (!- g
              (parse
                '((fix (lambda (sum)
                         (lambda (n)
                           (if (zero? n)
                               0
                               (+ n (sum (sub1 n)))))))
                  10))
              ?)))
        `(g.0
           ,(parse '((fix (lambda (sum)
                            (lambda (n)
                              (if (zero? n)
                                  0 
                                  (+ n (sum (sub1 n)))))))
                     10))
           int))
      (equal?
        (exists (g ?)
          (solution 
            (!- g
              (parse
                '((fix (lambda (sum)
                         (lambda (n)
                           (+ n (sum (sub1 n))))))
                  10))
              ?)))
        `(g.0
           ,(parse '((fix (lambda (sum)
                            (lambda (n) 
                              (+ n (sum (sub1 n))))))
                     10))
           int))
      (equal?
        (exists (g ?)
          (solution
            (!- g
              (parse '((lambda (f)
                         (if (f (zero? 5))
                             (+ (f 4) 8)
                             (+ (f 3) 7)))
                       (lambda (x) x)))
              ?)))
        #f))
  #t)


(test-check 'polymorphic-let
  (exists (g ?)
    (solution
      (!- g
	(parse
	  '(let ([f (lambda (x) x)])
	     (if (f (zero? 5))
	       (+ (f 4) 8)
	       (+ (f 3) 7))))
	?)))
  `(g.0 
     ,(parse
	'(let ([f (lambda (x) x)])
	   (if (f (zero? 5))
	     (+ (f 4) 8)
	     (+ (f 3) 7))))
     int))

(test-check 'with-robust-syntax
  (exists (g ?)
    (solution
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
  '(g.0 (app
	  (fix (lambda (sum)
		 (lambda (n)
		   (if (if (zero? (var n)) (boolc #t) (boolc #f))
		     (intc 0)
		     (+ (var n) (app (var sum) (sub1 (var n))))))))
	  (intc 10))
     int))

(test-check 'with-robust-syntax-but-long-jumps/poly-let
  (exists (g ?)
    (solution
      (!- g
	'(let ([f (lambda (x) (var x))])
	   (if (app (var f) (zero? (intc 5)))
	     (+ (app (var f) (intc 4)) (intc 8))
	     (+ (app (var f) (intc 3)) (intc 7))))
	?)))
  '(g.0 (let ([f (lambda (x) (var x))])
	  (if (app (var f) (zero? (intc 5)))
	    (+ (app (var f) (intc 4)) (intc 8))
	    (+ (app (var f) (intc 3)) (intc 7))))
     int))

(test-check 'type-habitation
  (and
    (equal?
      (exists (g ?) 
	(solution 
	  (!- g ? '(--> int int))))
      '((non-generic v.0 (--> int int) g.0)
	 (var v.0)
	 (--> int int)))
    (equal?
      (exists (g la f b)
	(solution
	  (!- g `(,la (,f) ,b) '(--> int int))))
      '(g.0 (lambda (v.0) (var v.0)) (--> int int)))
    (equal?
      (exists (g h r q z y t)
	(solution 
	  (!- g `(,h ,r (,q ,z ,y)) t)))
      '((non-generic v.0 int g.0)
	 (+ (var v.0) (+ (var v.0) (var v.0)))
	 int))
    (equal?
      (exists (g h r q z y t u v)
	(solution
	  (!- g `(,h ,r (,q ,z ,y)) `(,t ,u ,v))))
      '(g.0 (lambda (v.0) (+ (var v.0) (var v.0)))
	 (--> int int))))
  #t)
        
;;; long cuts

(define !-generator
  (lambda (long-cut)
    (letrec
      ([!- (extend-relation (a1 a2 a3)
             (relation (g v t)
               (to-show g `(var ,v) t)
               (all long-cut (env g v t)))
             (fact (g x) g `(intc ,x) int)
             (fact (g x) g `(boolc ,x) bool)
             (relation (g x)
               (to-show g `(zero? ,x) bool)
               (all long-cut (!- g x int)))
             (relation (g x)
               (to-show g `(sub1 ,x) int)
               (all long-cut (!- g x int)))
             (relation (g x y)
               (to-show g `(+ ,x ,y) int)
               (all long-cut (all! (!- g x int) (!- g y int))))
             (relation (g t test conseq alt)
               (to-show g `(if ,test ,conseq ,alt) t)
               (all long-cut
		 (all! (!- g test bool) (!- g conseq t) (!- g alt t))))
             (relation (g v t body type-v)
               (to-show g `(lambda (,v) ,body) `(--> ,type-v ,t))
               (all long-cut (!- `(non-generic ,v ,type-v ,g) body t)))
             (relation (g t rand rator)
               (to-show g `(app ,rator ,rand) t)
               (exists (t-rand)
                 (all long-cut
		   (all!
                     (!- g rator `(--> ,t-rand ,t))
                     (!- g rand t-rand)))))
             (relation (g rand t)
               (to-show g `(fix ,rand) t)
               (all long-cut (!- g rand `(--> ,t ,t))))
             (relation (g v rand body t)
               (to-show g `(let ([,v ,rand]) ,body) t)
               (exists (t-rand)
                 (all long-cut
		   (all!
                     (!- g rand t-rand)
                     (!- `(generic ,v ,t-rand ,g) body t))))))])
      !-)))

(define !-
  (relation/cut cut (g exp t)
    (to-show g exp t)
    ((!-generator cut) g exp t)))

(test-check 'with-robust-syntax-but-long-jumps/poly-let
  (exists (g ?)
    (solution
      (!- g
	'(let ([f (lambda (x) (var x))])
	   (if (app (var f) (zero? (intc 5)))
	     (+ (app (var f) (intc 4)) (intc 8))
	     (+ (app (var f) (intc 3)) (intc 7))))
	?)))
  '(g.0 (let ([f (lambda (x) (var x))])
	  (if (app (var f) (zero? (intc 5)))
	    (+ (app (var f) (intc 4)) (intc 8))
	    (+ (app (var f) (intc 3)) (intc 7))))
     int))

(define invertible-binary-function->ternary-relation
  (lambda (op inverted-op)
    (extend-relation (a1 a2 a3)
      (relation (x y z)
        (to-show x y z)
        (all (fails (instantiated z)) (fun-call op z x y)))
      (relation (x y z)
        (to-show x y z)
        (all (fails (instantiated y)) (fun-call inverted-op y z x)))
      (relation (x y z)
        (to-show x y z)
        (all (fails (instantiated x)) (fun-call inverted-op x z y)))
      (relation (x y z)
        (to-show x y z)
        (fun-call op z x y)))))

(define ++ (invertible-binary-function->ternary-relation + -))
(define -- (invertible-binary-function->ternary-relation - +))
(define ** (invertible-binary-function->ternary-relation * /))
(define // (invertible-binary-function->ternary-relation / *))

(test-check 'test-instantiated-1
  (and
      (equal?
        (exists (x) (solution (++ x 16.0 8)))
        '(-8.0 16.0 8))
      (equal?
        (exists (x) (solution (++ 10 16.0 x)))
        '(10 16.0 26.0))
      (equal?
        (exists (x) (solution (++ 10 16.0 26.0)))
        '(10 16.0 26.0))
      (equal?
        (exists (x) (solution (-- 10 7 3)))
        '(10 7 3)))
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
        (all (fails (instantiated y)) (fun-call op y x)))
      (relation (x y)
        (to-show x y)
        (all (fails (instantiated x)) (fun-call inverted-op x y)))
      (relation (x y)
        (to-show x y)
        (begin (pretty-print "Third rule") (fun-call op y x))))))

(define name
  (invertible-unary-function->binary-relation symbol->lnum lnum->symbol))

(test-check 'test-instantiated-2
  (and
      (equal?
        (exists (x) (solution (name 'sleep x)))
        '(sleep (115 108 101 101 112)))
      (equal?
        (exists (x) (solution (name x '(115 108 101 101 112))))
        '(sleep (115 108 101 101 112)))
      (equal?
        (exists (x) (solution (name 'sleep '(115 108 101 101 112))))
        '(sleep (115 108 101 101 112))))
  #t)

;;;; *****************************************************************
;;;; This is the start of a different perspective on logic programming.
;;;; Unitl I saw (!! fk), it was not possible to do the things that I
;;;; wanted to do.  This does obviate the need for unify-sequence, so
;;;; that is good.

(define father
  (lambda (dad child)
    (all! 
      (== dad 'john)
      (== child 'sam))))


(define father
  (extend-relation (a1 a2) father
    (lambda (dad child)
      (all! 
	(== dad 'sam)
	(== child 'pete)))))

(define father
  (extend-relation (a1 a2) father
    (lambda (dad child)
      (all!
	(== dad 'pete)
	(== child 'sal)))))

(define grandpa
  (lambda (grandfather child)
    (exists (x)
      (all (father grandfather x) (father x child)))))

(test-check 'grandpa-ng
  (exists (x y) (solve 5 (grandpa x y)))
  '((john pete) (sam sal)))

(define father-pete-sal (fact () 'pete 'sal))
(define father-sam-pete (fact () 'sam 'pete))
(define father-john-sam (fact () 'john 'sam))
(define father
  (extend-relation (a1 a2) father-john-sam father-sam-pete father-pete-sal))

(test-check 'grandpa-ng-1
  (exists (x y) (solve 5 (grandpa x y)))
  '((john pete) (sam sal)))
(test-check 'grandpa-ng-2
  (exists (x y) (solve 5 (grandpa 'sam y)))
  '((sam sal)))
(test-check 'grandpa-ng-2
  (exists (x y) (solve 5 (grandpa x 'sal)))
  '((sam sal)))

(define grandpa-sam
  (lambda (child)
    (lambda@ (sk fk subst cutk)
      (let ([next (!! fk)]
            [cut (!! cutk)])
        (exists (grandfather)
          (@ (all
               (all next (== grandfather 'sam))
               cut
               (exists (x)
                 (all (father grandfather x) (father x child))))
             sk fk subst cutk))))))

(test-check 'grandpa-sam-1
  (exists (x y) (solve 5 (grandpa-sam 'sal)))
  '((sal)))


(define grandpa-sam
  (relation/cut cut (child)
    (to-show child)
    (exists (x)
      (all (father 'sam x) (father x child)))))

(test-check 'grandpa-sam-2
  (exists (x y) (solve 5 (grandpa-sam 'sal)))
  '((sal)))

(define-syntax fact
  (syntax-rules ()
    [(_ (ex ...) x ...)
     (relation (ex ...) (to-show x ...))]))

(define father-pete-sal (fact () 'pete 'sal))
(define father-sam-pete (fact () 'sam 'pete))
(define father-john-sam (fact () 'john 'sam))
(define father 
  (extend-relation (a1 a2) father-john-sam father-sam-pete father-pete-sal))

(test-check 'grandpa-sam-3
  (exists (x y) (solve 5 (grandpa-sam 'sal)))
  '((sal)))

(define father-pete-sal
  (relation () (to-show 'pete 'sal)))

(define father-sam-pete
  (relation () (to-show 'sam 'pete)))

(define father-johh-sam
  (relation () (to-show 'john 'sam)))

(define father 
  (extend-relation (a1 a2) father-john-sam father-sam-pete father-pete-sal))

(test-check 'grandpa-sam-4
  (exists (x y) (solve 5 (grandpa-sam 'sal)))
  '((sal)))

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
(pretty-print (exists (x y) (solve 10 (R1 x y))))
(printf "~%R2:~%")
(pretty-print (exists (x y) (solve 10 (R2 x y))))
(printf "~%R1+R2:~%")
(pretty-print 
  (exists (x y) (solve 10 
		  ((extend-relation (a1 a2) R1 R2) x y))))

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
(time (pretty-print (exists (x y) (solve 5 (Rinf x y)))))
(printf "~%Rinf+R1: Rinf starves R1:~%")
(time
  (pretty-print 
  (exists (x y) (solve 5
		  ((extend-relation (a1 a2) Rinf R1) x y)))))

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

(printf "~%binary-extend-relation-interleave~%")
(printf "~%Rinf+R1:~%")
(time (pretty-print 
  (exists (x y) (solve 7
		  ((binary-extend-relation-interleave (a1 a2) Rinf R1) x y)))))
(printf "~%R1+RInf:~%")
(time (pretty-print 
  (exists (x y) (solve 7
		  ((binary-extend-relation-interleave (a1 a2) R1 Rinf) x y)))))

(printf "~%R2+R1:~%")
(time (pretty-print 
  (exists (x y) (solve 7
		  ((binary-extend-relation-interleave (a1 a2) R2 R1) x y)))))
(printf "~%R1+fact3:~%")
(time (pretty-print 
  (exists (x y) (solve 7
		  ((binary-extend-relation-interleave (a1 a2) R1 fact3) x y)))))
(printf "~%fact3+R1:~%")
(time (pretty-print 
  (exists (x y) (solve 7
		  ((binary-extend-relation-interleave (a1 a2) fact3 R1) x y)))))

;;; Test for nonoverlapping.

(printf "~%binary-extend-relation-interleave-non-overlap~%")
(test-check "R1+R2"
  (exists (x y) 
    (solve 10 
      ((binary-extend-relation-interleave-non-overlap (a1 a2) R1 R2) x y)))
  '((x1 y1) (x2 y2) (x3 y3)))

(test-check "R2+R1"
  (exists (x y) 
    (solve 10 
      ((binary-extend-relation-interleave-non-overlap (a1 a2) R2 R1) x y)))
  '((x1 y1) (x3 y3) (x2 y2)))

(test-check "Rinf+R1"
  (exists (x y)
    (solve 7
      ((binary-extend-relation-interleave-non-overlap (a1 a2) Rinf R1) x y)))
  '((z z)
    (x1 y1)
    ((s z) (s z))
    (x2 y2)
    ((s (s z)) (s (s z)))
    ((s (s (s z))) (s (s (s z))))
    ((s (s (s (s z)))) (s (s (s (s z)))))))

(test-check "R1+RInf"
  (exists (x y) 
    (solve 7
      ((binary-extend-relation-interleave-non-overlap (a1 a2) R1 Rinf) x y)))
  '((x1 y1)
    (z z)
    (x2 y2)
    ((s z) (s z))
    ((s (s z)) (s (s z)))
    ((s (s (s z))) (s (s (s z))))
    ((s (s (s (s z)))) (s (s (s (s z))))))
)

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
  (exists (x y) (solve 5 (Rinf2 x y)))
  '((z z)
     ((s (s z)) (s (s z)))
     ((s (s (s (s z)))) (s (s (s (s z)))))
     ((s (s (s (s (s (s z)))))) (s (s (s (s (s (s z)))))))
     ((s (s (s (s (s (s (s (s z))))))))
       (s (s (s (s (s (s (s (s z)))))))))))

(test-check "Rinf+Rinf2"
  (exists (x y)
    (solve 9
      ((binary-extend-relation-interleave-non-overlap 
	 (a1 a2) Rinf Rinf2) x y)))
  '((z z)
     ((s z) (s z))
     ((s (s z)) (s (s z)))
     ((s (s (s (s z)))) (s (s (s (s z)))))
     ((s (s (s z))) (s (s (s z))))
     ((s (s (s (s (s (s z)))))) (s (s (s (s (s (s z)))))))
     ((s (s (s (s (s (s (s (s z))))))))
       (s (s (s (s (s (s (s (s z)))))))))
     ((s (s (s (s (s z))))) (s (s (s (s (s z))))))
     ((s (s (s (s (s (s (s (s (s (s z))))))))))
       (s (s (s (s (s (s (s (s (s (s z))))))))))))
)

(test-check "Rinf2+Rinf"
  (exists (x y)
    (solve 9
      ((binary-extend-relation-interleave-non-overlap 
	 (a1 a2) Rinf2 Rinf) x y)))
  '((z z)
     ((s z) (s z))
     ((s (s z)) (s (s z)))
     ((s (s (s z))) (s (s (s z))))
     ((s (s (s (s z)))) (s (s (s (s z)))))
     ((s (s (s (s (s z))))) (s (s (s (s (s z))))))
     ((s (s (s (s (s (s z)))))) (s (s (s (s (s (s z)))))))
     ((s (s (s (s (s (s (s z)))))))
       (s (s (s (s (s (s (s z))))))))
     ((s (s (s (s (s (s (s (s z))))))))
       (s (s (s (s (s (s (s (s z)))))))))))

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
      (exists (x)
	(solution (nrev lst x))))
    (list lst (reverse lst))))

(define get_cpu_time
  (lambda ()
    (vector-ref (statistics) 1)))

(define lots
  (extend-relation ()
    (relation ()
      (to-show)
      (exists (count)
        (all
          (pred-call newline)
          (pred-call newline)
          (eg_count count)
          (bench count)
          fail)))
    (fact ())))

(define test-lots
  (lambda ()
    (solve 1000 (lots))))

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
    (exists (t0 t1 t2)
      (all
        (fun-call get_cpu_time t0)
        (dodummy count)
        (fun-call get_cpu_time t1)
        (dobench count)
        (fun-call get_cpu_time t2)
        (report count t0 t1 t2)))))

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
      (exists (n1)
        (all
          (pred-call > n 1)
          (fun-call - n1 n 1)
          (repeat n1))))))

(define report
  (relation (count t0 t1 t2)
    (to-show count t0 t1 t2)
    (exists (time1 time2 time lips units)
      (all
        (fun-call - time1 t1 t0)
        (fun-call - time2 t2 t1)
        (fun-call - time time2 time1)
        (calculate_lips count time lips units)
        (pred-call printf "~n~s lips for ~s" lips count)
        (pred-call printf " Iterations taking ~s  ~s ( ~s )~n " time units time)))))

(define calculate_lips
  (extend-relation (a1 a2 a3 a4)
    (relation/cut cut (count time lips)
      (to-show count time lips 'msecs)
      (== time 0)
      cut
      (== lips 0))
    (relation (count time lips)
      (to-show count time lips 'msecs)
      (exists (t1 t2)
        (all
          (fun-call * t1 496 count 1000)
          (fun-call + t2 time 0.0)
          (fun-call / lips t1 t2))))))

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
      (fails (pred-call/no-check *equal? c1 c2)))))

(printf "~%Counter-example: ~s~%" 
  (exists (a b c1 c2)
    (solution 
      (typeclass-counter-example-query a b c1 c2))))

(define depth-counter-var (exists (*depth-counter-var*) *depth-counter-var*))

; Run the antecedent no more than n times, recursively
(define with-depth
  (lambda (limit ant)
    (lambda@ (sk fk subst cutk)
      (cond
        [(assv depth-counter-var subst)
         => (lambda (cmt)
              (let ([counter (commitment->term cmt)])
                (printf "~%counter ~d" counter)
                (if (= counter limit)
                  (fk)
                  (let ([s (extend-subst depth-counter-var (+ counter 1) subst)])
                    (@ ant sk fk s cutk)))))]
        [else
          (let ([s (extend-subst depth-counter-var 0 subst)])
            (@ ant sk fk s cutk))]))))

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
  (exists (a b c1 c2)
    (solution 
      (typeclass-counter-example-query a b c1 c2))))

(printf "~%Counter-example: ~s~%" 
  (exists (a b c1 c2)
    (solve 4
      (typeclass-counter-example-query a b c1 c2))))

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
  (exists (a b c) (solve 100
			(extend-rel a b c))))

(define extend-rel
  (lambda (a b c)
    (with-depth 3
      (any
	(extend-clause-2 a b c)
        (extend-clause-1 a b c)))))

(printf "~%Extend: clause2 first. In Prolog, it would diverge!: ~s~%" 
  (exists (a b c) (solve 100
			(extend-rel a b c))))


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
      (fails (pred-call/no-check *equal? b1 b2)))))

 (printf "~%Counter-example: ~s~%" 
   (exists (a b1 b2) (solve 4
		       (typeclass-F-counter-example-query a b1 b2))))

 
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
  (exists (a) (solve 4
		(typeclass-F-instance-1 `(list ,a) a)))
  '())					; meaning: does not typecheck!

; This is an open-world assumption
(define typeclass-F
  (lambda (a b)
    (with-depth 2
      (any
	(typeclass-F-instance-1 a b)
	((relation/cut cut (a b1 b2)	; a relation under constraint a->b
	   (to-show a b1)
	   (fails
	     (all
	       (typeclass-F a b2)
	       (fails (pred-call/no-check *equal? b1 b2))
	       cut))) a b)
	))))

(printf "~%Typechecking (open world): ~s~%" 
  (exists (a) (solve 4
		(typeclass-F-instance-1 `(list ,a) a))))

(test-check "Typechecking (open world) f [x] int" 
  (exists (a) (solve 4
		(typeclass-F-instance-1 `(list ,a) 'int)))
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
	(pred-call printf "btree ~s ~s ~n" t1 t2)
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
    (exists (t1)
      (list
	`(btree ,t)
	`(myeq ,t  (mirror ,t1))
	`(myeq ,t1 (mirror ,t))))))

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
        [(var? term) (if (memv term fv) fv (cons term fv))]
        [(pair? term) (loop (cdr term) (loop (car term) fv))]
        [else fv]))))

(define symbol-append
  (lambda symbs
    (string->symbol
      (apply string-append
        (map symbol->string symbs)))))

(define concretize
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
; Why we need concretize?
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
    (let ([facts (concretize facts)])
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

; that is, we obtain the list of subgoals to verify '(leaf x)
; by invoking the function 'goal'.
; we extend the initial database (which contains btree facts)
; with mirror-axiom-eq-1. Thus, mirror-axiom-eq-1 and btree form
; the assumptions. We then verify the subgoals against the assumptions.
; Note that we wrote
;    '(leaf x)
; rather than
;    (exists (x) `(leaf ,x))
; because we want to prove that (goal '(leaf x)) holds for _all_ x
; rather than for some particular x.


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

; Again, we use Y because btree and mirror-axiom-eq-2 are recursive.
; We need the database that is the fixpoint of all constituent
; relations.
; The output above is a non-empty list: meaning that the inductive
; phase of the proof checks.

(exit 0)

;;; For future thoughts.

(define-syntax fun-call*
  (syntax-rules ()
    [(_ f u ...)
     (lambda (subst) 
       ((nonvar! (subst-in f subst)) (nonvar! (subst-in u subst)) ...))]))

