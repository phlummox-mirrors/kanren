;;;; Can you send me this translated using the latest version
;;;; of our logic system, below.  This is commented out in the
;;;; the code below.  That's where I would like for you to put
;;;; the answer.

;;;; Please send back all the code.
;;;; .... Dan

;-----------------------------------/-----------------------------

;(load "plshared.ss")

(define-syntax exists
  (syntax-rules ()
    [(_ () body0 body1 ...) (begin body0 body1 ...)]
    [(_ (id ...) body0 body1 ...)
     (let ([id (var 'id)] ...) body0 body1 ...)]))

(define-syntax lambda@
  (syntax-rules ()
    [(_ () body0 body1 ...) (begin body0 body1 ...)]
    [(_ (formal0 formal1 ...) body0 body1 ...)
     (lambda (formal0)
       (lambda@ (formal1 ...) body0 body1 ...))]))

(define-syntax @    
  (syntax-rules ()
    [(_ arg0) arg0]
    [(_ arg0 arg1 arg2 ...) (@ (arg0 arg1) arg2 ...)]))

(define test-@-lambda@
  (lambda ()
    (equal?
      (@ (lambda@ (x y z) (+ x (+ y z))) 1 2 3)
      6)))

(printf "~s ~s~%" 'test-@-lambda@ (test-@-lambda@))

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

(define test-nonrecursive-unify
  (lambda ()
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
          #f)))))

(printf "~s ~s~%" 'test-nonrecursive-unify (test-nonrecursive-unify))

(define == 
  (lambda (x y)
    (lambda@ (sk fk subst cutk)
      (cond
        [(unify x y subst)
         => (lambda (subst)
              (@ sk fk subst cutk))]
        [else (fk)]))))

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

(define-syntax let-values
  (syntax-rules ()
    [(_ (x ...) vs body0 body1 ...)
     (call-with-values (lambda () vs) (lambda (x ...) body0 body1 ...))]))

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

(define test-compose-subst-0
  (lambda ()
    (exists (x y)
      (equal?
        (append (unit-subst x y) (unit-subst y 52))
        `(,(commitment x y) ,(commitment y 52))))))

(printf "~s ~s~%" 'test-compose-subst-0 (test-compose-subst-0))

(define test-compose-subst-1
  (lambda ()
    (exists (x y)
      (equal?
        (compose-subst (unit-subst x y) (unit-subst y 52))
        `(,(commitment x 52) ,(commitment y 52))))))

(printf "~s ~s~%" 'test-compose-subst-1 (test-compose-subst-1))

(define test-compose-subst-2
  (lambda ()
    (exists (w x y)
      (equal?
        (let ([s (compose-subst (unit-subst y w) (unit-subst w 52))])
          (compose-subst (unit-subst x y) s))
        `(,(commitment x 52) ,(commitment y 52) ,(commitment w 52))))))

(printf "~s ~s~%" 'test-compose-subst-2 (test-compose-subst-2))

(define test-compose-subst-3
  (lambda ()
    (exists (w x y)
      (equal?
        (let ([s (compose-subst (unit-subst w 52) (unit-subst y w))])
          (compose-subst (unit-subst x y) s))
        `(,(commitment x w) ,(commitment w 52) ,(commitment y w))))))

(printf "~s ~s~%" 'test-compose-subst-3 (test-compose-subst-3))

(define test-compose-subst-4
  (lambda ()
    (exists (x y z)
      (equal?
        (let ([s (compose-subst (unit-subst y z) (unit-subst x y))]
              [r (compose-subst
                   (compose-subst (unit-subst x 'a) (unit-subst y 'b))
                   (unit-subst z y))])
          (compose-subst s r))
        `(,(commitment x 'b) ,(commitment z y))))))

(printf "~s ~s~%" 'test-compose-subst-4 (test-compose-subst-4))

(define initial-fk (lambda () '()))
(define initial-cutk initial-fk)
(define initial-sk (lambda@ (fk subst cutk) (cons (cons subst cutk) fk)))

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

; 	c(A,tuple(A,C,B),C,dict2).
; 	c(A,tuple(X,Y,B),C,dict1) :- c(A,B,C,_).
; Had I switched the order,
; 	c(A,tuple(X,Y,B),C,dict1) :- c(A,B,C,_).
; 	c(A,tuple(A,C,B),C,dict2).
; the queries would have never terminated. That's where our
; extend-relation-interleave would be quite handy.

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
    [(_ (id ...) rel-exp0 rel-exp1 ...)
     (binary-extend-relation (id ...) rel-exp0
       (extend-relation (id ...) rel-exp1 ...))]))

(define-syntax all
  (syntax-rules ()
    [(_) (lambda (sk) sk)]
    [(_ ant) ant]
    [(_ ant0 ant1 ...)
     (lambda@ (sk)
       (ant0 (splice-in-ants/all sk ant1 ...)))]))

(define-syntax splice-in-ants/all
  (syntax-rules ()
    [(_ sk ant) (ant sk)]
    [(_ sk ant0 ant1 ...)
     (ant0 (splice-in-ants/all sk ant1 ...))]))

(define-syntax all!
  (syntax-rules ()
    [(_) (lambda (sk) sk)]
    [(_ ant) ant]
    [(_ ant0 ant1 ...)
     (lambda@ (sk fk)
       (@ ant0 (splice-in-ants/all! sk fk ant1 ...) fk))]))

(define-syntax splice-in-ants/all!
  (syntax-rules ()
    [(_ sk fk ant)
     (lambda (ign-fk)
       (@ ant sk fk))]
    [(_ sk fk ant0 ant1 ...)
     (lambda (ign-fk)
       (@ ant0 (splice-in-ants/all! sk fk ant1 ...) fk))]))

(define-syntax relation
  (syntax-rules (to-show _)
    [(_ cut-id (ex-id ...) (to-show x ...) ant ...)
     (relation cut-id (ex-id ...) () (x ...) (x ...) ant ...)]
    [(_ cut-id (ex-id ...) (g ...) () (x ...))
     (lambda (g ...)
       (exists (ex-id ...)
	 (all! (== g x) ...)))]
    [(_ _ (ex-id ...) (g ...) () (x ...) ant ...)
     (lambda (g ...)
       (exists (ex-id ...)
	 (all! (== g x) ... (all ant ...))))]
    [(_ cut-id (ex-id ...) (g ...) () (x ...) ant ...)
     (lambda (g ...)
       (exists (ex-id ...)
         (all! (== g x) ...
           (lambda@ (sk fk subst cutk)
             (let ([cut-id (!! cutk)])
               (@ (all ant ...) sk fk subst cutk))))))]
    [(_ cut-id ex-ids (var ...) (x0 x1 ...) xs ant ...)
     (relation cut-id ex-ids (var ... g) (x1 ...) xs ant ...)]))

(define-syntax trace-relation
  (syntax-rules (to-show _)
    [(_ id cut-id (ex-id ...) (to-show x ...) ant ...)
     (trace-relation id cut-id (ex-id ...) () (x ...) (x ...) ant ...)]
    [(_ id cut-id (ex-id ...) (g ...) () (x ...))
     (trace-lambda id (g ...)
       (exists (ex-id ...)
	 (all! (== g x) ...)))]
    [(_ id _ (ex-id ...) (g ...) () (x ...) ant ...)
     (trace-lambda id (g ...)
       (exists (ex-id ...)
	 (all! (== g x) ... (all ant ...))))]
    [(_ id cut-id (ex-id ...) (g ...) () (x ...) ant ...)
     (trace-lambda id (g ...)
       (exists (ex-id ...)
         (all! (== g x) ...
           (lambda@ (sk fk subst cutk)
             (let ([cut-id (!! cutk)])
               (@ (all ant ...) sk fk subst cutk))))))]
    [(_ id cut-id ex-ids (var ...) (x0 x1 ...) xs ant ...)
     (trace-relation id cut-id ex-ids (var ... g) (x1 ...) xs ant ...)]))

(define-syntax fact
  (syntax-rules ()
    [(_ (ex-id ...) x ...)
     (relation _ (ex-id ...) (to-show x ...))]))

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
  (relation _ ()
    (to-show 'john 'sam)))

(printf "~s ~s~%" 'test-father0
  (let ([result
          (@ (father 'john 'sam)
             initial-sk initial-fk empty-subst initial-fk)])
    (and
      (equal? (caar result) '())
      (equal? ((cdr result)) '()))))

;;; Now we need concretize-subst about here.

(define child-of-male
  (relation _ (child dad)
    (to-show child dad)
    (father dad child)))

(define test-child-of-male-0
  (lambda ()
    (equal?
      (concretize-subst
        (caar (@ (child-of-male 'sam 'john)
                initial-sk initial-fk empty-subst initial-fk)))
      `(,(commitment 'child.0 'sam) ,(commitment 'dad.0 'john)))))

(printf "~s ~s~%" 'test-child-of-male-0 (test-child-of-male-0))

(define pete/sal
  (relation _ ()
    (to-show 'pete 'sal)))

(define new-father
  (extend-relation (a1 a2) father pete/sal))

(define test-father-1
  (lambda ()
    (let ([result
            (@ (new-father 'pete 'sal)
               initial-sk initial-fk empty-subst initial-fk)])
      (and
        (equal? (caar result) '())
        (equal? ((cdr result)) '())))))

(printf "~s ~s~%" 'test-father-1 (test-father-1))

(define query
  (let ([initial-fk (lambda () '())]
        [initial-sk (lambda@ (fk subst cutk) (cons (cons subst cutk) fk))])
    (lambda (antecedent)
      (@ antecedent initial-sk initial-fk empty-subst initial-fk))))

(define test-father-2
  (lambda ()
    (exists (x)
      (let ([result (query (new-father 'pete x))])
        (and
          (equal? (caar result) `(,(commitment x 'sal)))
          (equal? ((cdr result)) '()))))))

(printf "~s ~s~%" 'test-father-2 (test-father-2))

(define test-father-3
  (lambda ()
    (exists (x)
      (equal?
        (let ([answer (query (new-father 'pete x))])
          (let ([subst (caar answer)])
            (concretize-sequence (subst-in 'pete subst) (subst-in x subst))))
        '(pete sal)))))

(printf "~s ~s~%" 'test-father-3 (test-father-3))

(define test-father-4
  (lambda ()
    (exists (x y)
      (equal?
        (let ([answer (query (new-father x y))])
          (let ([subst (caar answer)])
            (concretize-sequence (subst-in x subst) (subst-in y subst))))
        '(john sam)))))

(printf "~s ~s~%" 'test-father-4 (test-father-4))

(define pete/pat
  (relation _ ()
    (to-show 'pete 'pat)))

(define newer-father
  (extend-relation (a1 a2) new-father pete/pat))

(define test-father-5
  (lambda ()
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
          '((pete sal) (pete pat)))))))
      
(printf "~s ~s~%" 'test-father-5 (test-father-5))

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
            (concretize-sequence (subst-in t0 (car subst/cutk)) ...))
       (stream-prefix (- n 1) (query (rel t0 ...))))]))

(define sam/pete
  (relation _ ()
    (to-show 'sam 'pete)))

(define newest-father (extend-relation (a1 a2) newer-father sam/pete))

(define test-father-6/solve
  (lambda ()
    (exists (x y)
      (and
        (equal?
          (solve 5 (newest-father 'pete x))
          '((pete sal) (pete pat)))
        (equal?
          (solve 6 (newest-father x y))
          '((john sam) (pete sal) (pete pat) (sam pete)))))))
            
(printf "~s ~s~%" 'test-father-6/solve (test-father-6/solve))

(define-syntax solution
  (syntax-rules ()
    [(_ x)
     (let ([ls (solve 1 x)])
       (if (null? ls) #f (car ls)))]))

(define test-father-7/solution
  (lambda ()
    (equal?
      (exists (x) (solution (newest-father 'pete x)))
      '(pete sal))))

(printf "~s ~s~%" 'test-father-7/solution (test-father-7/solution))

(define grandpa-sam
  (relation _ (grandchild)
    (to-show grandchild)
    (exists (parent)
      (lambda (sk)
        ((newest-father 'sam parent)
         ((newest-father parent grandchild) sk))))))

(define test-grandpa-sam-1
  (lambda ()
    (exists (y)
      (equal?
        (solve 6 (grandpa-sam y))
        '((sal) (pat))))))

(printf "~s ~s~%" 'test-grandpa-sam-1 (test-grandpa-sam-1))

(define-syntax any
  (syntax-rules ()
    [(_ ant ...)
     ((extend-relation () (relation _ () (to-show) ant) ...))]))

(define child
  (relation _ (child dad)
    (to-show child dad)
    (newest-father dad child)))

(define test-child-1
  (lambda ()
    (exists (x y)
      (equal?
        (solve 10 (child x y))
        '((sam john) (sal pete) (pat pete) (pete sam))))))

(printf "~s ~s~%" 'test-child-1 (test-child-1))

(define grandpa-sam
  (relation _ (grandchild)
    (to-show grandchild)
    (exists (parent)
      (all
        (newest-father 'sam parent)
        (newest-father parent grandchild)))))

(define test-grandpa-sam-2
  (lambda ()
    (exists (y)
      (equal?
        (solve 6 (grandpa-sam y))
        '((sal) (pat))))))

(printf "~s ~s~%" 'test-grandpa-sam-2 (test-grandpa-sam-2))

(define grandpa-maker
  (lambda (grandad)
    (relation _ (grandchild)
      (to-show grandchild)
      (exists (parent)
        (all
          (newest-father grandad parent)
          (newest-father parent grandchild))))))

(define test-grandpa-maker-1
  (lambda ()
    (exists (x)
      (equal?
        (solve 6 ((grandpa-maker 'sam) x))
        '((sal) (pat))))))

(printf "~s ~s~%" 'test-grandpa-maker-1 (test-grandpa-maker-1))

(define grandpa-maker
  (lambda (guide* grandad*)
    (relation _ (grandchild)
      (to-show grandchild)
      (exists (parent)
        (all
          (guide* grandad* parent)
          (guide* parent grandchild))))))

(define test-grandpa-maker-2
  (lambda ()
    (exists (x)
      (equal?
        (solve 4 ((grandpa-maker newest-father 'sam) x))
        '((sal) (pat))))))

(printf "~s ~s~%" 'test-grandpa-maker-2 (test-grandpa-maker-2))

(define grandpa
  (relation _ (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (newest-father grandad parent)
        (newest-father parent grandchild)))))

(define test-grandpa-1
  (lambda ()
    (exists (x)
      (equal?
        (solve 4 (grandpa 'sam x))
        '((sam sal) (sam pat))))))

(printf "~s ~s~%" 'test-grandpa-1 (test-grandpa-1))

(define-syntax fact
  (syntax-rules ()
    [(_ (var ...) x ...) (relation _ (var ...) (to-show x ...))]))

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
    (relation _ (grandad grandchild)
      (to-show grandad grandchild)
      (exists (parent)
        (all
          (father grandad parent)
          (father parent grandchild))))
    (relation _ (grandad grandchild)
      (to-show grandad grandchild)
      (exists (parent)
        (all
          (father grandad parent)
          (mother parent grandchild))))))

(define test-grandpa-2
  (lambda ()
    (exists (x y)
      (equal?
        (solve 10 (grandpa 'sam y))
        '((sam sal) (sam pat) (sam betty) (sam david))))))

(printf "~s ~s~%" 'test-grandpa-2 (test-grandpa-2))

(define grandpa/father
  (relation _ (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (father parent grandchild)))))

(define grandpa/mother
  (relation _ (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (mother parent grandchild)))))

(define grandpa
  (extend-relation (a1 a2) grandpa/father grandpa/mother))

(define test-grandpa-5
  (lambda ()
    (exists (x y)
      (equal?
        (solve 10 (grandpa 'sam y))
        '((sam sal) (sam pat) (sam betty) (sam david))))))

(printf "~s ~s~%" 'test-grandpa-5 (test-grandpa-5))

(define grandpa-sam
  (let ([r (relation _ (child)
             (to-show child)
             (exists (parent)
               (all
                 (father 'sam parent)
                 (father parent child))))])
    (relation _ (child)
      (to-show child)
      (r child))))

(define test-grandpa-sam-4
  (lambda ()
    (exists (y)
      (equal?
        (solve 6 (grandpa-sam y))
        '((sal) (pat))))))

(printf "~s ~s~%" 'test-grandpa-sam-4 (test-grandpa-sam-4))  

(define grandpa/father
  (relation cut (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (father parent grandchild)
        cut))))

(define grandpa/mother
  (relation _ (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (mother parent grandchild)))))

(define grandpa
  (extend-relation (a1 a2) grandpa/father grandpa/mother))

(define test-grandpa-8
  (lambda ()
    (exists (x y)
      (equal?
        (solve 10 (grandpa x y))
        '((john pete))))))

(printf "~s ~s~%" 'test-grandpa-8 (test-grandpa-8))

(define grandpa/father
  (relation cut (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all cut (father grandad parent) (father parent grandchild)))))

(define grandpa
  (extend-relation (a1 a2) grandpa/father grandpa/mother))

(define test-grandpa-10
  (lambda ()
    (exists (x y)
      (equal?
        (solve 10 (grandpa x y))
        '((john pete) (john polly) (sam sal) (sam pat))))))

(printf "~s ~s~%" 'test-grandpa-10 (test-grandpa-10))

(define fail
  (lambda@ (sk fk subst cutk) (fk)))

(define no-grandma
  (relation cut (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all (mother grandad parent) cut fail))))

(define no-grandma-grandpa
  (extend-relation (a1 a2) no-grandma grandpa))

(define test-no-grandma-grandpa-1
  (lambda ()
    (exists (x)
      (equal?
        (solve 1 (no-grandma-grandpa 'polly x))
        '()))))

(printf "~s ~s~%" 'test-no-grandma-grandpa-1 (test-no-grandma-grandpa-1))

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
         [(unify t ((nonvar! (subst-in f subst)) (nonvar! (subst-in u subst)) ...) subst)
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
  (relation _ (grandad grandchild)
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

(define test-grandpa-11
  (lambda ()
    (exists (x y)
      (equal?
        (solve 10 (grandpa x y))
        '((sam sal) (sam pat))))))

(printf "~s ~s~%" 'test-grandpa-11 (test-grandpa-11))

(define check
  (lambda (id f)
    (lambda term
      (if (not (procedure? f))
          (error id "Non-procedure found: ~s" f))
      (if (ormap var? term)
          (error id "Variable found: ~s" term))
      (apply f term))))

(define test-grandpa-12
  (lambda ()
    (exists (x y)
      (equal?
        (solve 10 (grandpa x y))
        '((sam sal) (sam pat))))))

(printf "~s ~s~%" 'test-grandpa-12 (test-grandpa-12))

(define fun    
  (lambda (f)
    (fun-nocheck (check 'fun f))))

(define test-fun-*  
  (lambda ()
    (exists (q)
      (equal?
        (solve 3 (fun-call * q 3 5))
       `((,* 15 3 5))))))

(printf "~s ~s~%" 'test-fun-* (test-fun-*))

(define test1
  (lambda (x)
    (any (pred-call < 4 5) (fun-call < x 6 7))))

;;;; Here is the definition of concretize.

(define concretize
  (lambda (t)
    (let-values (ct new-env) (concretize-term t '())
      ct)))

(define test-test1
  (lambda ()
    (exists (x)
      (equal?
        (solution (test1 x))
        `(,(concretize x))))))

(printf "~s ~s~%" 'test-test1 (test-test1))

(define test2
  (lambda (x)
    (any (pred-call < 5 4) (fun-call < x 6 7))))

(define test-test2
  (lambda ()
    (exists (x)
      (equal?
        (solution (test2 x))
        '(#t)))))

(printf "~s ~s~%" 'test-test2 (test-test2))

(define test3
  (lambda (x y)
    (any (fun-call < x 5 4) (fun-call < y 6 7))))

(define test-test3
  (lambda ()
    (exists (x y)
      (equal?
        (solution (test3 x y))
        `(#f ,(concretize y))))))

(printf "~s ~s~%" 'test-test3 (test-test3))

(define fails
  (lambda (ant)
    (lambda@ (sk fk subst cutk)
      (@ ant
        (lambda@ (current-fk subst cutk) (fk))
        (lambda () (@ sk fk subst cutk))
        subst cutk))))

(define grandpa
  (relation _ (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (fails (pred-call starts-with-p? parent))
        (father parent grandchild)))))

(define test-grandpa-13
  (lambda ()
    (exists (x y)
      (equal?
        (solve 10 (grandpa x y))
        '((john pete) (john polly))))))

(printf "~s ~s~%" 'test-grandpa-13 (test-grandpa-13))

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
  (relation _ (grandad grandchild)
    (to-show grandad grandchild)
    (exists (parent)
      (all
        (father grandad parent)
        (father parent grandchild)
        (view-subst grandchild)))))

(define test-grandpa-14/view-subst
  (lambda ()
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
          '((john pete) (john polly) (sam sal) (sam pat)))))))

(printf "~s ~s~%" 'test-grandpa-14/view-subst (test-grandpa-14/view-subst))

(define father
  (extend-relation (a1 a2) father
    (extend-relation (a1 a2) (fact () 'john 'harry)
      (extend-relation (a1 a2) (fact () 'harry 'carl) (fact () 'sam 'ed)))))

(define ancestor
  (extend-relation (a1 a2)
    (relation _ (old young)
      (to-show old young)
      (father old young))
    (relation _ (old young)
      (to-show old young)
      (exists (not-so-old)
        (all (father old not-so-old) (ancestor not-so-old young))))))

(define test-ancestor
  (lambda ()
    (exists (x)
      (equal?
        (solve 21 (ancestor 'john x))
        '((john sam)
          (john harry)
          (john pete)
          (john polly)
          (john ed)
          (john sal)
          (john pat)
          (john carl))))))

(printf "~s ~s~%" 'test-ancestor (test-ancestor))

(define common-ancestor
  (relation _ (young-a young-b old)
    (to-show young-a young-b old)
    (all
      (ancestor old young-a)
      (ancestor old young-b))))

(define test-common-ancestor
  (lambda ()
    (exists (x)
      (equal?
        (solve 4 (common-ancestor 'pat 'ed x))
        '((pat ed john) (pat ed sam))))))

(printf "~s ~s~%" 'test-common-ancestor (test-common-ancestor))

(define younger-common-ancestor
  (relation _ (young-a young-b old not-so-old)
    (to-show young-a young-b old not-so-old)
    (all
      (common-ancestor young-a young-b not-so-old)
      (common-ancestor young-a young-b old)
      (ancestor old not-so-old))))

(define test-younger-common-ancestor
  (lambda ()
    (exists (x)
      (equal?
        (solve 4 (younger-common-ancestor 'pat 'ed 'john x))
        '((pat ed john sam))))))

(printf "~s ~s~%" 'test-younger-common-ancestor (test-younger-common-ancestor))

(define youngest-common-ancestor
  (relation _ (young-a young-b not-so-old)
    (to-show young-a young-b not-so-old)
    (all
      (common-ancestor young-a young-b not-so-old)
      (exists (y)
        (fails (younger-common-ancestor young-a young-b not-so-old y))))))

(define test-youngest-common-ancestor
  (lambda ()
    (exists (x)
      (equal?
        (solve 4 (youngest-common-ancestor 'pat 'ed x))
        '((pat ed sam))))))

(printf "~s ~s~%" 'test-youngest-common-ancestor (test-youngest-common-ancestor))

(define test-Seres-Spivey
  (lambda ()
    (equal?
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
        (john carl)))))

(printf "~s ~s~%" 'test-Seres-Spiver (test-Seres-Spivey))

(define towers-of-hanoi
  (letrec
      ([move
         (extend-relation (a1 a2 a3 a4)
           (relation cut ()
             (to-show 0 _ _ _)
             cut)
           (relation _ (n a b c)
             (to-show n a b c)
             (exists (m)
               (all
                 (pred-call positive? n)
                 (fun-call - m n 1)
                 (move m a c b)
                 (pred-call printf "Move a disk from ~s to ~s~n" a b)
                 (move m c b a)))))])
    (relation _ (n)
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

(define test-compose-subst-5
  (lambda ()
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
          `(p (f ,y) b (g b)))))))

(printf "~s ~s~%" 'test-compose-subst-5 (test-compose-subst-5))

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

(define test-unify/pairs
  (lambda ()
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
            #f))))))

(printf "~s ~s~%" 'test-unify/pairs-eager (test-unify/pairs))

(define test-pathological
  (lambda ()
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
              empty-subst)))))))

;Baader & Snyder
(printf "~s ~s~%" 'test-unify/pathological-eager (test-pathological))

(define test-fun-resubst
  (lambda ()
    (equal?
      (concretize
        (let ([j (relation _ (x w z)
                   (to-show z)
                   (all
                     (fun-call (lambda () 4) x)
                     (fun-call (lambda () 3) w)
                     (fun-call (lambda (y) (cons x y)) z w)))])
          (exists (q) (solve 4 (j q)))))
      '(((4 . 3))))))

(printf "~s ~s~%" 'test-fun-resubst-eager (test-fun-resubst))

(define towers-of-hanoi-path
  (let ([steps '()])
    (let ([push-step (lambda (x y) (set! steps (cons `(,x ,y) steps)))])
      (letrec
        ([move
           (extend-relation (a1 a2 a3 a4)
             (relation cut ()
               (to-show 0 _ _ _)
               cut)
             (relation _ (n a b c)
               (to-show n a b c)
               (exists (m)
                 (all
                   (pred-call positive? n)
                   (fun-call - m n 1)
                   (move m a c b)
                   (pred-call push-step a b)
                   (move m c b a)))))])
        (relation _ (n path)
          (to-show n path)
          (begin
            (set! steps '())
            (any
              (fails (move n 'l 'm 'r))
              (== path (reverse steps)))))))))

(define test-towers-of-hanoi-path
  (lambda ()
    (equal?
      (exists (path)
        (solution (towers-of-hanoi-path 3 path)))
      '(3 ((l m) (l r) (m r) (l m) (r l) (r m) (l m))))))

(printf "~s ~s~%" 'test-towers-of-hanoi-path (test-towers-of-hanoi-path))

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

(define test-unify/pairs-lazy
  (lambda ()
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
            #f))))))

(printf "~s ~s~%" 'test-unify/pairs-lazy (test-unify/pairs-lazy))
(printf "~s ~s~%" 'test-fun-resubst-lazy (test-fun-resubst))
;Baader & Snyder
(printf "~s ~s~%" 'test-unify/pathological-lazy (test-pathological))

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
(define test-unify/pairs-oleg
  (lambda ()
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
        (list
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
          #t)))))
          
(printf "~s ~s~%" 'test-unify/pairs-oleg (test-unify/pairs-oleg))
(printf "~s ~s~%" 'test-fun-resubst-oleg (test-fun-resubst))

(define test-pathological
  (lambda ()
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
                  (subst-vars-recursively vars s))))))))))

;Baader & Snyder
(printf "~s ~s~%" 'test-unify/pathological-oleg (test-pathological))

(define concat
  (lambda (xs ys)
    (cond
      [(null? xs) ys]
      [else (cons (car xs) (concat (cdr xs) ys))])))

(define test-concat-as-function
  (lambda ()
    (equal?
      (concat '(a b c) '(u v))
      '(a b c u v))))

(printf "~s ~s~%" 'test-concat-as-function (test-concat-as-function))

(define test-fun-concat
  (lambda ()
    (exists (q)
      (equal?
        (solve 1 (fun-call concat q '(a b c) '(u v)))
        '(((a b c u v) (a b c) (u v)))))))

(define concat
  (extend-relation (a1 a2 a3)
    (fact (xs) '() xs xs)
    (relation _ (x xs ys zs)
      (to-show `(,x . ,xs) ys `(,x . ,zs))
      (concat xs ys zs))))

(define test-concat
  (lambda ()
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
          ((x.0 x.1 x.2 x.3 x.4) () (x.0 x.1 x.2 x.3 x.4)))))))

(time (printf "~s ~s~%" 'test-concat (test-concat)))

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
  (relation _ (g v t w type-w)
    (to-show `(non-generic ,w ,type-w ,g) v t)
    (all! (unequal? w v) (instantiated g) (env g v t))))

(define env (extend-relation (a1 a2 a3)
              non-generic-match-env non-generic-recursive-env))

(define unequal?
  (extend-relation (a1 a2)
    (relation cut (a)
      (to-show a a)
      (all cut fail))
    (relation _ (a b)
      (to-show a b)
      (fails fail))))

(define fix  ;;; this is so that students can see what happens
  (lambda (e)
    (e (lambda (z) ((fix e) z)))))

(define generic-base-env
  (relation _ (g v targ tresult t)
    (to-show `(generic ,v (--> ,targ ,tresult) ,g) v t)
    (all! (fun-call instantiate t `(--> ,targ ,tresult)))))

(define generic-recursive-env
  (relation cut (g v w type-w t)
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
  (relation _ (g v t)
    (to-show g `(var ,v) t)
    (all! (env g v t))))

(define int-rel
  (fact (g x) g `(intc ,x) int))

(define bool-rel
  (fact (g x) g `(boolc ,x) bool))

(define zero?-rel
  (relation _ (g x)
    (to-show g `(zero? ,x) bool)
    (all! (!- g x int))))

(define sub1-rel
  (relation _ (g x)
    (to-show g `(sub1 ,x) int)
    (all! (!- g x int))))

(define +-rel
  (relation _ (g x y)
    (to-show g `(+ ,x ,y) int)
    (all! (!- g x int) (!- g y int))))

(define if-rel
  (relation _ (g t test conseq alt)
    (to-show g `(if ,test ,conseq ,alt) t)
    (all! (!- g test bool) (!- g conseq t) (!- g alt t))))

(define lambda-rel
  (relation _ (g v t body type-v)
    (to-show g `(lambda (,v) ,body) `(--> ,type-v ,t))
    (all! (!- `(non-generic ,v ,type-v ,g) body t))))

(define app-rel
  (relation _ (g t rand rator)
    (to-show g `(app ,rator ,rand) t)
    (exists (t-rand)
      (all! (!- g rator `(--> ,t-rand ,t)) (!- g rand t-rand)))))

(define fix-rel
  (relation _ (g rand t)
    (to-show g `(fix ,rand) t)
    (all! (!- g rand `(--> ,t ,t)))))

(define polylet-rel
  (relation _ (g v rand body t)
    (to-show g `(let ([,v ,rand]) ,body) t)
    (exists (t-rand)
      (all!
        (!- g rand t-rand)
        (!- `(generic ,v ,t-rand ,g) body t)))))

(define !-
  (extend-relation (a1 a2 a3)
    var-rel int-rel bool-rel zero?-rel sub1-rel +-rel 
    if-rel lambda-rel app-rel fix-rel polylet-rel))

(define test-!-1
  (lambda ()
    (and
      (equal?
        (exists (g) (solution (!- g '(intc 17) int)))
        '(g.0 (intc 17) int))
      (equal?
        (exists (g ?) (solution (!- g '(intc 17) ?)))
        '(g.0 (intc 17) int)))))

(printf "~s ~s~%" 'ints-and-bools (test-!-1))

(define test-!-zero?
  (lambda ()
    (equal?
      (exists (g ?) (solution (!- g '(zero? (intc 24)) ?)))
      '(g.0 (zero? (intc 24)) bool))))

(printf "~s ~s~%" 'arithmetic-primitives (test-!-zero?))

(define test-!-sub1
  (lambda ()
    (equal?
      (exists (g ?) (solution (!- g '(zero? (sub1 (intc 24))) ?)))
      '(g.0 (zero? (sub1 (intc 24))) bool))))
    
(printf "~s ~s~%" 'arithmetic-primitives (test-!-sub1))

(define test-!-+
  (lambda ()
    (equal?
      (exists (g ?)
        (solution
          (!- g '(zero? (sub1 (+ (intc 18) (+ (intc 24) (intc 50))))) ?)))
      '(g.0 (zero? (sub1 (+ (intc 18) (+ (intc 24) (intc 50))))) bool))))

(printf "~s ~s~%" 'arithmetic-primitives (test-!-+))

(define test-!-2
  (lambda ()
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
        '(g.0 (zero? (sub1 (+ (intc 18) (+ (intc 24) (intc 50))))) bool)))))

(printf "~s ~s~%" 'arithmetic-primitives (test-!-2))

(define test-!-3
  (lambda ()
    (equal?
      (exists (?)
        (solution (!- '() '(if (zero? (intc 24)) (intc 3) (intc 4)) ?)))
      '(() (if (zero? (intc 24)) (intc 3) (intc 4)) int))))

(printf "~s ~s~%" 'if-expressions (test-!-3))

(define test-!-3a
  (lambda ()
    (equal?
      (exists (g ?)
        (solution (!- g '(if (zero? (intc 24)) (zero? (intc 3)) (zero? (intc 4))) ?)))
      '(g.0 (if (zero? (intc 24)) (zero? (intc 3)) (zero? (intc 4))) bool))))

(printf "~s ~s~%" 'if-expressions (test-!-3a))

(define test-!-3
  (lambda ()
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
        '((non-generic b bool (non-generic a int g.0)) (zero? (var a)) bool)))))

(printf "~s ~s~%" 'variables (test-!-3))

(define test-!-4a
  (lambda ()
    (equal?
      (exists (g ?)
        (solution 
          (!- `(non-generic b bool (non-generic a int ,g))
            '(lambda (x) (+ (var x) (intc 5)))
            ?)))
      '((non-generic b bool (non-generic a int g.0))
        (lambda (x) (+ (var x) (intc 5)))
        (--> int int)))))

(printf "~s ~s~%" 'variables-4a (test-!-4a))

(define test-!-4b
  (lambda ()
    (equal?
      (exists (g ?)
        (solution 
          (!- `(non-generic b bool (non-generic a int ,g))
            '(lambda (x) (+ (var x) (var a)))
            ?)))
      '((non-generic b bool (non-generic a int g.0))
        (lambda (x) (+ (var x) (var a)))
        (--> int int)))))

(printf "~s ~s~%" 'variables-4b (test-!-4b))

(define test-!-4c
  (lambda ()
    (equal?
      (exists (g ?)
        (solution
          (!- g '(lambda (a) (lambda (x) (+ (var x) (var a)))) ?)))
      '(g.0 
         (lambda (a) (lambda (x) (+ (var x) (var a))))
         (--> int (--> int int))))))

(printf "~s ~s~%" 'variables-4c (test-!-4c))

(define test-!-5
  (lambda ()
    (list
      (equal?
        (exists (g ?)
          (solution
            (!- g (parse
                    '(lambda (f)
                       (lambda (x)
                         ((f x) x))))
              ?)))
        `(g.0 ,(parse '(lambda (f) (lambda (x) ((f x) x))))
           (-->
             (--> type-v.0 (--> type-v.0 t.0))
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
        #f))))

(printf "~s ~s~%" 'everything-but-polymorphic-let (test-!-5))

(define test-!-6
  (lambda ()
    (equal?
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
         int))))

(printf "~s ~s~%" 'polymorphic-let (test-!-6))

(define test-!-7
  (lambda ()
    (equal?
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
         int))))

(printf "~s ~s~%" 'with-robust-syntax (test-!-7)) 

(define test-!-8
  (lambda ()
    (equal?
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
         int))))

(printf "~s ~s~%" 'with-robust-syntax-but-long-jumps/poly-let (test-!-8))

(define test-!-9
  (lambda ()
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
           (--> int int))))))
        
(printf "~s ~s~%" 'type-inhabitation (test-!-9))

;;; long cuts

(define !-generator
  (lambda (long-cut)
    (letrec
      ([!- (extend-relation (a1 a2 a3)
             (relation _ (g v t)
               (to-show g `(var ,v) t)
               (all long-cut (env g v t)))
             (fact (g x) g `(intc ,x) int)
             (fact (g x) g `(boolc ,x) bool)
             (relation _ (g x)
               (to-show g `(zero? ,x) bool)
               (all long-cut (!- g x int)))
             (relation _ (g x)
               (to-show g `(sub1 ,x) int)
               (all long-cut (!- g x int)))
             (relation _ (g x y)
               (to-show g `(+ ,x ,y) int)
               (all long-cut (all! (!- g x int) (!- g y int))))
             (relation _ (g t test conseq alt)
               (to-show g `(if ,test ,conseq ,alt) t)
               (all long-cut
		 (all! (!- g test bool) (!- g conseq t) (!- g alt t))))
             (relation _ (g v t body type-v)
               (to-show g `(lambda (,v) ,body) `(--> ,type-v ,t))
               (all long-cut (!- `(non-generic ,v ,type-v ,g) body t)))
             (relation _ (g t rand rator)
               (to-show g `(app ,rator ,rand) t)
               (exists (t-rand)
                 (all long-cut
		   (all!
                     (!- g rator `(--> ,t-rand ,t))
                     (!- g rand t-rand)))))
             (relation _ (g rand t)
               (to-show g `(fix ,rand) t)
               (all long-cut (!- g rand `(--> ,t ,t))))
             (relation _ (g v rand body t)
               (to-show g `(let ([,v ,rand]) ,body) t)
               (exists (t-rand)
                 (all long-cut
		   (all!
                     (!- g rand t-rand)
                     (!- `(generic ,v ,t-rand ,g) body t))))))])
      !-)))

(define !-
  (relation cut (g exp t)
    (to-show g exp t)
    ((!-generator cut) g exp t)))

(printf "~s ~s~%" 'with-robust-syntax-but-long-jumps/poly-let (test-!-8))

(define invertible-binary-function->ternary-relation
  (lambda (op inverted-op)
    (extend-relation (a1 a2 a3)
      (relation _ (x y z)
        (to-show x y z)
        (all (fails (instantiated z)) (fun-call op z x y)))
      (relation _ (x y z)
        (to-show x y z)
        (all (fails (instantiated y)) (fun-call inverted-op y z x)))
      (relation _ (x y z)
        (to-show x y z)
        (all (fails (instantiated x)) (fun-call inverted-op x z y)))
      (relation _ (x y z)
        (to-show x y z)
        (fun-call op z x y)))))

(define ++ (invertible-binary-function->ternary-relation + -))
(define -- (invertible-binary-function->ternary-relation - +))
(define ** (invertible-binary-function->ternary-relation * /))
(define // (invertible-binary-function->ternary-relation / *))

(define test-instantiated-1
  (lambda ()
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
        '(10 7 3)))))

(printf "~s ~s~%" 'test-instantiated-1 (test-instantiated-1))

(define symbol->lnum
  (lambda (sym)
    (map char->integer (string->list (symbol->string sym)))))

(define lnum->symbol
  (lambda (lnums)
    (string->symbol (list->string (map integer->char lnums)))))

(define invertible-unary-function->binary-relation
  (lambda (op inverted-op)
    (extend-relation (a1 a2)
      (relation _ (x y)
        (to-show x y)
        (all (fails (instantiated y)) (fun-call op y x)))
      (relation _ (x y)
        (to-show x y)
        (all (fails (instantiated x)) (fun-call inverted-op x y)))
      (relation _ (x y)
        (to-show x y)
        (begin (pretty-print "Third rule") (fun-call op y x))))))

(define name
  (invertible-unary-function->binary-relation symbol->lnum lnum->symbol))

(define test-instantiated-2
  (lambda ()
    (and
      (equal?
        (exists (x) (solution (name 'sleep x)))
        '(sleep (115 108 101 101 112)))
      (equal?
        (exists (x) (solution (name x '(115 108 101 101 112))))
        '(sleep (115 108 101 101 112)))
      (equal?
        (exists (x) (solution (name 'sleep '(115 108 101 101 112))))
        '(sleep (115 108 101 101 112))))))

(printf "~s ~s~%" 'test-instantiated-2 (test-instantiated-2))

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

(pretty-print (exists (x y) (solve 5 (grandpa x y))))

(define father-pete-sal (fact () 'pete 'sal))
(define father-sam-pete (fact () 'sam 'pete))
(define father-john-sam (fact () 'john 'sam))
(define father (extend-relation (a1 a2) father-john-sam father-sam-pete father-pete-sal))

(pretty-print (exists (x y) (solve 5 (grandpa x y))))
(pretty-print (exists (x y) (solve 5 (grandpa 'sam y))))
(pretty-print (exists (x y) (solve 5 (grandpa x 'sal))))

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

(pretty-print (exists (x y) (solve 5 (grandpa-sam 'sal))))

(pretty-print (exists (x y) (solve 5 (grandpa-sam 'sal))))

(define grandpa-sam
  (relation cut (child)
    (to-show child)
    (exists (x)
      (all (father 'sam x) (father x child)))))

(pretty-print (exists (x y) (solve 5 (grandpa-sam 'sal))))

(define-syntax fact
  (syntax-rules ()
    [(_ (ex ...) x ...)
     (relation _ (ex ...) (to-show x ...))]))

(define father-pete-sal (fact () 'pete 'sal))
(define father-sam-pete (fact () 'sam 'pete))
(define father-john-sam (fact () 'john 'sam))
(define father (extend-relation (a1 a2) father-john-sam father-sam-pete father-pete-sal))

(pretty-print (exists (x y) (solve 5 (grandpa-sam 'sal))))

(define father-pete-sal
  (relation cut () (to-show 'pete 'sal)))

(define father-sam-pete
  (relation cut () (to-show 'sam 'pete)))

(define father-johh-sam
  (relation cut () (to-show 'john 'sam)))

(define father (extend-relation (a1 a2) father-john-sam father-sam-pete father-pete-sal))

(pretty-print (exists (x y) (solve 5 (grandpa-sam 'sal))))

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
    (relation _ (x y t1 t2)
      (to-show t1 t2)
      (== t1 `(s ,x))
      (== t2 `(s ,y))
      (Rinf x y))))
(printf "~%Rinf:~%")
(pretty-print (exists (x y) (solve 5 (Rinf x y))))
(printf "~%Rinf+R1: Rinf starves R1:~%")
(pretty-print 
  (exists (x y) (solve 5
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

(printf "~%binary-extend-relation-interleave~%")
(printf "~%Rinf+R1:~%")
(pretty-print 
  (exists (x y) (solve 7
		  ((binary-extend-relation-interleave (a1 a2) Rinf R1) x y))))
(printf "~%R1+RInf:~%")
(pretty-print 
  (exists (x y) (solve 7
		  ((binary-extend-relation-interleave (a1 a2) R1 Rinf) x y))))

(printf "~%R2+R1:~%")
(pretty-print 
  (exists (x y) (solve 7
		  ((binary-extend-relation-interleave (a1 a2) R2 R1) x y))))
(printf "~%R1+fact3:~%")
(pretty-print 
  (exists (x y) (solve 7
		  ((binary-extend-relation-interleave (a1 a2) R1 fact3) x y))))
(printf "~%fact3+R1:~%")
(pretty-print 
  (exists (x y) (solve 7
		  ((binary-extend-relation-interleave (a1 a2) fact3 R1) x y))))

;;; Test for nonoverlapping.

(printf "~%binary-extend-relation-interleave-non-overlap~%")
(printf "~%R1+R2:~%")
(pretty-print 
  (exists (x y) 
    (solve 10 
      ((binary-extend-relation-interleave-non-overlap (a1 a2) R1 R2) x y))))
(printf "~%R2+R1:~%")
(pretty-print 
  (exists (x y) 
    (solve 10 
      ((binary-extend-relation-interleave-non-overlap (a1 a2) R2 R1) x y))))
(printf "~%Rinf+R1:~%")
(pretty-print 
  (exists (x y)
    (solve 7
      ((binary-extend-relation-interleave-non-overlap (a1 a2) Rinf R1) x y))))
(printf "~%R1+RInf:~%")
(pretty-print 
  (exists (x y) 
    (solve 7
      ((binary-extend-relation-interleave-non-overlap (a1 a2) R1 Rinf) x y))))

; Infinitary relation Rinf2
; r(z,z).
; r(s(s(X)),s(s(Y))) :- r(X,Y).
; Rinf2 overlaps with Rinf in the infinite number of points

(define Rinf2
  (extend-relation (a1 a2)
    (fact () 'z 'z)
    (relation _ (x y t1 t2)
      (to-show t1 t2)
      (== t1 `(s (s ,x)))
      (== t2 `(s (s ,y)))
      (Rinf2 x y))))
(printf "~%Rinf2:~%")
(pretty-print (exists (x y) (solve 5 (Rinf2 x y))))
(printf "~%Rinf+Rinf2~%")
(pretty-print 
  (exists (x y)
    (solve 9
      ((binary-extend-relation-interleave-non-overlap 
	 (a1 a2) Rinf Rinf2) x y))))
(printf "~%Rinf2+Rinf~%")
(pretty-print 
  (exists (x y)
    (solve 9
      ((binary-extend-relation-interleave-non-overlap 
	 (a1 a2) Rinf2 Rinf) x y))))


; nrev([],[]).
; nrev([X|Rest],Ans) :- nrev(Rest,L), append(L,[X],Ans).

; append([],L,L).
; append([X|L1],L2,[X|L3]) :- append(L1,L2,L3).


; data([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
;                            21,22,23,24,25,26,27,28,29,30]).


(define nrev
  (extend-relation (a1 a2)
    (fact () '() '())
    (relation _ (x rest ans)
      (to-show `(,x . ,rest) ans)
      (exists (ls)
        (all
          (nrev rest ls)
          (concat ls `(,x) ans))))))

(define test-nrev
  (lambda ()
    (time
      (exists (x)
        (solution (nrev '(1 2 3 4 5 6 7 8 9
                           10 11 12 13 14 15 16 17 18
                           19 20 21 22 23 24 25 26 27
                           28 29 30)
                    x))))))

(printf "Timing test ~s~n" (test-nrev))

(define get_cpu_time
  (lambda ()
    (vector-ref (statistics) 1)))

(define lots
  (extend-relation ()
    (relation _ ()
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
  (relation _ (count)
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
    (relation $ (count)
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
    (relation $ (count)
      (to-show count)
      (repeat count)
      (dummy _)
      fail)
    (fact () _)))

(define dummy
  (relation $ ()
    (to-show _)))

(define repeat
  (extend-relation (a1)
    (fact (n) n)
    (relation _ (n)
      (to-show n)
      (exists (n1)
        (all
          (pred-call > n 1)
          (fun-call - n1 n 1)
          (repeat n1))))))

(define report
  (relation _ (count t0 t1 t2)
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
    (relation cut (count time lips)
      (to-show count time lips 'msecs)
      (== time 0)
      cut
      (== lips 0))
    (relation _ (count time lips)
      (to-show count time lips 'msecs)
      (exists (t1 t2)
        (all
          (fun-call * t1 496 count 1000)
          (fun-call + t2 time 0.0)
          (fun-call / lips t1 t2))))))

;(test-lots)

#!eof

