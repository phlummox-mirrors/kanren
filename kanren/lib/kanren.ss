; From dfried@cs.indiana.edu Tue May 27 07:31:50 2003
; Message-ID: <200305270731.h4R7Vlq18608@bullshark.cs.indiana.edu>
; To: oleg@pobox.com
; Subject: Re: Essentials of Constraint Programming 
; In-Reply-To: Your message of "Sun, 30 Mar 2003 14:55:37 PST."
;              <200303302255.h2UMtbwr018647@adric.fnmoc.navy.mil> 
; X-Mailer: MH-E 7.2; nmh 1.0.4; GNU Emacs 20.5.1
; Date: Tue, 27 May 2003 02:31:47 -0500
; From: Dan Friedman <dfried@cs.indiana.edu>
; Status: RO

; I am using your clever unifier that does cars/cdrs by introducing
; logic variables.  I decided that it is the most elegant.  But, I
; cannot get it to work in my new version.  Specifically, I can't get
; it to work for my type inferencer.  I have no clue why?  Would
; you be willing to look at it?

; ... Dan

; I am inclosing the file, just in case.  It all works until I
; get to adding lambda expressions.

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

;;;; quasiquote has been coded by Oscar Waddell.
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

(define compose-subst*
  (lambda (s x t)
    (cond
      [(assv x s) =>
       (lambda (pr)
         (let ([q (commitment->term pr)])
           (if (lv? q)
               (compose-subst s (unit-subst q t))
               (unify q t s))))]
      [else (compose-subst s (unit-subst x t))])))

(define calls-to-unify2 0)

(define unify2
  (lambda (d t s)
    (set! calls-to-unify2 (add1 calls-to-unify2))
    (unify d t s)))

(define printff printf)
;(define-syntax printff (syntax-rules () [(_ x ...) (void)]))
'(define write
  (lambda (x . p)
    (if (null? p)
      (begin
        (pretty-print x)
        (newline))
      (begin
        (pretty-print x (car p))
        (newline (car p))))))
(define-record lv (name) ())
(define lv make-lv)

(print-gensym #f)
; (define lv
;   (lambda (name)
;     (cons 'lv name)))
; (define lv?
;   (lambda (x)
;     (and (pair? x) (eqv? (car x) 'lv))))
; (define lv-name
;   (lambda (x)
;     (if (lv? x) (cdr x) (error 'lv-name "Invalid Logic Variable: ~s" x))))
;;; ------------------------------------------------------

'(define-syntax define
  (syntax-rules ()
    [(_ x y) (begin (write 'x) (newline) (set! x y))]))

(define copy-term
  (lambda (var-fn)
    (letrec
      ([copy-term
         (lambda (t env k)
           (cond
             [(lv? t) (var-fn t env k)]
             [(pair? t)
              (copy-term (car t) env
                (lambda (a-t env)
                  (copy-term (cdr t) env
                    (lambda (d-t env)
                      (k (cons a-t d-t) env)))))]
             [else (k t env)]))])
      (lambda  (term)
        (copy-term term '() (lambda (t env) t))))))

(define concretize
  (copy-term
    (lambda (t env k)
      (cond
        [(assv t env)
         => (lambda (pr)
              (k (cadr pr) env))]
        [else (let ([tname (lv-name t)])
                (let ([c (let ([pr (assv/lv-name tname env)])
                           (+ (if (not pr) 0 (cddr pr)) 1))])
                  (let ([name (artificial-name tname c)])
                    (k name (cons `(,t . (,name . ,c)) env)))))]))))

(define artificial-name
  (lambda (name c)
    (string->symbol
      (string-append (symbol->string name) "." (number->string c)))))

(define assv/lv-name
  (lambda (name env)
    (cond
      [(null? env) #f]
      [(eqv? (lv-name (caar env)) name) (car env)]
      [else (assv/lv-name name (cdr env))])))

(define-syntax exists ;;; can never change this to a lets
  (syntax-rules ()
    [(_ (name ...) body0 body1 ...)
     (let ([name (lv 'name)] ...) body0 body1 ...)]))

(define _ (exists (_) _))

(define-syntax lambda@
  (syntax-rules ()
    [(_ () body0 body1 ...) (begin body0 body1 ...)]
    [(_ (formal0 formal1 ...) body0 body1 ...)
     (lambda (formal0)
       (lambda@ (formal1 ...) body0 body1 ...))]))

(define-syntax trace-lambda@
  (syntax-rules ()
    [(_ name () body0 body1 ...) (begin body0 body1 ...)]
    [(_ name (formal0 formal1 ...) body0 body1 ...)
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

(printff "~s ~s~%" 'test-@-lambda@ (test-@-lambda@))

(define empty-subst '())

(define empty-subst? null?)

(define compose-subst
  (lambda (base refining)
    (cond
      [(empty-subst? base) refining]
      [(empty-subst? refining) base]
      [else (refine base refining refining)])))

(define refine
  (lambda (base refining refining-survivors)
    (cond
      [(null? base) refining-survivors]
      [else (cons-if-real-commitment
              (commitment->var (car base))
              (nonempty-subst-in (commitment->term (car base)) refining)
              (refine (cdr base) refining
                (cond
                  [(assv (commitment->var (car base)) refining-survivors)
                   => (lambda (c) (remv c refining-survivors))]
                  [else refining-survivors])))])))

(define commitment list)             ;;; change to cons
(define commitment->term cadr)       ;;; and change to cdr
(define commitment->var car)

(define cons-if-real-commitment
  (lambda (lv term refined)
    (cond
      [(eqv? term lv) refined]
      [else (cons (commitment lv term) refined)])))

(define nonempty-subst-in
  (lambda (t subst)
    (cond
      [(lv? t)
       (cond
         [(assv t subst) => commitment->term]
         [else t])]
      [else t])))

(define subst-in
  (lambda (t subst)
    (cond
      [(empty-subst? subst) t]
      [else (nonempty-subst-in t subst)])))

(define unit-subst
  (lambda (var t)
    (if (or (eq? var t) (eq? var _)) empty-subst (list (commitment var t)))))

(define test-compose-subst-1
  (lambda ()
    (equal?
      (concretize
        (exists (x y)
          (let ([s (compose-subst (unit-subst x y) (unit-subst y 52))])
            (subst-in x s))))
      52)))

(printff "~s ~s~%" 'test-compose-subst-1 (test-compose-subst-1))

(define test-compose-subst-2
  (lambda ()
    (equal?
      (concretize
        (exists (w x y)
          (let ([s (compose-subst (unit-subst y w) (unit-subst w 52))])
            (let ([r (compose-subst (unit-subst x y) s)])
              (subst-in x r)))))
      52)))

(printff "~s ~s~%" 'test-compose-subst-2 (test-compose-subst-2))

(define test-compose-subst-3
  (lambda ()
    (equal?
      (concretize
        (exists (w x y)
          (let ([s (compose-subst (unit-subst w 52) (unit-subst y w))])
            (let ([r (compose-subst (unit-subst x y) s)])
              (subst-in x r)))))
      'w.1)))

(printff "~s ~s~%" 'test-compose-subst-3 (test-compose-subst-3))

(define test-compose-subst-4
  (lambda ()
    (equal?
      (concretize
        (exists (x y z)
          (let ([s (compose-subst (unit-subst y z) (unit-subst x y))]
                [r (compose-subst
		     (compose-subst (unit-subst x 'a) (unit-subst y 'b))
		     (unit-subst z y))])
            (write (concretize s))
            (write (concretize r))
            (newline)
            (compose-subst s r))))
      (begin
	`(,(commitment 'x.1 'y.1)
	  ,(commitment 'y.1 'z.1))
	`(,(commitment 'x.1 'a)
	  ,(commitment 'y.1 'b)
	  ,(commitment 'z.1 'y.1))
	`(,(commitment 'x.1 'b)
	  ,(commitment 'z.1 'y.1))))))
  
(printff "~s ~s~%" 'test-compose-subst-4 (test-compose-subst-4))

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
      [(or (eqv? t u) (eqv? t _) (eqv? u _)) empty-subst]
      [(lv? t) (unit-subst t u)]
      [(lv? u) (unit-subst u t)]
      [else #f])))

(define test-nonrecursive-unify
  (lambda ()
    (and
      (equal?
        (concretize
          (exists (x)
            (unify x 3 empty-subst)))
        `(,(commitment 'x.1 3)))
      (equal?
        (concretize
          (exists (y)
            (unify 4 y empty-subst)))
        `(,(commitment 'y.1 4)))
      (equal?
        (concretize
          (exists (x y)
            (unify x y empty-subst)))
        `(,(commitment 'x.1 'y.1)))
      (equal?
        (unify 'x 'x empty-subst)
        '())
      (equal?
        (concretize
          (exists (x)
            (unify x x empty-subst)))
        '())
      (equal?
        (unify 4 'y empty-subst)
        #f)
      (equal?
        (unify 'x 3 empty-subst)
        #f)
      (equal?
        (unify 3 4 empty-subst)
        #f))))

(printff "~s ~s~%" 'test-nonrecursive-unify (test-nonrecursive-unify))

(define initial-fk (lambda () '()))
(define initial-sk
  (lambda@ (fk subst cut)
    (cons subst fk)))

(define failer (lambda (succk fk) (fk)))

(define-syntax unify-incrementally
  (lambda (w)
    (syntax-case w (quote quasiquote)
      [(_ subst () ())
       (syntax (lambda (succk fk) (succk subst)))]
      [(_ subst (c0 c1 ...) (t-lexvar0 t-lexvar1 ...)) ;;; c0 is anything
       (syntax
         (let ([subst (unify t-lexvar0 c0 subst)]) ;;; must be a let
           (if subst
               (unify-incrementally subst (c1 ...) (t-lexvar1 ...))
               failer)))])))

(define !!
  (lambda (exiting-fk)
    (lambda@ (sk fk subst cutk)
      (@ sk exiting-fk subst cutk))))

(define-syntax relation
  (syntax-rules (show)
    [(_ (var ...) (c0 ...) (show cut (var-ant ...) ant))
     (relation-aux () (c0 ...) (var ...) (c0 ...) (show cut (var-ant ...) ant))]))

(define-syntax relation-aux
  (syntax-rules (show)
    [(_ (acc0 ...) () (var ...) c0s (show cut (var-ant ...) ant))
     (lambda (acc0 ...)
       (lambda (sk)
         (lambda (fk)
           (lambda (entering-subst)
             (lambda (cutk)
               (let ([cut (!! cutk)])
                 (exists (var ...)
                   ((unify-incrementally entering-subst c0s (acc0 ...))
                      (lambda (subst) (@ (exists (var-ant ...) ant) sk fk subst cutk))
                      fk))))))))]
    [(_ (acc0 ...) (x0 x1 ...) (var ...) c0s (show cut (var-ant ...) ant))
     (relation-aux (acc0 ... g) (x1 ...) (var ...) c0s (show cut (var-ant ...) ant))]))

(define extend-relation ;;; This should be a macro, too, and it is close.
  (lambda (relation1 relation2)
    (lambda args
      (lambda (sk)
        (lambda (fk)
          (lambda (subst)
            (lambda (cut)
            (@ (apply relation1 args)
               sk
               (lambda () (@ (apply relation2 args) sk fk subst cut))
               subst
               cut))))))))

(define-syntax all
  (syntax-rules ()
    [(_) (lambda (sk) sk)]))

(define test-unify-incrementally
  (lambda () 
    (equal?
      (concretize
        (exists (x y z)
          (let ([s (compose-subst
		     (compose-subst (unit-subst x 2) (unit-subst y 3))
		     (unit-subst z 4))])
            ((unify-incrementally s (x y z) (2 3 4))
             (lambda (subst) subst)
             (lambda () '())))))
      `(,(commitment 'x.1 2)
	,(commitment 'y.1 3)
	,(commitment 'z.1 4)))))

(printff "~s ~s~%" 'test-unify-incrementally (test-unify-incrementally))

(define father  
  (relation () ('john 'sam) (show cut () (all))))

(printff "~s ~s~%" 'test-father0
  (let ([result
          (@ (father 'john 'sam)
             initial-sk initial-fk empty-subst initial-fk)])
    (and
      (equal? (car result) '())
      (equal? ((cdr result)) '()))))

(define child-of-male
  (relation (child dad) (child dad) (show cut () (father dad child))))

(define test-child-of-male-0
  (lambda ()
    (equal?
      (concretize
        (car (@ (child-of-male 'sam 'john)
                initial-sk initial-fk empty-subst initial-fk)))
      `(,(commitment 'child.1 'sam) ,(commitment 'dad.1 'john)))))

(printff "~s ~s~%" 'test-child-of-male-0 (test-child-of-male-0))

(define father2
  (relation () ('pete 'sal) (show cut  () (all))))

(define new-father
  (extend-relation father father2))

(define test-father-1
  (lambda ()
    (let ([result
            (@ (new-father 'pete 'sal)
               initial-sk initial-fk empty-subst initial-fk)])
      (and
        (equal? (car result) '())
        (equal? ((cdr result)) '())))))

(printff "~s ~s~%" 'test-father-1 (test-father-1))

(define query
  (let ([initial-fk (lambda () '())]
        [initial-sk (lambda (fk) (lambda (subst) (lambda (cut)
                                            (cons subst fk))))])
    (lambda (antecedent)
      (@ antecedent initial-sk initial-fk empty-subst initial-fk))))

(define test-father-2
  (lambda ()
    (let ([result (concretize
                    (exists (x)
                      (query (new-father 'pete x))))])
      (and
        (equal? (car result) `(,(commitment 'x.1 'sal)))
        (equal? ((cdr result)) '())))))

(printff "~s ~s~%" 'test-father-2 (test-father-2))

(define test-father-3
  (lambda ()
    (equal?
      (concretize
        (exists (x)
          (let ([term (list 'pete x)])
            (let ([answer (query (new-father 'pete x))])
              (map (lambda (t) (subst-in t (car answer))) term)))))
      '(pete sal))))

(printff "~s ~s~%" 'test-father-3 (test-father-3))

(define test-father-4
  (lambda ()
    (equal?
      (concretize
        (exists (x y)
          (let ([term (list x y)])
            (let ([answer (query (new-father x y))])
              (map (lambda (t) (subst-in t (car answer))) term)))))
      '(john sam))))

(printff "~s ~s~%" 'test-father-4 (test-father-4))

(define pete/pat
  (relation () ('pete 'pat) (show cut  () (all))))

(define newer-father
  (extend-relation new-father pete/pat))

(define test-father-5
  (lambda ()
    (and
      (equal?
        (concretize
          (exists (x)
            (let ([term (list 'pete x)])
              (let ([answer1 (query (newer-father 'pete x))])
                (write '***)
                (write answer1)
                (newline)
                (list
                  (map (lambda (t) (subst-in t (car answer1))) term)
                  (let ([answer2 ((cdr answer1))])
                    (map (lambda (t) (subst-in t (car answer2))) term)))))))
        '((pete sal) (pete pat)))
      (equal?
        (concretize
          (exists (x)
            (let ([term (list 'pete x)])
              (let ([answer1 (query (newer-father 'pete x))])
                (cons
                  (map (lambda (t) (subst-in t (car answer1))) term)
                  (let ([answer2 ((cdr answer1))])
                    (cons
                      (map (lambda (t) (subst-in t (car answer2))) term)
                      (let ([answer3 ((cdr answer2))])
                        (if (null? answer3)
                            '()
                            (cons 
                              (map (lambda (t) (subst-in t (car answer3))) term)
                              '()))))))))))
        '((pete sal) (pete pat))))))
      
(printff "~s ~s~%" 'test-father-5 (test-father-5))

(define stream-prefix
  (lambda (n strm)
    (if (null? strm) '()
      (cons (car strm)
        (if (zero? n) '()
          (stream-prefix (- n 1) ((cdr strm))))))))

(define-syntax solve
  (syntax-rules ()
    [(_ n (rel t0 ...))
     (concretize
       (map (lambda (subst)
              (list (subst-in t0 subst) ...))
         (stream-prefix (- n 1) (query (rel t0 ...)))))]))

(define sam/pete
  (relation () ('sam 'pete) (show cut  () (all))))

(define newest-father (extend-relation newer-father sam/pete))

(define test-father-6/solve
  (lambda ()
    (and
      (equal?
        (exists (x) (solve 5 (newest-father 'pete x)))
        '((pete sal) (pete pat)))
      (equal?
        (exists (x y) (solve 6 (newest-father x y)))
        '((john sam) (pete sal) (pete pat) (sam pete))))))
            
(printff "~s ~s~%" 'test-father-6/solve (test-father-6/solve))

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

(printff "~s ~s~%" 'test-father-7/solution (test-father-7/solution))

(define query-apply
  (lambda (rel t*)
    (let ([ans (query (apply rel t*))])
      (if (null? (cdr ans))
        #f
        (concretize
          (map (lambda (t) (subst-in t (car ans))) t*))))))

(define test-father-7/query-apply
  (lambda ()
    (equal?
      (exists (x) (query-apply newest-father `(pete ,x)))
      '(pete sal))))

(printff "~s ~s~%" 'test-father-7/query-apply (test-father-7/query-apply))

(define grandpa-sam
  (relation (grandchild) (grandchild)
    (show cut  (parent)
      (lambda (sk)
        ((newest-father 'sam parent)
         ((newest-father parent grandchild) sk))))))

(define test-grandpa-sam-1
  (lambda ()
    (equal?
      (exists (y) (solve 6 (grandpa-sam y)))
      '((sal) (pat)))))

(printff "~s ~s~%" 'test-grandpa-sam-1 (test-grandpa-sam-1))

(define-syntax all
  (syntax-rules ()
    [(_) (lambda (sk) sk)]
    [(_ antecedent0) antecedent0]
    [(_ antecedent0 antecedent1 ...)
     (lambda (sk)
       (antecedent0 ((all antecedent1 ...) sk)))]))

'(define-syntax any ;;; haven't thought about this one yet.
  (syntax-rules ()
    [(_ antecedent ...)
     ((relation () (select ((to-show) antecedent) ...)))]))

(define child
  (relation (child dad) (child dad)
    (show cut () (newest-father dad child))))

(define test-child-1
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (child x y)))
      '((sam john) (sal pete) (pat pete) (pete sam)))))

(printff "~s ~s~%" 'test-child-1 (test-child-1))

(define grandpa-sam
  (relation (grandchild) (grandchild)
    (show cut (parent)
      (all
        (newest-father 'sam parent)
        (newest-father parent grandchild)))))

(define test-grandpa-sam-2
  (lambda ()
    (equal?
      (exists (y) (solve 6 (grandpa-sam y)))
      '((sal) (pat)))))

(printff "~s ~s~%" 'test-grandpa-sam-2 (test-grandpa-sam-2))

(define grandpa-maker
  (lambda (grandad)
    (relation (grandchild) (grandchild)
      (show cut (parent)
        (all
          (newest-father grandad parent)
          (newest-father parent grandchild))))))

(define test-grandpa-maker-1
  (lambda ()
    (equal?
      (exists (x) (solve 6 ((grandpa-maker 'sam) x)))
      '((sal) (pat)))))     

(printff "~s ~s~%" 'test-grandpa-maker-1 (test-grandpa-maker-1))

(define grandpa-maker
  (lambda (guide* grandad*)
    (relation (grandchild) (grandchild)
      (show cut (parent)
        (all
          (guide* grandad* parent)
          (guide* parent grandchild))))))

(define test-grandpa-maker-2
  (lambda ()
    (equal?
      (exists (x) (solve 4 ((grandpa-maker newest-father 'sam) x)))
      '((sal) (pat)))))

(printff "~s ~s~%" 'test-grandpa-maker-2 (test-grandpa-maker-2))

(define grandpa
  (relation (grandad grandchild) (grandad grandchild)
    (show cut (parent)
      (all
        (newest-father grandad parent)
        (newest-father parent grandchild)))))

(define test-grandpa-1
  (lambda ()
    (equal?
      (exists (x) (solve 4 (grandpa 'sam x)))
      '((sam sal) (sam pat)))))

(printff "~s ~s~%" 'test-grandpa-1 (test-grandpa-1))

(define-syntax fact
  (syntax-rules ()
    [(_ (var ...) x ...) (relation (var ...) (x ...) (show cut () (all)))]))

(define father
  (extend-relation
    (fact () 'john 'sam)
    (extend-relation
      (fact () 'sam 'pete)
      (extend-relation
        (fact () 'sam 'polly)
        (extend-relation
          (fact () 'pete 'sal)
          (fact () 'pete 'pat))))))

(define mother
  (extend-relation
    (fact () 'polly 'betty)
    (fact () 'polly 'david)))

(define grandpa
  (extend-relation
    (relation (grandad grandchild) (grandad grandchild)
      (show cut (parent)
        (all
          (father grandad parent)
          (father parent grandchild))))
    (relation (grandad grandchild) (grandad grandchild)
      (show cut (parent)
        (all
          (father grandad parent)
          (mother parent grandchild))))))

(define test-grandpa-2
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa 'sam y)))
      '((sam sal) (sam pat) (sam betty) (sam david)))))

(printff "~s ~s~%" 'test-grandpa-2 (test-grandpa-2))

(define grandpa/father
  (relation (grandad grandchild) (grandad grandchild)
    (show cut (parent)
      (all
        (father grandad parent)
        (father parent grandchild)))))

(define grandpa/mother
  (relation (grandad grandchild) (grandad grandchild)
    (show cut (parent)
      (all
        (father grandad parent)
        (mother parent grandchild)))))

(define grandpa
  (extend-relation grandpa/father grandpa/mother))

(define test-grandpa-5
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa 'sam y)))
      '((sam sal) (sam pat) (sam betty) (sam david)))))

(printff "~s ~s~%" 'test-grandpa-5 (test-grandpa-5))

(define grandpa-sam
  (let ([r (relation (child) (child)
              (show cut (parent)
                (all
                  (father 'sam parent)
                  (father parent child))))])
    (relation (child) (child)
      (show cut () (r child)))))

(define test-grandpa-sam-4
  (lambda ()
    (equal?
      (exists (y) (solve 6 (grandpa-sam y)))
      '((sal) (pat)))))

(printff "~s ~s~%" 'test-grandpa-sam-4 (test-grandpa-sam-4))  

(define grandpa/father
  (relation (grandad grandchild) (grandad grandchild)
    (show cut (parent)
      (all
        (father grandad parent)
        (father parent grandchild)
        cut))))

(define grandpa/mother
  (relation (grandad grandchild) (grandad grandchild)
    (show cut (parent)
      (all
        (father grandad parent)
        (mother parent grandchild)))))

(define grandpa
  (extend-relation grandpa/father grandpa/mother))

(define test-grandpa-8
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa x y)))
      '((john pete)))))

(printff "~s ~s~%" 'test-grandpa-8 (test-grandpa-8))

(define grandpa/father
  (relation (grandad grandchild) (grandad grandchild)
    (show cut (parent)
      (all cut (father grandad parent) (father parent grandchild)))))

(define grandpa
  (extend-relation grandpa/father grandpa/mother))

(define test-grandpa-10
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa x y)))
      '((john pete) (john polly) (sam sal) (sam pat)))))

(printff "~s ~s~%" 'test-grandpa-10 (test-grandpa-10))

(define fail
  (lambda@ (sk fk subst cutk) (fk)))

(define no-grandma
  (relation (grandad grandchild) (grandad grandchild)
    (show cut (parent) (all (mother grandad parent) cut fail))))

(define no-grandma-grandpa
  (extend-relation no-grandma grandpa))

(define test-no-grandma-grandpa-1
  (lambda ()
    (equal?
      (exists (x) (solve 1 (no-grandma-grandpa 'polly x)))
      '())))

(printff "~s ~s~%" 'test-no-grandma-grandpa-1 (test-no-grandma-grandpa-1))

(define grandpa
  (relation (grandad grandchild) (grandad grandchild)
    (show cut (parent)
      (all 
        (father grandad parent)
        (starts-with-p? parent)
        (father parent grandchild)))))

(define starts-with-p?
  (lambda (x)
    (lambda@ (sk fk subst cutk)
      (let ([x (subst-in x subst)])
        (if (lv? x)
          (error 'starts-with-p? "Variable found: ~s." x))
        (if (and
              (symbol? x)
              (string=? (string (string-ref (symbol->string x) 0)) "p"))
          (@ sk fk subst cutk)
          (fk))))))

(define test-grandpa-11
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa x y)))
      '((sam sal) (sam pat)))))

(printff "~s ~s~%" 'test-grandpa-11 (test-grandpa-11))

(define pred             
  (lambda (p)
    (pred-nocheck (check 'pred p))))

(define check
  (lambda (name f)
    (lambda term
      (if (not (procedure? f))
          (error name "Non-procedure found: ~s" f))
      (if (ormap lv? term)
          (error name "Variable found: ~s" term))
      (apply f term))))

(define pred-nocheck
  (lambda (p)
    (lambda term
      (lambda (sk)
        (lambda@ (fk subst cutk)
          (if (apply p (map (lambda (t) (subst-in t subst)) term))
              (@ sk fk subst cutk)
              (fk)))))))

(define starts-with-p?
  (pred
    (lambda (x)
      (and
        (symbol? x)
        (string=? (string (string-ref (symbol->string x) 0)) "p")))))

(define test-grandpa-12
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa x y)))
      '((sam sal) (sam pat)))))

(printff "~s ~s~%" 'test-grandpa-12 (test-grandpa-12))

(define fun    
  (lambda (f)
    (fun-nocheck (check 'fun f))))

(define fun-nocheck
  (lambda (f)
    (lambda (t . term)
      (lambda@ (sk fk subst cutk)
        (cond
          [(unify (apply f (map (lambda (x) (subst-in x subst)) term)) t subst)
           =>
           (lambda (subst)
             (@ sk fk subst cutk))]
          [else (fk)])))))

(define test-fun-*  
  (lambda ()
    (equal?
      (exists (q) (solve 3 ((fun *) q 3 5)))
      '((15 3 5)))))

(printff "~s ~s~%" 'test-fun-* (test-fun-*))

'(define test1
  (lambda (x)
    (any ((pred <) 4 5) ((fun <) x 6 7))))

'(define test-test1
  (lambda ()
    (equal?
      (exists (x) (solution (test1 x)))
      '(x.1))))

'(printff "~s ~s~%" 'test-test1 (test-test1))

'(define test2
  (lambda (x)
    (any ((pred <) 5 4) ((fun <) x 6 7))))

'(define test-test2
  (lambda ()
    (equal?
      (exists (x) (solution (test2 x)))
      '(#t))))

'(printff "~s ~s~%" 'test-test2 (test-test2))

'(define test3
  (lambda (x y)
    (any ((fun <) x 5 4) ((fun <) y 6 7))))

'(define test-test3
  (lambda ()
    (equal?
      (exists (x y) (solution (test3 x y)))
      '(#f y.1))))

'(printff "~s ~s~%" 'test-test3 (test-test3))

(define fails
  (lambda (antecedent)
    (lambda@ (sk fk subst cutk)
      (@ antecedent
        (lambda@ (current-fk subst cutk) (fk))
        (lambda () (@ sk fk subst cutk))
        subst cutk))))

(define grandpa
  (relation (grandad grandchild) (grandad grandchild)
    (show cut (parent)
      (all
        (father grandad parent)
        (fails (starts-with-p? parent))
        (father parent grandchild)))))

(define test-grandpa-13
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa x y)))
      '((john pete) (john polly)))))

(printff "~s ~s~%" 'test-grandpa-13 (test-grandpa-13))

(define instantiated
  (pred-nocheck
    (lambda (t)
      (not (lv? t)))))

(define view-subst
  (lambda (t)
    (lambda@ (sk fk subst cutk)
      (write (subst-in t subst))
      (write (concretize subst))
      (@ sk fk subst cutk))))

(define grandpa
  (relation (grandad grandchild) (grandad grandchild)
    (show cut (parent)
      (all
        (father grandad parent)
        (father parent grandchild)
        (view-subst grandchild)))))

(define test-grandpa-14/view-subst
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa x y)))
      (begin
        'pete
        '((grandad.1 x.1)
          (grandchild.1 y.1)
          (x.1 john)
          (parent.1 sam)
          (y.1 pete))
        'polly
        '((grandad.1 x.1)
          (grandchild.1 y.1)
          (x.1 john)
          (parent.1 sam)
          (y.1 polly))
        'sal 
        '((grandad.1 x.1)
           (grandchild.1 y.1)
           (x.1 sam)
           (parent.1 pete)
           (y.1 sal))
        'pat
        '((grandad.1 x.1)
          (grandchild.1 y.1)
          (x.1 sam)
          (parent.1 pete)
          (y.1 pat))
        '((john pete) (john polly) (sam sal) (sam pat))))))

(printff "~s ~s~%" 'test-grandpa-14/view-subst (test-grandpa-14/view-subst))

(define father
  (extend-relation father
    (extend-relation (fact () 'john 'harry)
      (extend-relation (fact () 'harry 'carl) (fact () 'sam 'ed)))))

(define ancestor
  (extend-relation
    (relation (old young) (old young)
      (show cut () (father old young)))
    (relation (old young) (old young)
      (show cut (not-so-old)
        (all (father old not-so-old) (ancestor not-so-old young))))))

(define test-ancestor
  (lambda ()
    (equal?
      (exists (x) (solve 21 (ancestor 'john x)))
      '((john sam)
        (john harry)
        (john pete)
        (john polly)
        (john ed)
        (john sal)
        (john pat)
        (john carl)))))

(printff "~s ~s~%" 'test-ancestor (test-ancestor))

(define common-ancestor
  (relation (young-a young-b old) (young-a young-b old)
    (show cut ()
      (all
        (ancestor old young-a)
        (ancestor old young-b)))))

(define test-common-ancestor
  (lambda ()
    (equal?
      (exists (x) (solve 4 (common-ancestor 'pat 'ed x)))
      '((pat ed john) (pat ed sam)))))

'(printff "~s ~s~%" 'test-common-ancestor (test-common-ancestor))

(define younger-common-ancestor
  (relation (young-a young-b old not-so-old) (young-a young-b old not-so-old)
    (show cut ()
      (all
        (common-ancestor young-a young-b not-so-old)
        (common-ancestor young-a young-b old)
        (ancestor old not-so-old)))))

(define test-younger-common-ancestor
  (lambda ()
    (equal?
      (exists (x) (solve 4 (younger-common-ancestor 'pat 'ed 'john x)))
      '((pat ed john sam)))))

'(printff "~s ~s~%" 'test-younger-common-ancestor (test-younger-common-ancestor))

(define youngest-common-ancestor
  (relation (young-a young-b not-so-old) (young-a young-b not-so-old)
    (show cut (y)
     (all
       (common-ancestor young-a young-b not-so-old)
       (fails (younger-common-ancestor young-a young-b not-so-old y))))))

(define test-youngest-common-ancestor
  (lambda ()
    (equal?
      (exists (x) (solve 4 (youngest-common-ancestor 'pat 'ed x)))
      '((pat ed sam)))))

'(printff "~s ~s~%" 'test-youngest-common-ancestor (test-youngest-common-ancestor))

(define == (fun (lambda (x) x)))

(define ==
  (lambda (t1 t2)
    (lambda@ (sk fk subst cutk)
      (cond
        [(unify t1 t2 subst)
         =>
         (lambda (subst)
           (@ sk fk subst cutk))]
        [else (fk)]))))
  
'(define test-Seres-Spivey
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

'(printff "~s ~s~%" 'test-Seres-Spiver (test-Seres-Spivey))

(define towers-of-hanoi
  (letrec
      ([move
         (extend-relation
           (relation () (0 _ _ _)
             (show cut () cut))
           (relation (n a b c) (n a b c)
             (show cut (m)
               (all
                 ((fun -) m n 1)
                 (move m a c b)
                 ((pred (lambda (x y)
                          (printff "Move a disk from ~s to ~s~n" x y)))
                  a b)
                 (move m c b a)))))])
    (relation (n) (n)
      (show cut () (move n 'left 'middle 'right)))))

(begin
  (printff "~s with 3 disks~n~n" 'test-towers-of-hanoi)
  (solution (towers-of-hanoi 3))
  (void))

(define nonempty-subst-in
  (lambda (t subst)
    (cond
      [(lv? t)
       (cond
         [(assv t subst) => commitment->term]
         [else t])]
      [(pair? t)
       (cons
         (nonempty-subst-in (car t) subst)
         (nonempty-subst-in (cdr t) subst))]
      [else t])))

(define test-compose-subst-5
  (lambda ()
    (equal?
      (concretize
        (exists (x y z)
          (let ([term `(p ,x ,y (g ,z))])
            (let ([s (compose-subst (unit-subst y z) (unit-subst x `(f ,y)))]
                  [r (compose-subst (unit-subst x 'a) (unit-subst z 'b))])
              (let ([term1 (subst-in term s)])
                ;(write (concretize term1))
                (let ([term2 (subst-in term1 r)])
                  ;(write (concretize term2))
                  (let ([sr (compose-subst s r)])
                    ;(write (concretize sr))
                    (subst-in term sr))))))))
      (begin
        '(p (f y.1) z.1 (g z.1))
        '(p (f y.1) b (g b))
        '((y.1 b) (x.1 (f y.1)) (z.1 b))
        '(p (f y.1) b (g b))))))

(printff "~s ~s~%" 'test-compose-subst-5 (test-compose-subst-5))

(define unify*
  (lambda (t u)
    (cond
      [(or (eqv? t u) (eqv? t _) (eqv? u _)) empty-subst]
      [(lv? t) (if (occurs? t u) #f (unit-subst t u))]
      [(lv? u) (if (occurs? u t) #f (unit-subst u t))]
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
      [(equal? t u) empty-subst]
      [else #f])))

(define occurs?
  (lambda (lv term)
    (cond
      [(lv? term) (eqv? term lv)]
      [(pair? term) (or (occurs? lv (car term)) (occurs? lv (cdr term)))]
      [else #f])))

(define test-unify/pairs
  (lambda ()
    (and
      (and
        (equal?
          (exists (x) (unify `(,x ,4) `(3 ,x) empty-subst))
          #f)
        (equal?
          (exists (x) (unify `(,x ,x) '(3 4) empty-subst))
          #f))
      (and
        (equal?
          (concretize
            (exists (x y) 
              (unify `(,x ,y) '(3 4) empty-subst)))
          `(,(commitment 'x.1 3) ,(commitment 'y.1 4)))
        (equal?
          (concretize
            (exists (x y) 
              (unify `(,x 4) `(3 ,y) empty-subst)))
          `(,(commitment 'x.1 3) ,(commitment 'y.1 4))))
      (and
        (equal?
          (concretize
            (exists (w x y z)     
              (unify `(,x 4 3 ,w) `(3 ,y ,x ,z) empty-subst)))
          `(,(commitment 'x.1 3)
	    ,(commitment 'y.1 4)
	    ,(commitment 'w.1 'z.1)))
        (equal?
          (concretize
            (exists (x y)
              (unify `(,x 4) `(,y ,y) empty-subst)))
          `(,(commitment 'x.1 4)
	    ,(commitment 'y.1 4)))
        (equal?
          (exists (x y) 
            (unify `(,x 4 3) `(,y ,y ,x) empty-subst))
          #f)
        (equal?
          (concretize
            (exists (r v w x u)
              (unify `(,r (,v (,w ,x) 8))
		`(,r (,u (abc ,u) ,x))
		empty-subst)))
          `(,(commitment 'v.1 8)
	    ,(commitment 'w.1 'abc)
	    ,(commitment 'x.1 8)
	    ,(commitment 'u.1 8)))
        (equal?
          (concretize
            (exists (x y)
              (unify `(p (f a) (g ,x)) `(p ,x ,y) empty-subst)))
          `(,(commitment 'x.1 '(f a))
	    ,(commitment 'y.1 '(g (f a)))))
        (equal?
          (concretize
            (exists (x y)
              (unify `(p (g ,x) (f a)) `(p ,y ,x) empty-subst)))
          `(,(commitment 'y.1 '(g (f a))) ,(commitment 'x.1 '(f a))))
        (equal?
          (concretize
            (exists (x y z)
              (unify `(p a ,x (h (g ,z))) `(p ,z (h ,y) (h ,y)) empty-subst)))
          `(,(commitment 'z.1 'a)
	    ,(commitment 'x.1 '(h (g a)))
	    ,(commitment 'y.1 '(g a))))
        (equal? ;;; Oleg's works on this.
          (concretize
            (exists (x y)
              (unify `(p ,x ,x) `(p ,y (f ,y)) empty-subst)))
          #f)))))

(printff "~s ~s~%" 'test-unify/pairs-eager (test-unify/pairs))

(define test-fun-resubstitute
  (lambda ()
    (equal?
      (concretize
        (let ([j (relation (x w z) (z)
                   (show cut ()
                     (all
                        ((fun (lambda () 4)) x)
                        ((fun (lambda () 3)) w)
                        ((fun (lambda (y) (cons x y))) z w))))])
          (exists (q) (solve 4 (j q)))))
      '(((4 . 3))))))

(printff "~s ~s~%" 'test-fun-resubstitute-eager (test-fun-resubstitute))

(define unify
  (lambda (t u subst)
    (cond
      [(or (eqv? t u) (eqv? t _) (eqv? u _)) subst]
      [(lv? t) (unify-with-lv t (subst-in u subst) subst)]
      [(lv? u) (unify-with-lv u (subst-in t subst) subst)]
      [(and (pair? t) (pair? u))
       (cond
	 [(unify (car t) (car u) subst)
	  => (lambda (subst)
               (unify (cdr t) (cdr u) subst))]
	 [else #f])]
      [(equal? t u) subst]
      [else #f])))

(define unify-with-lv
  (lambda (t-var u subst)
    (cond
      [(assv t-var subst) (unify (subst-in t-var subst) u subst)]
      [(occurs? t-var u) #f]
      [else (compose-with-virtual-unit-subst subst t-var u)])))

(define compose-with-virtual-unit-subst
  (lambda (base t-var u)
    (cons (commitment t-var u)
      (map
        (lambda (c)
          (commitment
	    (commitment-var c)
	    (subst-in-with-virtual-unit-subst
	      (commitment-term c) t-var u)))
        base))))

(define subst-in-with-virtual-unit-subst
  (lambda (t t-var u)
    (cond
      [(lv? t) (if (eqv? t t-var) u t)]
      [(pair? t)
       (cons
         (subst-in-with-virtual-unit-subst (car t) t-var u)
         (subst-in-with-virtual-unit-subst (cdr t) t-var u))]
      [else t])))

;;; ;-------------------------------------------------------
;;; This is the unifier of Oleg Kiselov

(define normalize-subst
  (lambda (subst)
    (map (lambda (c)
           (commitment (commitment->var c)
             (substitute-vars-recursively
	       (commitment->term c) subst)))
      subst)))

(define substitute-vars-recursively
  (lambda (term subst)
    (traverse-term
      (lambda (var)
	(cond
	  [(assv var subst) =>
	   (lambda (c)
	     (substitute-vars-recursively
	       (commitment->term c) (remq c subst)))]
	  [else var]))
      term)))

(define traverse-term
  (lambda (f t)
    (cond
      [(lv? t) (f t)]
      [(pair? t) (cons (traverse-term f (car t)) (traverse-term f (cdr t)))]
      [else t])))

(define nonempty-subst-in
  (lambda (t subst)
    (cond
      [(lv? t)
       (cond
         [(assv t subst)
	  => (lambda (c)
	       (nonempty-subst-in (commitment->term c) subst))]
         [else t])]
      [(pair? t)
       (cons
         (nonempty-subst-in (car t) subst)
         (nonempty-subst-in (cdr t) subst))]
      [else t])))

;;;; This is new stuff

(define extend-subst
  (lambda (a t s)
    (cond
      [(assq a s)
       => (lambda (c)
            (if (lv? t)
                (cond
                  [(assq t s)
                   => (lambda (ct)
                        (unify (commitment->term c) (commitment->term ct) s))]
                  [else (cons-if-real-commitment t (commitment->term c) s)])
                (unify (commitment->term c) t s)))]
      [else (cons-if-real-commitment a t s)])))

(define count-unify 0)

(define unify
  (lambda (t u subst)
    (set! count-unify (add1 count-unify))
    (unify^^ t u subst)))

(define unify^^
  (lambda (t u subst)
    (cond
      [(or (eqv? t u) (eqv? t _) (eqv? u _)) subst]
      [(lv? t)
       (cond
         [(assv t subst)
          => (lambda (c)        ; t is bound
               (unify^^ (commitment->term c) u subst))]
         [(lv? u) (unify-with-unbound-lv-and-other-is-lv t u subst)]
         [else (unify-with-unbound-lv-and-other-is-value t u subst)])]
      [(lv? u)
       (cond
         [(assv u subst)
          => (lambda (c)        ; u is bound
               (unify^^ (commitment->term c) t subst))]
         [else (unify-with-unbound-lv-and-other-is-value u t subst)])]
      [(and (pair? t) (pair? u))
       (cond
         [(unify^^ (car t) (car u) subst)
          => (lambda (car-subst)
               (unify^^ (cdr t) (cdr u) car-subst))]
         [else #f])]
      [(equal? t u) subst]
      [else #f])))

(define unify-with-unbound-lv-and-other-is-lv
  (lambda (unbound-t-var u-var subst)
    (cond
      [(assv u-var subst)                  
       => (lambda (c)                       ; u-var is bound
            (let ([u-term (commitment->term c)])
              (cons-if-real-commitment unbound-t-var u-term subst)))]
      [else (compose-subst (unit-subst unbound-t-var u-var) subst)])))

;;; Don't add the commitment of an uncommited variable x to a pair (a . b)
; instead, add the commitment x = (var1 . var2) and
; unify var1 with a and var2 with b.

(define unify-with-unbound-lv-and-other-is-value
  (lambda (unbound-t-var u-value subst)
    (cond
      [(pair? u-value)
       (let ([car-var (lv ':a)]
             [cdr-var (lv ':d)])
         (let ([new-pair (cons car-var cdr-var)])
           (cond
             [(unify^^ car-var (car u-value)
                (compose-subst (unit-subst unbound-t-var new-pair) subst))
              => (lambda (subst)
                   (unify^^ cdr-var (cdr u-value) subst))]
             [else #f])))]
      [else (compose-subst (unit-subst unbound-t-var u-value) subst)])))
;------------------------------------------------------------------------

(define ==
  (lambda (t1 t2)
    (lambda@ (sk fk subst cutk)
      (cond
        [(unify t1 t2 subst)
         =>
         (lambda (subst)
           (@ sk fk subst cutk))]
        [else (fk)]))))

(define test-unify/pairs
  (lambda ()
    (and
      (and
        (equal?
          (exists (x) (unify `(,x ,4) `(3 ,x) empty-subst))
          #f)
        (equal?
          (exists (x) (unify `(,x ,x) '(3 4) empty-subst))
          #f))
      (and
        (equal?
          (concretize
            (exists (x y) 
              (unify `(,x ,y) '(3 4) empty-subst)))
          `(,(commitment 'y.1 4) ,(commitment 'x.1 3)))
        (equal?
          (concretize
            (exists (x y) 
              (unify `(,x 4) `(3 ,y) empty-subst)))
          `(,(commitment 'y.1 4) ,(commitment 'x.1 3))))
      (and
        (equal?
          (concretize
            (exists (w x y z)
	      (let ([s (normalize-subst
                         (unify `(,x 4 3 ,w) `(3 ,y ,x ,z) empty-subst))])
		(let ([vars (list w y x)])
		  (map commitment
		    vars
		    (substitute-vars-recursively vars s))))))
          `(,(commitment 'w.1 'z.1)
	    ,(commitment 'y.1 4)
	    ,(commitment 'x.1 3)))
        (equal? 
          (concretize
            (exists (x y)
              (let ([s (normalize-subst
			 (unify `(,x 4) `(,y ,y) empty-subst))])
		(let ([vars (list y x)])
		  (map commitment
		    vars
		    (substitute-vars-recursively vars s))))))
          `(,(commitment 'y.1 4) ,(commitment 'x.1 4)))
        (equal?
          (exists (x y) 
            (unify `(,x 4 3) `(,y ,y ,x) empty-subst))
          #f)
        (equal? 
          (concretize
            (exists (r v w x u)
              (let ([s (normalize-subst
                         (unify
			   `(,r (,v (,w ,x) 8))
			   `(,r (,u (abc ,u) ,x))
			   empty-subst))])
                (let ([vars (list u x w v)])
                  (map commitment
		    vars
		    (substitute-vars-recursively vars s))))))
          `(,(commitment 'u.1 8)
	    ,(commitment 'x.1 8)
	    ,(commitment 'w.1 'abc)
	    ,(commitment 'v.1 8)))
        (equal? 
          (concretize
            (exists (x y)
              (let ([s (normalize-subst
                         (unify `(p (f a) (g ,x)) `(p ,x ,y) empty-subst))])
                (let ([vars (list y x)])
                  (map commitment
		    vars
		    (substitute-vars-recursively vars s))))))
          `(,(commitment 'y.1 '(g (f a)))
	    ,(commitment 'x.1 '(f a))))
        (equal? 
          (concretize
            (exists (x y)
              (let ([s (normalize-subst
                         (unify `(p (g ,x) (f a)) `(p ,y ,x) empty-subst))])
                (let ([vars (list x y)])
                  (map commitment
		    vars
		    (substitute-vars-recursively vars s))))))
          `(,(commitment 'x.1 '(f a))
	    ,(commitment 'y.1 '(g (f a)))))
        (equal? 
          (concretize
            (exists (x y z)
              (let ([s (normalize-subst
                         (unify
			   `(p a ,x (h (g ,z)))
			   `(p ,z (h ,y) (h ,y))
			   empty-subst))])
                (let ([vars (list y x z)])
                  (map commitment
		    vars
		    (substitute-vars-recursively vars s))))))
          `(,(commitment 'y.1 '(g a))
	    ,(commitment 'x.1 '(h (g a)))
	    ,(commitment 'z.1 'a)))
        (equal? 
          (concretize ;;; was #f
            (exists (x y)
              (let ([s (unify `(p ,x ,x) `(p ,y (f ,y)) empty-subst)])
                (let ([var (map commitment->var s)])
                  (map commitment
		    var
		    (substitute-vars-recursively var s))))))
          `(,(commitment ':d.1 '())
            ,(commitment ':a.1 '(f :a.1))
            ,(commitment ':d.2 '((f . :d.2)))
            ,(commitment ':a.2 'f)
            ,(commitment 'y.1 '(f (f . :d.2)))
            ,(commitment 'x.1 `(f (f . :d.2)))))))))
          
(printff "~s ~s~%" 'test-unify/pairs-lazy (test-unify/pairs))
(printff "~s ~s~%" 'test-fun-resubstitute-lazy (test-fun-resubstitute))

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

(printff "~s ~s~%" 'test-concat-as-function (test-concat-as-function))

(define test-fun-concat
  (lambda ()
    (equal?
      (exists (q) (solve 1 ((fun concat) q '(a b c) '(u v))))
      '(((a b c u v) (a b c) (u v))))))

(define concat
  (extend-relation
    (fact (xs) '() xs xs)
    (relation (x xs ys zs) (`(,x . ,xs) ys `(,x . ,zs))
      (show cut () (concat xs ys zs)))))

(define count-unify 0)
(define calls-to-unify2 0)
(define calls-to-compose-subst2 0)

(define test-concat
  (lambda ()
    (and
      (equal?
        (exists (q) (solve 6 (concat '(a b c) '(u v) q)))
        '(((a b c) (u v) (a b c u v))))
      (pretty-print count-unify)
      (set! count-unify 0)
      (equal?
        (exists (q) (solve 6 (concat '(a b c) q '(a b c u v))))
        '(((a b c) (u v) (a b c u v))))
      (pretty-print count-unify)
      (set! count-unify 0)
      (equal? 
        (exists (q) (solve 6 (concat q '(u v) '(a b c u v))))     
        '(((a b c) (u v) (a b c u v))))
      (pretty-print count-unify)
      (set! count-unify 0)      
      (equal? 
        (exists (q r) (solve 6 (concat q r '(a b c u v))))
        '((() (a b c u v) (a b c u v))
          ((a) (b c u v) (a b c u v))
          ((a b) (c u v) (a b c u v))
          ((a b c) (u v) (a b c u v))
          ((a b c u) (v) (a b c u v))
          ((a b c u v) () (a b c u v))))
      (pretty-print count-unify)
      (set! count-unify 0)      
      (equal?
        (exists (q r s) (solve 6 (concat q r s)))
        '((() xs.1 xs.1)
          ((x.1) xs.2 (x.1 . xs.2))
          ((x.1 x.2) xs.3 (x.1 x.2 . xs.3))
          ((x.1 x.2 x.3) xs.4 (x.1 x.2 x.3 . xs.4))
          ((x.1 x.2 x.3 x.4) xs.5 (x.1 x.2 x.3 x.4 . xs.5))
          ((x.1 x.2 x.3 x.4 x.5) xs.6 (x.1 x.2 x.3 x.4 x.5 . xs.6))))
      (pretty-print count-unify)
      (set! count-unify 0)      
      (equal?
        (exists (q r) (solve 6 (concat q '(u v) `(a b c . ,r))))
        '(((a b c) (u v) (a b c u v))
          ((a b c x.1) (u v) (a b c x.1 u v))
          ((a b c x.1 x.2) (u v) (a b c x.1 x.2 u v))
          ((a b c x.1 x.2 x.3) (u v) (a b c x.1 x.2 x.3 u v))
          ((a b c x.1 x.2 x.3 x.4) (u v) (a b c x.1 x.2 x.3 x.4 u v))
          ((a b c x.1 x.2 x.3 x.4 x.5)
           (u v)
           (a b c x.1 x.2 x.3 x.4 x.5 u v))))
      (pretty-print count-unify)
      (set! count-unify 0)      
      (equal?
        (exists (q) (solve 6 (concat q '() q)))
        '((() () ())
          ((x.1) () (x.1))
          ((x.1 x.2) () (x.1 x.2))
          ((x.1 x.2 x.3) () (x.1 x.2 x.3))
          ((x.1 x.2 x.3 x.4) () (x.1 x.2 x.3 x.4))
          ((x.1 x.2 x.3 x.4 x.5) () (x.1 x.2 x.3 x.4 x.5))))
      (pretty-print count-unify)
      (set! count-unify 0)
      #t)))

(time (printff "~s ~s~%" 'test-concat (test-concat)))

(pretty-print calls-to-unify2)
(pretty-print calls-to-compose-subst2)

;;;; Types from here on out.

(define int-rel
  (relation (g x) (g x "int")
    (show cut () (all ((pred integer?) x) cut))))

(define bool-rel
  (relation (g x) (g x "bool")
    (show cut () (all ((pred boolean?) x) cut))))

(define !- (extend-relation int-rel bool-rel))

(define test-!-1
  (lambda ()
    (and
      (equal?
        (exists (g) (solution (!- g 17 "int")))
        '(g.1 17 "int"))
      (equal?
        (exists (g ?) (solution (!- g 17 ?)))
        '(g.1 17 "int")))))

(printff "~s ~s~%" 'ints-and-bools (test-!-1))

(define zero?-rel
  (relation (g x) (g `(zero? ,x) "bool")
    (show cut () (all cut (!- g x "int")))))
  
(define sub1-rel
  (relation (g x) (g `(sub1 ,x) "int")
    (show cut () (all cut (!- g x "int")))))

(define +-rel
  (relation (g x y) (g `(+ ,x ,y) "int")
    (show cut () (all cut (!- g x "int") cut (!- g y "int")))))

(define !- (extend-relation !-
             (extend-relation zero?-rel
               (extend-relation sub1-rel +-rel))))

(define test-!-2
  (lambda ()
    (and
      (equal?
        (exists (g ?) (solution (!- g '(zero? 24) ?)))
        '(g.1 (zero? 24) "bool"))
      (equal?
        (exists (g ?) (solution (!- g '(zero? (+ 24 50)) ?)))
        '(g.1 (zero? (+ 24 50)) "bool"))
      (equal?
        (exists (g ?)
          (solution
            (!- g '(zero? (sub1 (+ 18 (+ 24 50)))) ?)))
        '(g.1 (zero? (sub1 (+ 18 (+ 24 50)))) "bool")))))

(printff "~s ~s~%" 'arithmetic-primitives (test-!-2))

(define if-rel
  (relation (g t test conseq alt) (g `(if ,test ,conseq ,alt) t)
    (show cut () (all cut (!- g test "bool") cut (!- g conseq t) cut (!- g alt t)))))

(define !- (extend-relation !- if-rel))

(define test-!-3
  (lambda ()
    (equal?
      (exists (g ?) (solution (!- g '(if (zero? 24) 3 4) ?)))
      '(g.1 (if (zero? 24) 3 4) "int"))))

(printff "~s ~s~%" 'if-expressions (test-!-3))

(define test-!-3a
  (lambda ()
    (equal?
      (exists (g ?) (solution (!- g '(if (zero? 24) (zero? 3) (zero? 4)) ?)))
      '(g.1 (if (zero? 24) (zero? 3) (zero? 4)) "bool"))))

(printff "~s ~s~%" 'if-expressions (test-!-3a))

(define lexvar-rel
  (relation (g v t) (g v t)
    (show cut () (all cut ((pred symbol?) v) cut (env g v t)))))

(define base-env
  (relation (g v t) (`(non-generic ,v ,t ,g) v t)
    (show cut () cut)))

;!!! cut after all??
(define middle-env
  (relation (g v t type-w) (`(non-generic ,v ,t ,g) v type-w)
    (show cut () (all cut (unequal? t type-w) cut fail))))

(define recursive-env
  (relation (g v t w type-w) (`(non-generic ,w ,type-w ,g) v t)
    (show cut () (all cut (unequal? w v) cut (env g v t)))))
              
(define env
  (extend-relation base-env (extend-relation middle-env recursive-env)))

(define unequal?
  (extend-relation
    (relation (a) (a a)
      (show cut () (all cut fail)))
    (relation (a b) (a b)
      (show cut () (fails fail)))))

(define !- (extend-relation !- lexvar-rel))

(define test-!-3
  (lambda ()
    (and
      (equal?
        (exists (g ?)
          (solution
            (env `(non-generic b "int" (non-generic a "bool" ,g)) 'a ?)))
        '((non-generic b "int" (non-generic a "bool" g.1)) a "bool"))
      (equal?
        (exists (g ?)
          (solution 
            (!- `(non-generic a "int" ,g) '(zero? a) ?)))
        '((non-generic a "int" g.1) (zero? a) "bool"))
      (equal?
        (exists (g ?)
          (solution
            (!- `(non-generic b "bool" (non-generic a "int" ,g))
              '(zero? a)
              ?)))
        '((non-generic b "bool" (non-generic a "int" g.1)) (zero? a) "bool")))))

(printff "~s ~s~%" 'variables (test-!-3))
(printff "~%Accidental binding ~s~%"
  (exists (g ?)
    (solution
      (!- g
	'a
	?))))



(define lambda-rel
  (relation (g v t body type-v) (g `(lambda () ,body) `("->" "()" ,t))
    (show cut () cut)))

(define lambda1-rel
  (relation (g x) (g `(zero ,x) "bool")
    (show cut () (all cut (!- g x "int")))))

; (define zero?-rel
;   (relation (g x) (g `(zero? ,x) "t")
;     (show cut () (all cut (!- g x "int")))))

(define !- ;(extend-relation lambda-rel 
	     (extend-relation lexvar-rel (extend-relation int-rel bool-rel)))
;(define !- (extend-relation !- lambda1-rel))


(define test-!-4a1
  (lambda ()
      (exists (g ?)
        (solution 
          (!- `(non-generic b "bool" (non-generic a "int" ,g))
            '(lambda () a)
            ?)))))
(printff "~s ~s~%" 'variables-4a1 (test-!-4a1))

(define lambda-rel
  (relation (g v t body type-v) (g `(lambda (,v) ,body) `("->" ,type-v ,t))
    (show cut () (all cut (!- `(non-generic ,v ,type-v ,g) body t)))))

(define (extend-relations rel . rels)
  (let loop ((rel rel) (rels rels))
    (if (null? rels) rel
      (extend-relation rel (loop (car rels) (cdr rels))))))

(define !- (extend-relations  lambda-rel lexvar-rel
	      int-rel bool-rel 
	     zero?-rel
	     sub1-rel +-rel if-rel  ))

(define !-
  (letrec
    ((rel
       (extend-relations  lambda1-rel 
	 zero?-rel
	 sub1-rel +-rel if-rel int-rel bool-rel lexvar-rel))
      (lambda1-rel
	(relation (g v t body type-v)
	  (g `(lambda (,v) ,body) `("->" ,type-v ,t))
	  (show cut () (all cut (rel `(non-generic ,v ,type-v ,g) body t))))))
    rel))

(define test-!-4a
  (lambda ()
    (equal?
      (exists (g ?)
        (solution 
          (!- `(non-generic b "bool" (non-generic a "int" ,g))
            '(lambda (x) (+ x 5))
            ?)))
      '((non-generic b "bool" (non-generic a "int" g.1))
        (lambda (x) (+ x 5))
        ("->" "int" "int")))))

(define test-!-4a
  (lambda ()
    (equal?
      (exists (g ?)
        (solution 
          (!- g
            '(lambda (x) (+ x 5))
            ?)))
      '(g.1
        (lambda (x) (+ x 5))
        ("->" "int" "int")))))

(define test-!-4a1
  (lambda ()
      (exists (g ?)
        (solution 
          (!- g
            '(lambda (x) (+ x 5))
            ?)))))

(define test-!-4a2
  (lambda ()
      (exists (g ?)
        (solution 
          (!- `(non-generic b "bool" (non-generic a "int" ,g))
            '(lambda (x) b)
            ?)))))

(define test-!-4a3
  (lambda ()
      (exists (g ?)
        (solution 
          (!- `(non-generic b "bool" (non-generic a "int" ,g))
            '(lambda (x) (zero? x))
            ?)))))

(define test-!-4a4
  (lambda ()
      (exists (g ?)
        (solution 
          (!- `(non-generic b "bool" (non-generic a "int" ,g))
            '(lambda (x) (lambda (y) y))
            ?)))))

(define test-!-4a5
  (lambda ()
      (exists (g ?)
        (solution 
          (!- `(non-generic b "bool" (non-generic a "int" ,g))
            '(lambda (x) (lambda (y) x))
            ?)))))

(printff "~s ~s~%" 'variables-4a (test-!-4a))
(printff "~s ~s~%" 'variables-4a1 (test-!-4a1))
(printff "~s ~s~%" 'variables-4a2 (test-!-4a2))
(printff "~s ~s~%" 'variables-4a3 (test-!-4a3))
(printff "~s ~s~%" 'variables-4a4 (test-!-4a4))
(printff "~s ~s~%" 'variables-4a5 (test-!-4a5))


(define !-
  (let ([app-rel
          (relation (g rator rand t)
            (g `(,rator ,rand) t)
            (show cut (t-rand) (all cut  (!- g rator `("->" ,t-rand ,t)) cut (!- g rand t-rand))))]
        [lambda-rel
          (relation (g v t body type-v)
            (g `(lambda (,v) ,body) `("->" ,type-v ,t))
            (show cut () (all cut (!- `(non-generic ,v ,type-v ,g) body t))))]
        [fix-rel
          (relation (g rand t)
            (g `(fix ,rand) t)
            (show cut () (all cut (!- g rand `("->" ,t ,t)) cut)))]
        [polylet-rel
          (relation (g v rand body t)
            (g `(let ([,v ,rand]) ,body) t)
            (show cut (t-rand) (all cut (!- g rand t-rand) cut (!- `(generic ,v ,t-rand ,g) body t))))])
    (extend-relations
      fix-rel lambda-rel zero?-rel sub1-rel +-rel if-rel app-rel int-rel bool-rel lexvar-rel)))

(printff "Testing~%")
(pretty-print
  (list
    (exists (g ?)
          (solution
            (!- '() '(lambda (f)
                     (lambda (x)
                       ((f x) x))) ?)))
    (exists (g ?)
          (solution
            (!- '()
              '(fix (lambda (sum) sum))
              ?)))

    (exists (g ?)
          (solution
            (!- '()
              '((fix (lambda (sum)
                       (lambda (n)
                         (if (zero? n)
                             0
                             (+ n (sum (sub1 n)))))))
                10)
              ?)))
))


(define test-!-5
  (lambda ()
    (list
      (equal?
        (exists (g ?)
          (solution
            (!- '() '(lambda (f)
                     (lambda (x)
                       ((f x) x))) ?)))
        '(() 
           (lambda (f) 
             (lambda (x)
               ((f x) x)))
           ("->" ("->" t-rand.1 ("->" t-rand.1 t.1))
            ("->" t-rand.1 t.1))))
      (equal?
        (exists (g ?)
          (solution
            (!- '()
              '((fix (lambda (sum)
                       (lambda (n)
                         (if (zero? n)
                             0
                             (+ n (sum (sub1 n)))))))
                10)
              ?)))
        '(()
           ((fix (lambda (sum)
                   (lambda (n)
                     (if (zero? n)
                         0 
                         (+ n (sum (sub1 n)))))))
            10)
           "int"))
      (equal?
        (exists (g ?)
          (solution 
            (!- '()
              '((fix (lambda (sum)
                       (lambda (n)
                         (+ n (sum (sub1 n))))))
                10)
              ?)))
        '(()
           ((fix (lambda (sum)
                   (lambda (n) 
                     (+ n (sum (sub1 n))))))
            10)
           "int"))
      (equal?
        (exists (g ?)
          (solution
            (!- '()
              '((lambda (f)
                  (if (f (zero? 5))
                      (+ (f 4) 8)
                      (+ (f 3) 7)))
                (lambda (x) x))
              ?)))
        #f))))

(printff "~s ~s~%" 'everything-but-polymorphic-let (test-!-5))

#!eof

(define test-!-4b
  (lambda ()
    (equal?
      (exists (g ?)
        (solution 
          (!- `(non-generic b "bool" (non-generic a "int" ,g))
            '(lambda (x) (+ x a))
            ?)))
      '((non-generic b "bool" (non-generic a "int" g.1))
        (lambda (x) (+ x a))
        ("->" "int" "int")))))

(printff "~s ~s~%" 'variables-4b (test-!-4b))

(define test-!-4c
  (lambda ()
    (equal?
      (exists (g ?)
        (solution
          (!- g '(lambda (a) (lambda (x) (+ x a))) ?)))
      '(g.1 
         (lambda (a) (lambda (x) (+ x a)))
         ("->" "int" ("->" "int" "int"))))))

(printff "~s ~s~%" 'variables-4c (test-!-4c))

(define app-rel
  (relation (g exp t)
    (reify-!
      (lambda (!)
        (exists (g t rand rator)
          ((to-show g `(,rator ,rand) t)
           (exists (t-rand)
             (all !
               (!- g rator `("->" ,t-rand ,t)) !
               (!- g rand t-rand) !))))))))

(define fix-rel
  (relation (g exp t)
    (reify-!
      (lambda (!)
        (exists (g t rand)
          ((to-show g `(fix ,rand) t)
           (all ! (!- g rand `("->" ,t ,t)) !)))))))

(define polylet-rel
  (relation (g exp t)
    (reify-!
      (lambda (!)
        (exists (g t rand v body)
          ((to-show g `(let ([,v ,rand]) ,body) t)
           (exists (t-rand)
             (all !
               (!- g rand t-rand) !
               (!- `(generic ,v ,t-rand ,g) body t) !))))))))

(define !- (let ([!- !-]) (extend-relation (g exp t) !- fix-rel polylet-rel app-rel)))

(define test-!-5
  (lambda ()
    (and
      (equal?
        (exists (g ?)
          (solution
            (!- g '(lambda (f)
                     (lambda (x)
                       ((f x) x))) ?)))
        '(g.1 
           (lambda (f) 
             (lambda (x)
               ((f x) x)))
           ("->" ("->" t-rand.1 ("->" t-rand.1 t.1))
            ("->" t-rand.1 t.1))))
      (equal?
        (exists (g ?)
          (solution
            (!- g
              '((fix (lambda (sum)
                       (lambda (n)
                         (if (zero? n)
                             0
                             (+ n (sum (sub1 n)))))))
                10)
              ?)))
        '(g.1
           ((fix (lambda (sum)
                   (lambda (n)
                     (if (zero? n)
                         0 
                         (+ n (sum (sub1 n)))))))
            10)
           "int"))
      (equal?
        (exists (g ?)
          (solution 
            (!- g
              '((fix (lambda (sum)
                       (lambda (n)
                         (+ n (sum (sub1 n))))))
                10)
              ?)))
        '(g.1
           ((fix (lambda (sum)
                   (lambda (n) 
                     (+ n (sum (sub1 n))))))
            10)
           "int"))
      (equal?
        (exists (g ?)
          (solution
            (!- g
              '((lambda (f)
                  (if (f (zero? 5))
                      (+ (f 4) 8)
                      (+ (f 3) 7)))
                (lambda (x) x))
              ?)))
        #f))))

(printff "~s ~s~%" 'everything-but-polymorphic-let (test-!-5))

(define fix
  (lambda (e)
    (e (lambda (z) ((fix e) z)))))

(define generic-env
  (relation (g v t)
    (reify-!
      (lambda (!)
        (select
          (exists (g targ tresult)
            ((to-show `(generic ,v ("->" ,targ ,tresult) ,g) v t)
             (all ((fun-nocheck instantiate) t `("->" ,targ ,tresult)) !)))
          (exists (w type-w)
            ((to-show `(generic ,w ,type-w ,g) v t)
             (all ! (env g v t) !))))))))

(define instantiate
  (copy-term
    (lambda (t env k)
      (cond
        [(assv t env)
         => (lambda (pr)
              (k (cdr pr) env))]
        [else (let ([new-lv (lv (lv-name t))])
                (k new-lv (cons `(,t . ,new-lv) env)))]))))

(define env (let ([env env]) (extend-relation (g v t) env generic-env)))

(define test-!-6
  (lambda ()
    (equal?
      (exists (g ?)
        (solution
          (!- g
            '(let ([f (lambda (x) x)])
               (if (f (zero? 5))
                   (+ (f 4) 8)
                   (+ (f 3) 7)))
            ?)))
      '(g.1 
         (let ([f (lambda (x) x)])
           (if (f (zero? 5))
               (+ (f 4) 8)
               (+ (f 3) 7)))
         "int"))))

(printff "~s ~s~%" 'polymorphic-let (test-!-6))

(define lexvar-rel
  (relation (g exp t)
    (reify-!
      (lambda (!)
        (exists (v)
          ((to-show g `(var ,v) t)
           (all ! (env g v t) !)))))))

(define int-rel
  (relation (g exp t)
    (reify-!
      (lambda (!)
        (exists (g x)
          ((to-show g `(intc ,x) "int") !))))))

(define bool-rel
  (relation (g exp t)
    (reify-!
      (lambda (!)
        (exists (g x)
          ((to-show g `(boolc ,x) "bool") !))))))

(define app-rel
  (relation (g exp t)
    (reify-!
      (lambda (!)
        (exists (g t rand rator)
          ((to-show g `(app ,rator ,rand) t)
           (exists (t-rand)
             (all !
               (!- g rator `("->" ,t-rand ,t)) !
               (!- g rand t-rand) !))))))))

(define !-
  (extend-relation (g exp t)
    lexvar-rel int-rel bool-rel zero?-rel sub1-rel +-rel 
    if-rel lambda-rel app-rel fix-rel polylet-rel))

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
      '(g.1 (app
              (fix (lambda (sum)
                     (lambda (n)
                       (if (if (zero? (var n)) (boolc #t) (boolc #f))
                           (intc 0)
                           (+ (var n) (app (var sum) (sub1 (var n))))))))
              (intc 10))
         "int"))))

(printff "~s ~s~%" 'with-robust-syntax (test-!-7)) 

(define !-
  (relation (g exp t)
    (exists (g t x y z tx)
      (reify-!
        (lambda (!)
          (select
            ((to-show g `(var ,x) t)
             (all ! (env g x t) !))
            ((to-show g `(intc ,x) "int") !)
            ((to-show g `(boolc ,x) "bool") !)
            ((to-show g `(zero? ,x) "bool")
             (all ! (!- g x "int") !))
            ((to-show g `(sub1 ,x) "int")
             (all ! (!- g x "int") !))
            ((to-show g `(+ ,x ,y) "int")
             (all ! (!- g x "int") ! (!- g y "int") !))
            ((to-show g `(if ,x ,y ,z) t)
             (all ! (!- g x "bool") ! (!- g y t) ! (!- g z t) !))
            ((to-show g `(lambda (,x) ,y) `("->" ,tx ,t))
             (all ! (!- `(non-generic ,x ,tx ,g) y t) !))
            ((to-show g `(app ,x ,y) t)
             (all ! (!- g x `("->" ,tx ,t)) ! (!- g y tx) !))
            ((to-show g `(fix ,x) t)
             (all ! (!- g x `("->" ,t ,t)) !))
            ((to-show g `(let ([,x ,y]) ,z) t)
             (all 
               ! (!- g y tx) ! (!- `(generic ,x ,tx ,g) z t) !))))))))

(printff "~s ~s~%" 'with-robust-syntax-but-one-relation (test-!-7))

(define !-
  (relation (g exp t)
    (exists (g exp t)
      (reify-! 
        (lambda (!)
          ((to-show g exp t) ((!-/generator !) g exp t)))))))

(define !-/generator
  (lambda (!)
    (letrec
      ([!- (relation (g exp t)
             (exists (g t x y z tx)
               (select
                 ((to-show g `(var ,x) t)
                  (all ! (env g x t) !))
                 ((to-show g `(intc ,x) "int") !)
                 ((to-show g `(boolc ,x) "bool") !)
                 ((to-show g `(zero? ,x) "bool")
                  (all ! (!- g x "int") !))
                 ((to-show g `(sub1 ,x) "int")
                  (all ! (!- g x "int") !))
                 ((to-show g `(+ ,x ,y) "int")
                  (all ! (!- g x "int") ! (!- g y "int") !))
                 ((to-show g `(if ,x ,y ,z) t)
                  (all ! (!- g x "bool") ! (!- g y t) ! (!- g z t) !))
                 ((to-show g `(lambda (,x) ,y) `("->" ,tx ,t))
                  (all ! (!- `(non-generic ,x ,tx ,g) y t) !))
                 ((to-show g `(app ,x ,y) t)
                  (all ! (!- g x `("->" ,tx ,t)) ! (!- g y tx) !))
                 ((to-show g `(fix ,x) t)
                  (all ! (!- g x `("->" ,t ,t)) !))
                 ((to-show g `(let ([,x ,y]) ,z) t)
                  (all 
                    ! (!- g y tx) ! (!- `(generic ,x ,tx ,g) z t) !)))))])
      !-)))

(printff "~s ~s~%" 'with-robust-syntax-but-long-jumps (test-!-7))

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
      '(g.1 (let ([f (lambda (x) (var x))])
              (if (app (var f) (zero? (intc 5)))
                  (+ (app (var f) (intc 4)) (intc 8))
                  (+ (app (var f) (intc 3)) (intc 7))))
         "int"))))

(printff "~s ~s~%" 'with-robust-syntax-but-long-jumps/poly-let (test-!-8))

(define test-!-9
  (lambda ()
    (and
      (equal?
        (exists (g ?) 
          (solution 
            (!- g ? '("->" "int" "int"))))
        '((non-generic x.1 ("->" "int" "int") g.1)
          (var x.1)
          ("->" "int" "int")))
      (equal?
        (exists (g la f b)
          (solution
            (!- g `(,la (,f) ,b) '("->" "int" "int"))))
        '(g.1 (lambda (x.1) (var x.1)) ("->" "int" "int")))
      (equal?
        (exists (g h r q z y t)
          (solution 
            (!- g `(,h ,r (,q ,z ,y)) t)))
        '((non-generic x.1 "int" g.1)
          (+ (var x.1) (+ (var x.1) (var x.1)))
          "int"))
      (equal?
        (exists (g h r q z y t u v)
          (solution
            (!- g `(,h ,r (,q ,z ,y)) `(,t ,u ,v))))
        '(g.1 (lambda (x.1) (+ (var x.1) (var x.1)))
           ("->" "int" "int"))))))
        
(printff "~s ~s~%" 'type-inhabitation (test-!-9))        

(define invertible-binary-function->ternary-relation
  (lambda (op inverted-op)
    (relation (x y z)
      (select
        ((to-show x y z)
         (all
           (fails (instantiated z))
           ((fun op) z x y)))
        ((to-show x y z)
         (all
           (fails (instantiated y))
           ((fun inverted-op) y z x)))
        ((to-show x y z)
         (all
           (fails (instantiated x))
           ((fun inverted-op) x z y)))
        ((to-show x y z) ((fun op) z x y))))))

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

(printff "~s ~s~%" 'test-instantiated-1 (test-instantiated-1))

(define symbol->lnum
  (lambda (sym)
    (map char->integer (string->list (symbol->string sym)))))

(define lnum->symbol
  (lambda (lnums)
      (string->symbol (list->string (map integer->char lnums)))))

(define invertible-unary-function->binary-relation
  (lambda (op inverted-op)
    (relation (x y)
      (select
        ((to-show x y)
         (all
           (fails (instantiated y))
           ((fun op) y x)))
        ((to-show x y)
         (all
           (fails (instantiated x))
           ((fun inverted-op) x y)))
        ((to-show x y) ((fun op) y x))))))

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

(printff "~s ~s~%" 'test-instantiated-2 (test-instantiated-2))
