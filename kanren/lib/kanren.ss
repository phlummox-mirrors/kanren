; From dfried@cs.indiana.edu Thu Jan 30 14:10:42 2003
; Message-ID: <200301301410.h0UEAcN05746@bullshark.cs.indiana.edu>
; To: oleg@pobox.com
; Subject: Re: Fabulous!!
; In-Reply-To: Your message of "Tue, 28 Jan 2003 11:31:14 PST."
;              <200301281931.h0SJVEE9065468@adric.fnmoc.navy.mil> 
; Date: Thu, 30 Jan 2003 09:10:38 -0500
; From: Dan Friedman <dfried@cs.indiana.edu>

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

(define-syntax arity
  (syntax-rules ()
    [(_ x0) 1]
    [(_ x0 ...) (+ (arity x0) ...)]))

(define test-arity
  (lambda ()
    (equal?
      (expand '(arity a b c d e))
      '(+ 1 1 1 1 1))))

(printff "~s ~s~%" 'test-arity (test-arity))

(define-syntax exists
  (syntax-rules ()
    [(_ (name ...) body0 body1 ...)
     (let ([name (lv 'name)] ...) body0 body1 ...)]))

'(define there-exists
  (lambda (name proc)
    (proc (lv name))))

'(define-syntax exists
  (syntax-rules ()
    [(_ () body0 body1 ...) (begin body0 body1 ...)]
    [(_ (name0 name1 ...) body0 body1 ...)
     (there-exists 'name0 
       (lambda (name0)
         (exists (name1 ...) body0 body1 ...)))]))

(define existential
  (lambda (name f)
    (lambda (subst)
      ((f (lv name)) subst))))

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
              (car (car base))
              (nonempty-subst-in (cadr (car base)) refining)
              (refine (cdr base) refining
                (cond
                  [(assv (car (car base)) refining-survivors)
                   => (lambda (p) (remv p refining-survivors))]
                  [else refining-survivors])))])))

(define cons-if-real-commitment
  (lambda (lv term refined)
    (cond
      [(eqv? term lv) refined]
      [else (cons (list lv term) refined)])))

;; remove all elements of refining whose domain is in base:
(define restrict
  (lambda (refining base-dom)
    (cond
      [(null? refining) '()]
      [(memv (car (car refining)) base-dom)
       (restrict (cdr refining) base-dom)]
      [else (cons (car refining)
              (restrict (cdr refining) base-dom))])))


(define nonempty-subst-in
  (lambda (t subst)
    (cond
      [(lv? t)
       (cond
         [(assv t subst) => cadr]
         [else t])]
      [else t])))

(define subst-in
  (lambda (t subst)
    (cond
      [(empty-subst? subst) t]
      [else (nonempty-subst-in t subst)])))

(define unit-subst
  (lambda (var t)
    (list (list var t))))

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
        '((x.1 y.1) (y.1 z.1))
        '((x.1 a) (y.1 b) (z.1 y.1))
        '((x.1 b) (z.1 y.1))))))
  
(printff "~s ~s~%" 'test-compose-subst-4 (test-compose-subst-4))

(define _ (exists (_) _))

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
        '((x.1 3)))
      (equal?
        (concretize
          (exists (y)
            (unify 4 y empty-subst)))
        '((y.1 4)))
      (equal?
        (concretize
          (exists (x y)
            (unify x y empty-subst)))
        '((x.1 y.1)))
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

(define-syntax unify-incrementally
  (syntax-rules ()
    [(_ subst) (lambda (succk fk) (succk subst))]
    [(_ subst t-lexvar0 t-lexvar1 ...)
     (lambda (t)
       (cond
         [(unify t t-lexvar0 subst)
          => (lambda (subst)
	       (unify-incrementally subst t-lexvar1 ...))]
         [else (lambda@ (t-lexvar1 ...) (lambda (succk fk) (fk)))]))]))

(define test-unify-incrementally
  (lambda () 
    (equal?
      (concretize
        (exists (x y z)
          (let ([s (compose-subst
		     (compose-subst (unit-subst x 2) (unit-subst y 3))
		     (unit-subst z 4))])
            ((@ (unify-incrementally s x y z)
                2 3 4)
             (lambda (subst) subst)
             (lambda () '())))))
      '((x.1 2) (y.1 3) (z.1 4)))))

(printff "~s ~s~%" 'test-unify-incrementally (test-unify-incrementally))

(define-syntax select
  (syntax-rules ()
    [(_)
     (lambda (goal-fn lengoal)
       (lambda@ (sk fk subst cutk)
         (fk)))]
    [(_ rule0) rule0]
    [(_ rule0 rule1 ...)
     (lambda (goal-fn lengoal)
       (lambda@ (sk fk subst cutk)
         (@ (rule0 goal-fn lengoal)
            sk
            (lambda ()
              (@ ((select rule1 ...) goal-fn lengoal)
                 sk fk subst cutk))
            subst cutk)))]))

(define initial-fk (lambda () '()))
(define initial-sk
  (lambda@ (fk subst cutk)
    (cons subst fk)))

(define-syntax relation
  (syntax-rules ()
    [(_ (t-lexvar0 ...) body0 body1 ...)
     (lambda (t-lexvar0 ...)
       ((begin body0 body1 ...)
        (lambda (entering-subst)
          (unify-incrementally entering-subst t-lexvar0 ...))
        (arity t-lexvar0 ...)))]))

(define-syntax possible-arity-mismatch
  (syntax-rules ()
    [(_ lengoal t0 ...)
     (if (not (= (arity t0 ...) lengoal))
       (error 'to-show "arity of ~s is not ~s." (list t0 ...) lengoal))]))

(define-syntax to-show
  (syntax-rules ()
    [(_ t0 ...)
     (lambda (antecedent)
       (lambda (goal-fn lengoal)
         (lambda@ (sk fk entering-subst cutk)
           (possible-arity-mismatch lengoal t0 ...)
           ((@ (goal-fn entering-subst) t0 ...)
            (lambda (exiting-subst)
              (@ antecedent sk fk exiting-subst fk))
            fk))))]))

(define-syntax all
  (syntax-rules ()
    [(_) (lambda (sk) sk)]))

(define father
  (relation (dad child)
    ((to-show 'john 'sam) (all))))

(printff "~s ~s~%" 'test-father0
  (let ([result
          (@ (father 'john 'sam)
             initial-sk initial-fk empty-subst initial-fk)])
    (and
      (equal? (car result) '())
      (equal? ((cdr result)) '()))))

(define child-of-male
  (relation (child dad)
    (exists (child dad)
      ((to-show child dad) (father dad child)))))

(define test-child-of-male-0
  (lambda ()
    (equal?
      (concretize
        (car (@ (child-of-male 'sam 'john)
                initial-sk initial-fk empty-subst initial-fk)))
      '((child.1 sam) (dad.1 john)))))

(printff "~s ~s~%" 'test-child-of-male-0 (test-child-of-male-0))

(define-syntax fact
  (syntax-rules ()
    [(_ t0 ...) ((to-show t0 ...) (all))]))

(define father
  (relation (dad child)
    (select
      (fact 'john 'sam)
      (fact 'pete 'sal))))

(define test-father-1
  (lambda ()
    (let ([result
            (@ (father 'pete 'sal)
               initial-sk initial-fk empty-subst initial-fk)])
      (and
        (equal? (car result) '())
        (equal? ((cdr result)) '())))))

(printff "~s ~s~%" 'test-father-1 (test-father-1))

(define test-father-2
  (lambda ()
    (let ([result
            (@ (father 'pete 'sal)
               initial-sk initial-fk empty-subst initial-fk)])
      (and
        (equal? (car result) '())
        (equal? ((cdr result)) '())))))

(printff "~s ~s~%" 'test-father-2 (test-father-2))

(define query
  (let ([initial-fk (lambda () '())]
        [initial-sk (lambda@ (fk subst cutk) (cons subst fk))])
    (lambda (antecedent)
      (@ antecedent initial-sk initial-fk empty-subst initial-fk))))

(define test-father-3
  (lambda ()
    (let ([result (concretize
                    (exists (x)
                      (query (father 'pete x))))])
      (and
        (equal? (car result) '((x.1 sal)))
        (equal? ((cdr result)) '())))))

(printff "~s ~s~%" 'test-father-3 (test-father-3))

(define test-father-4
  (lambda ()
    (equal?
      (concretize
        (exists (x)
          (let ([term (list 'pete x)])
            (let ([answer (query (father 'pete x))])
              (map (lambda (t) (subst-in t (car answer))) term)))))
      '(pete sal))))

(printff "~s ~s~%" 'test-father-4 (test-father-4))

(define father
  (relation (dad child)
    (select
      (fact 'john 'sam)
      (fact 'sam 'pete)
      (fact 'pete 'sal)
      (fact 'pete 'pat))))

(define test-father-5
  (lambda ()
    (and
      (equal?
        (concretize
          (exists (x)
            (let ([term (list 'pete x)])
              (let ([answer1 (query (father 'pete x))])
                (list
                  (map (lambda (t) (subst-in t (car answer1))) term)
                  (let ([answer2 ((cdr answer1))])
                    (map (lambda (t) (subst-in t (car answer2))) term)))))))
        '((pete sal) (pete pat)))
      (equal?
        (concretize
          (exists (x)
            (let ([term (list 'pete x)])
              (let ([answer1 (query (father 'pete x))])
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

(define test-father-6/solve
  (lambda ()
    (and
      (equal?
        (exists (x) (solve 5 (father 'pete x)))
        '((pete sal) (pete pat)))
      (equal?
        (exists (x y) (solve 6 (father x y)))
        '((john sam) (sam pete) (pete sal) (pete pat))))))
            
(printff "~s ~s~%" 'test-father-6/solve (test-father-6/solve))

(define-syntax solution
  (syntax-rules ()
    [(_ x)
     (let ([ls (solve 1 x)])
       (if (null? ls) #f (car ls)))]))

(define test-father-7/solution
  (lambda ()
    (equal?
      (exists (x) (solution (father 'pete x)))
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
      (exists (x) (query-apply father `(pete ,x)))
      '(pete sal))))

(printff "~s ~s~%" 'test-father-7/query-apply (test-father-7/query-apply))

(define grandpa-sam
  (relation (grandchild)
    (exists (parent)
      ((to-show grandchild)
       (lambda@ (sk)
         ((father 'sam parent)
          ((father parent grandchild) sk)))))))

(define-syntax all
  (syntax-rules ()
    [(_) (lambda (sk) sk)]
    [(_ antecedent0) antecedent0]
    [(_ antecedent0 antecedent1 ...)
     (lambda (sk)
       (antecedent0 ((all antecedent1 ...) sk)))]))

(define test-grandpa-sam-1
  (lambda ()
    (equal?
      (exists (y) (solve 6 (grandpa-sam y)))
      '((sal) (pat)))))

(printff "~s ~s~%" 'test-grandpa-sam-1 (test-grandpa-sam-1))

(define-syntax any
  (syntax-rules ()
    [(_ antecedent ...)
     ((relation () (select ((to-show) antecedent) ...)))]))

(define child
  (relation (child dad)
    (exists (child dad)
      ((to-show child dad)
       (father dad child)))))

(define test-child-1
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (child x y)))
      '((sam john) (pete sam) (sal pete) (pat pete)))))

(printff "~s ~s~%" 'test-child-1 (test-child-1))

(define grandpa-sam
  (relation (grandchild)
    (exists (parent)
      ((to-show grandchild)
       (all
         (father 'sam parent)
         (father parent grandchild))))))

(define test-grandpa-sam-2
  (lambda ()
    (equal?
      (exists (y) (solve 6 (grandpa-sam y)))
      '((sal) (pat)))))

(printff "~s ~s~%" 'test-grandpa-sam-2 (test-grandpa-sam-2))

(define a-relation
  (relation (t1 ...)
    (select
      (exists (lv-names-1 ...)
        ((to-show term-11 ...)
         (all ant-11 ...)))
      ...
      (exists (lv-names-1 ...)
        ((to-show term-n1 ...)
         (all ant-n1 ...))))))

(define grandpa-maker
  (lambda (grandad)
    (relation (grandchild)
      (exists (parent)
        ((to-show grandchild)
         (all
           (father grandad parent)
           (father parent grandchild)))))))

(define test-grandpa-maker-1
  (lambda ()
    (equal?
      (exists (x) (solve 6 ((grandpa-maker 'sam) x)))
      '((sal) (pat)))))     

(printff "~s ~s~%" 'test-grandpa-maker-1 (test-grandpa-maker-1))

(define grandpa-maker
  (lambda (guide grandad)
    (relation (grandchild)
      (exists (parent)
        ((to-show grandchild)
         (all
           (guide grandad parent)
           (guide parent grandchild)))))))

(define test-grandpa-maker-2
  (lambda ()
    (equal?
      (exists (x) (solve 4 ((grandpa-maker father 'sam) x)))
      '((sal) (pat)))))

(printff "~s ~s~%" 'test-grandpa-maker-2 (test-grandpa-maker-2))

(define grandpa
  (relation (grandad grandchild)
    (exists (parent)
      ((to-show grandad grandchild)
       (all
         (father grandad parent)
         (father parent grandchild))))))

(define test-grandpa-1
  (lambda ()
    (equal?
      (exists (x) (solve 4 (grandpa 'sam x)))
      '((sam sal) (sam pat)))))

(printff "~s ~s~%" 'test-grandpa-1 (test-grandpa-1))

(define father
  (relation (dad child)
    (select
      (fact 'john 'sam)
      (fact 'sam 'pete)
      (fact 'sam 'polly)
      (fact 'pete 'sal)
      (fact 'pete 'pat))))

(define mother
  (relation (mom child)
    (select
      (fact 'polly 'betty)
      (fact 'polly 'david))))

(define grandpa
  (relation (grandad grandchild)
    (select
      (exists (parent)
        ((to-show grandad grandchild)
         (all
           (father grandad parent)
           (father parent grandchild))))
      (exists (parent)
        ((to-show grandad grandchild)
         (all
           (father grandad parent)
           (mother parent grandchild)))))))

(define test-grandpa-2
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa 'sam y)))
      '((sam sal) (sam pat) (sam betty) (sam david)))))

(printff "~s ~s~%" 'test-grandpa-2 (test-grandpa-2))

(define grandpa
  (relation (grandad grandchild)
    (select
      (exists (parent)
        ((to-show grandad grandchild)
         (all
           (father grandad parent)
           (father parent grandchild))))
      (exists (parent)
        ((to-show grandad grandchild)
         (all
           (father grandad parent)
           (mother parent grandchild)))))))

(define test-grandpa-3
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa 'sam y)))
      '((sam sal) (sam pat) (sam betty) (sam david)))))

(printff "~s ~s~%" 'test-grandpa-3 (test-grandpa-3))

(define grandpa
  (relation (grandad grandchild)
    (exists (parent)
      (select
        ((to-show grandad grandchild)
         (all
           (father grandad parent)
           (father parent grandchild)))
        ((to-show grandad grandchild)
         (all
           (father grandad parent)
           (mother parent grandchild)))))))

(define test-grandpa-4
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa 'sam y)))
      '((sam sal) (sam pat) (sam betty) (sam david)))))

(printff "~s ~s~%" 'test-grandpa-4 (test-grandpa-4))

(define-syntax extend-relation
  (syntax-rules ()
    [(_ (t-lexvar0 ...) rel0 rel1 ...)
     (lambda (t-lexvar0 ...)
       (lambda@ (sk fk subst cutk)
         (extend-relation-aux (t-lexvar0 ...)
           sk fk subst cutk rel0 rel1 ...)))]))

(define-syntax extend-relation-aux
  (syntax-rules ()
    [(_ (t-lexvar0 ...) sk fk subst cutk) (fk)]
    [(_ (t-lexvar0 ...) sk fk subst cutk rel0 rel1 ...)
     (@ (rel0 t-lexvar0 ...) sk
       (lambda ()
         (extend-relation-aux (t-lexvar0 ...) sk fk subst cutk rel1 ...))
       subst cutk)]))

(define grandpa/father
  (relation (grandad grandchild)
    ((to-show grandad grandchild)
     (exists (parent)
       (all
         (father grandad parent)
         (father parent grandchild))))))

(define grandpa/mother
  (relation (grandad grandchild)
    ((to-show grandad grandchild)
     (exists (parent)
       (all
         (father grandad parent)
         (mother parent grandchild))))))

(define grandpa
  (extend-relation (grandad grandchild) grandpa/father grandpa/mother))

(define test-grandpa-5
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa 'sam y)))
      '((sam sal) (sam pat) (sam betty) (sam david)))))

(printff "~s ~s~%" 'test-grandpa-5 (test-grandpa-5))

(define grandpa
  (extend-relation (grandad grandchild)
    (relation (grandad grandchild)
      ((to-show grandad grandchild)
       (exists (parent)
         (all
           (father grandad parent)
           (father parent grandchild)))))
    (relation (grandad grandchild)
      ((to-show grandad grandchild)
       (exists (parent)
         (all
           (father grandad parent)
           (mother parent grandchild)))))))

(define test-grandpa-6
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa 'sam y)))
      '((sam sal) (sam pat) (sam betty) (sam david)))))

(printff "~s ~s~%" 'test-grandpa-6a (test-grandpa-6))

(define grandpa
  (exists (parent)
    (extend-relation (grandad grandchild)
      (relation (grandad grandchild)
        ((to-show grandad grandchild)
         (all
           (father grandad parent)
           (father parent grandchild))))
      (relation (grandad grandchild)
        ((to-show grandad grandchild)
         (all
           (father grandad parent)
           (mother parent grandchild)))))))

(printff "~s ~s~%" 'test-grandpa-6b (test-grandpa-6))

(define-syntax relation@
  (syntax-rules ()
    [(_ (t-lexvar0 ...) body0 body1 ...)
     (let ([r (relation (t-lexvar0 ...) body0 body1 ...)])
       (relation@-aux (t-lexvar0 ...) (r t-lexvar0 ...)))]))

(define-syntax relation@-aux
  (syntax-rules ()
    [(_ (t-lexvar) body0 body1 ...)
     (relation (t-lexvar)
       ((to-show t-lexvar) body0 body1 ...))]
    [(_ (t-lexvar0 t-lexvar1 ...) body0 body1 ...)
     (lambda (t-lexvar0)
       (let ([r (relation (t-lexvar0)
                  ((to-show t-lexvar0)
                   (lambda@ (sk fk subst cutk)
                     (let ([t-lexvar0 (subst-in t-lexvar0 subst)])
                       (relation@-aux (t-lexvar1 ...) body0 body1 ...)))))])
         (query (r t-lexvar0))))]))

(define grandpa-sam
  (relation@ (child)
    ((to-show child)
     (exists (parent)
       (all 
         (father 'sam parent)
         (father parent child))))))

(define test-grandpa-sam-3
  (lambda ()
    (equal?
      (exists (y) (solve 6 (grandpa-sam y)))
      '((sal) (pat)))))

(printff "~s ~s~%" 'test-grandpa-sam-3 (test-grandpa-sam-3))

(define grandpa-sam
  (let ([r (relation (child)
             ((to-show child)
              (exists (parent)
                (all
                  (father 'sam parent)
                  (father parent child)))))])
    (relation (child)
      (exists (child)
        ((to-show child) (r child))))))

(define test-grandpa-sam-4
  (lambda ()
    (equal?
      (exists (y) (solve 6 (grandpa-sam y)))
      '((sal) (pat)))))

(printff "~s ~s~%" 'test-grandpa-sam-4 (test-grandpa-sam-4))

(define grandpa
  (relation@ (grandad child)
    (exists (grandad child)
      ((to-show grandad child)
       (exists (parent)
         (all 
           (father grandad parent)
           (father parent child)))))))

(define test-grandpa-7
  (lambda ()
    (equal?
      (exists (x y) (solve 8 ((grandpa x) y)))
      '((pete) (polly) (sal) (pat)))))

(printff "~s ~s~%" 'test-grandpa-7 (test-grandpa-7))

(define reify-cutk
  (lambda (proc)
    (lambda (goal-fn lengoal)
      (lambda@ (sk fk subst cutk)
        (@ ((proc cutk) goal-fn lengoal) sk fk subst cutk)))))

(define grandpa/father
  (relation (grandad grandchild)
    (reify-cutk
      (lambda (cutk)
        ((to-show grandad grandchild)
         (exists (parent)
           (all
             (father grandad parent)
             (father parent grandchild)
             (!! cutk))))))))

(define grandpa
  (extend-relation (grandad grandchild) grandpa/father grandpa/mother))

(define !!
  (lambda (exiting-fk)
    (lambda@ (sk fk subst cutk)
      (@ sk exiting-fk subst cutk))))

(define test-grandpa-8
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa x y)))
      '((john pete)))))

(printff "~s ~s~%" 'test-grandpa-8 (test-grandpa-8))

(define reify-!
  (lambda (proc)
    (lambda (goal-fn lengoal)
      (lambda@ (sk fk subst cutk)
        (@ ((proc (!! cutk)) goal-fn lengoal) sk fk subst cutk)))))

(define grandpa/father
  (relation (grandad grandchild)
    (reify-!
      (lambda (!)
        ((to-show grandad grandchild)
         (exists (parent)
           (all
             (father grandad parent)
             !
             (father parent grandchild))))))))

(define grandpa
  (extend-relation (grandad grandchild) grandpa/father grandpa/mother))

(define test-grandpa-9
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa x y)))
      '((john pete) (john polly)))))

(printff "~s ~s~%" 'test-grandpa-9 (test-grandpa-9))

(define grandpa/father
  (relation (grandad grandchild)
    (reify-!
      (lambda (!)
        ((to-show grandad grandchild)
         (exists (parent)
           (all
             !
             (father grandad parent)
             (father parent grandchild))))))))

(define grandpa
  (extend-relation (grandad grandchild) grandpa/father grandpa/mother))

(define test-grandpa-10
  (lambda ()
    (equal?
      (exists (x y) (solve 10 (grandpa x y)))
      '((john pete) (john polly) (sam sal) (sam pat)))))

(printff "~s ~s~%" 'test-grandpa-10 (test-grandpa-10))

(define fail
  (lambda args
    (lambda@ (sk fk subst cutk) (fk))))

(define no-grandma
  (relation (grandad grandchild)
    (reify-cutk
      (lambda (cutk)
        ((to-show grandad grandchild)
         (exists (parent)
           (all (mother grandad parent) (!! cutk) (fail))))))))

(define !fail
  (lambda (exiting-fk)
    (lambda@ (sk fk subst cutk)
      (exiting-fk))))

(define no-grandma
  (relation (grandad grandchild)
    (reify-cutk
      (lambda (cutk)
        ((to-show grandad grandchild)
         (exists (parent)
           (all (mother grandad parent) (!fail cutk))))))))

(define no-grandma-grandpa
  (extend-relation (grandad grandchild) no-grandma grandpa))

(define test-no-grandma-grandpa-1
  (lambda ()
    (equal?
      (exists (x) (solve 1 (no-grandma-grandpa 'polly x)))
      '())))

(printff "~s ~s~%" 'test-no-grandma-grandpa-1 (test-no-grandma-grandpa-1))

(define grandpa
  (relation (grandad grandchild)
    ((to-show grandad grandchild)
     (exists (parent)
       (all 
         (father grandad parent)
         (starts-with-p? parent)
         (father parent grandchild))))))

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

(define test1
  (lambda (x)
    (any ((pred <) 4 5) ((fun <) x 6 7))))

(define test-test1
  (lambda ()
    (equal?
      (exists (x) (solution (test1 x)))
      '(x.1))))

(printff "~s ~s~%" 'test-test1 (test-test1))

(define test2
  (lambda (x)
    (any ((pred <) 5 4) ((fun <) x 6 7))))

(define test-test2
  (lambda ()
    (equal?
      (exists (x) (solution (test2 x)))
      '(#t))))

(printff "~s ~s~%" 'test-test2 (test-test2))

(define test3
  (lambda (x y)
    (any ((fun <) x 5 4) ((fun <) y 6 7))))

(define test-test3
  (lambda ()
    (equal?
      (exists (x y) (solution (test3 x y)))
      '(#f y.1))))

(printff "~s ~s~%" 'test-test3 (test-test3))

(define fails
  (lambda (antecedent)
    (lambda@ (sk fk subst cutk)
      (@ antecedent
        (lambda@ (current-fk subst cutk) (fk))
        (lambda () (@ sk fk subst cutk))
        subst cutk))))

(define grandpa
  (relation (grandad grandchild)
    ((to-show grandad grandchild)
     (exists (parent)
       (all
         (father grandad parent)
         (fails (starts-with-p? parent))
         (father parent grandchild))))))

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
  (relation (grandad grandchild)
    ((to-show grandad grandchild)
     (exists (parent)
       (all
         (father grandad parent)
         (father parent grandchild)
         ;(view-subst grandchild)
         )))))

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
  (let ([father father])
    (extend-relation (dad child) father
      (relation (dad child)
        (select
          (fact 'john 'harry)
          (fact 'harry 'carl)
          (fact 'sam 'ed))))))

(define ancestor
  (relation (old young)
    (select
      ((to-show old young)
       (father old young))
      ((to-show old young)
       (exists (not-so-old)
         (all
           (father old not-so-old)
           (ancestor not-so-old young)))))))

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
  (relation (young-a young-b old)
    ((to-show young-a young-b old)
     (all
       (ancestor old young-a)
       (ancestor old young-b)))))

(define test-common-ancestor
  (lambda ()
    (equal?
      (exists (x) (solve 4 (common-ancestor 'pat 'ed x)))
      '((pat ed john) (pat ed sam)))))

(printff "~s ~s~%" 'test-common-ancestor (test-common-ancestor))

(define younger-common-ancestor
  (relation (young-a young-b old not-so-old)
    ((to-show young-a young-b old not-so-old)
     (all
       (common-ancestor young-a young-b not-so-old)
       (common-ancestor young-a young-b old)
       (ancestor old not-so-old)))))

(define test-younger-common-ancestor
  (lambda ()
    (equal?
      (exists (x) (solve 4 (younger-common-ancestor 'pat 'ed 'john x)))
      '((pat ed john sam)))))

(printff "~s ~s~%" 'test-younger-common-ancestor (test-younger-common-ancestor))

(define youngest-common-ancestor
  (relation (young-a young-b not-so-old)
    ((to-show young-a young-b not-so-old)
     (all
       (common-ancestor young-a young-b not-so-old)
       (exists (y)
         (fails
           (younger-common-ancestor young-a young-b not-so-old y)))))))

(define test-youngest-common-ancestor
  (lambda ()
    (equal?
      (exists (x) (solve 4 (youngest-common-ancestor 'pat 'ed x)))
      '((pat ed sam)))))

(printff "~s ~s~%" 'test-youngest-common-ancestor (test-youngest-common-ancestor))

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

(printff "~s ~s~%" 'test-Seres-Spiver (test-Seres-Spivey))

(define towers-of-hanoi
  (letrec
    ([move
       (relation (n a b c)
         (reify-!
           (lambda (!)
             (select
               ((to-show 0 _ _ _) !)
               (exists (m)
                 ((to-show n a b c)
                  (all
                    ((fun -) m n 1)
                    (move m a c b)
                    ((pred (lambda (x y)
                             (printff "Move a disk from ~s to ~s~n" x y)))
                     a b)
                    (move m c b a))))))))])
    (relation (n)
      ((to-show n) (move n 'left 'middle 'right)))))

(begin
  (printff "~s with 3 disks~n~n" 'test-towers-of-hanoi)
  (solution (towers-of-hanoi 3))
  (void))

(define nonempty-subst-in
  (lambda (t subst)
    (cond
      [(lv? t)
       (cond
         [(assv t subst) => cadr]
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
          '((x.1 3) (y.1 4)))
        (equal?
          (concretize
            (exists (x y) 
              (unify `(,x 4) `(3 ,y) empty-subst)))
          '((x.1 3) (y.1 4))))
      (and
        (equal?
          (concretize
            (exists (w x y z)     
              (unify `(,x 4 3 ,w) `(3 ,y ,x ,z) empty-subst)))
          '((x.1 3) (y.1 4) (w.1 z.1)))
        (equal?
          (concretize
            (exists (x y)
              (unify `(,x 4) `(,y ,y) empty-subst)))
          '((x.1 4) (y.1 4)))
        (equal?
          (exists (x y) 
            (unify `(,x 4 3) `(,y ,y ,x) empty-subst))
          #f)
        (equal?
          (concretize
            (exists (r v w x u)
              (unify `(,r (,v (,w ,x) 8)) `(,r (,u (abc ,u) ,x)) empty-subst)))
          '((v.1 8) (w.1 abc) (x.1 8) (u.1 8)))
        (equal?
          (concretize
            (exists (x y)
              (unify `(p (f a) (g ,x)) `(p ,x ,y) empty-subst)))
          '((x.1 (f a)) (y.1 (g (f a)))))
        (equal?
          (concretize
            (exists (x y)
              (unify `(p (g ,x) (f a)) `(p ,y ,x) empty-subst)))
          '((y.1 (g (f a))) (x.1 (f a))))
        (equal?
          (concretize
            (exists (x y z)
              (unify `(p a ,x (h (g ,z))) `(p ,z (h ,y) (h ,y)) empty-subst)))
          '((z.1 a) (x.1 (h (g a))) (y.1 (g a))))
        (equal?
          (concretize
            (exists (x y)
              (unify `(p ,x ,x) `(p ,y (f ,y)) empty-subst)))
          #f)))))

(printff "~s ~s~%" 'test-unify/pairs-eager (test-unify/pairs))

(define towers-of-hanoi-path
  (let ([steps '()])
    (letrec
        ([move
           (relation (n a b c)
             (reify-!
               (lambda (!)
                 (select
                   ((to-show 0 _ _ _) !)
                   (exists (m)
                     ((to-show n a b c)
                      (all
                        ((fun -) m n 1)
                        (move m a c b)
                        ((pred (lambda (x y)
                                 (set! steps (cons (list x y) steps))))
                         a b)
                        (move m c b a))))))))])
      (relation (n path)
        (set! steps '())
        (select
          ((to-show n path) (fails (move n 'left 'middle 'right)))
          ((to-show n path) (== path (reverse steps))))))))

(define test-towers-of-hanoi-path
  (lambda ()
    (equal?
      (exists (path) (solution (towers-of-hanoi-path 3 path)))
      '(3 ((left middle)
           (left right)
           (middle right)
           (left middle)
           (right left)
           (right middle)
           (left middle))))))

(printff "~s ~s~n" 'test-towers-of-hanoi-path (test-towers-of-hanoi-path))

(define test-fun-resubstitute
  (lambda ()
    (equal?
      (concretize
        (let ([j (relation (z)
                   (exists (x w z)
                     ((to-show z)
                      (all
                        ((fun (lambda () 4)) x)
                        ((fun (lambda () 3)) w)
                        ((fun (lambda (y) (cons x y))) z w)))))])
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
    (cons (list t-var u)
      (map
        (lambda (b)
          (list (car b) (subst-in-with-virtual-unit-subst (cadr b) t-var u)))
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
           (list (car c)
             (substitute-vars-recursively (cadr c) subst)))
      subst)))

(define substitute-vars-recursively
  (lambda (term subst)
    (letrec
        ([resolve-var
           (lambda (var)
             (cond
               [(assv var subst) =>
                (lambda (c)
                  (substitute-vars-recursively (cadr c) (remq c subst)))]
               [else var]))])
      (traverse-term resolve-var term))))

(define traverse-term ;;; probably can use copy-term, here.
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
          => (lambda (c) (nonempty-subst-in (cadr c) subst))]
         [else t])]
      [(pair? t)
       (cons
         (nonempty-subst-in (car t) subst)
         (nonempty-subst-in (cdr t) subst))]
      [else t])))

(define unify
  (lambda (t u subst)
    (cond
      [(or (eqv? t u) (eqv? t _) (eqv? u _)) subst]
      [(lv? t)
       (cond
         [(assv t subst)
          => (lambda (t-binding)        ; t is bound
               (unify (cadr t-binding) u subst))]
         [(lv? u) (unify-with-unbound-lv-and-other-is-lv t u subst)]
         [else (unify-with-unbound-lv-and-other-is-value t u subst)])]
      [(lv? u)
       (cond
         [(assv u subst)
          => (lambda (u-binding)        ; u is bound
               (unify (cadr u-binding) t subst))]
         [else (unify-with-unbound-lv-and-other-is-value u t subst)])]
      [(and (pair? t) (pair? u))
       (cond
         [(unify (car t) (car u) subst)
          => (lambda (car-subst)
               (unify (cdr t) (cdr u) car-subst))]
         [else #f])]
      [(equal? t u) subst]
      [else #f])))

(define unify-with-unbound-lv-and-other-is-lv
  (lambda (unbound-t-var u-var subst)
    (cond
      [(assv u-var subst)                  
       => (lambda (u-binding)                       ; u-var is bound
            (let ([u-val (cadr u-binding)])
              (cons-if-real-commitment unbound-t-var u-val subst)))]
      [else (compose-subst (unit-subst unbound-t-var u-var) subst)])))

;;; Don't add the commitment of an uncommited variable x to a pair (a . b)
; instead, add the commitment x = (var1 . var2) and
; unify var1 with a and var2 with b.

(define unify-with-unbound-lv-and-other-is-value
  (lambda (unbound-t-var u-value subst)
    (cond
      [(pair? u-value)
       (let ([car-var (lv 'a:)]
             [cdr-var (lv 'd:)])
         (let ([new-pair (cons car-var cdr-var)])
           (cond
             [(unify car-var (car u-value)
                (compose-subst (unit-subst unbound-t-var new-pair) subst))
              => (lambda (subst)
                   (unify cdr-var (cdr u-value) subst))]
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

(define towers-of-hanoi-path
  (let ([steps '()])
    (letrec
        ([move
           (relation (n a b c)
             (reify-!
               (lambda (!)
                 (select
                   ((to-show 0 _ _ _) !)
                   (exists (m)
                     ((to-show n a b c)
                      (all
                        ((fun -) m n 1)
                        (move m a c b)
                        ((pred (lambda (x y)
                                 (set! steps (cons (list x y) steps))))
                         a b)
                        (move m c b a))))))))])
      (relation (n path)
        (set! steps '())
        (select
          ((to-show n path) (fails (move n 'left 'middle 'right)))
          ((to-show n path) (== path (reverse steps))))))))

(printff "~s ~s~n" 'test-towers-of-hanoi-path (test-towers-of-hanoi-path))

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
          '((y.1 4) (x.1 3)))
        (equal?
          (concretize
            (exists (x y) 
              (unify `(,x 4) `(3 ,y) empty-subst)))
          '((y.1 4) (x.1 3))))
      (and
        (equal?
          (concretize
            (exists (w x y z)     
              (unify `(,x 4 3 ,w) `(3 ,y ,x ,z) empty-subst)))
          '((w.1 z.1) (y.1 4) (x.1 3)))
        (equal? ;;; not in Oleg's; his is ((x.1 4)) after normalizing
          (concretize
            (exists (x y)
              (normalize-subst (unify `(,x 4) `(,y ,y) empty-subst))))
          '((y.1 4) (x.1 4)))
        (equal?
          (exists (x y) 
            (unify `(,x 4 3) `(,y ,y ,x) empty-subst))
          #f)
        (equal? 
          (concretize
            (exists (r v w x u)
              (let ([s (normalize-subst
                         (unify `(,r (,v (,w ,x) 8)) `(,r (,u (abc ,u) ,x)) empty-subst))])
                (let ([vars (list u x w v)])
                  (map list vars (substitute-vars-recursively vars s))))))
          '((u.1 8) (x.1 8) (w.1 abc) (v.1 8)))
        (equal? 
          (concretize
            (exists (x y)
              (let ([s (normalize-subst
                         (unify `(p (f a) (g ,x)) `(p ,x ,y) empty-subst))])
                (let ([vars (list y x)])
                  (map list vars (substitute-vars-recursively vars s))))))
          '((y.1 (g (f a))) (x.1 (f a))))
        (equal? 
          (concretize
            (exists (x y)
              (let ([s (normalize-subst
                         (unify `(p (g ,x) (f a)) `(p ,y ,x) empty-subst))])
                (let ([vars (list x y)])
                  (map list vars (substitute-vars-recursively vars s))))))
          '((x.1 (f a)) (y.1 (g (f a)))))
        (equal? 
          (concretize
            (exists (x y z)
              (let ([s (normalize-subst
                         (unify `(p a ,x (h (g ,z))) `(p ,z (h ,y) (h ,y)) empty-subst))])
                (let ([vars (list y x z)])
                  (map list vars (substitute-vars-recursively vars s))))))
          '((y.1 (g a)) (x.1 (h (g a))) (z.1 a)))
        (equal? 
          (concretize ;;; was #f
            (exists (x y)
              (let ([s (unify `(p ,x ,x) `(p ,y (f ,y)) empty-subst)])
                (let ([var (map car s)])
                  (map list var (substitute-vars-recursively var s))))))
          '((d:.1 ())
            (a:.1 (f a:.1))
            (d:.2 ((f . d:.2)))
            (a:.2 f)
            (y.1 (f (f . d:.2)))
            (x.1 (f (f . d:.2)))))))))
          
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
  (relation (xs ys zs)
    (select
      (exists (xs)
        (fact '() xs xs))
      (exists (x xs zs)
        ((to-show `(,x . ,xs) ys `(,x . ,zs))
         (concat xs ys zs))))))

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
        '((() s.1 s.1)
          ((x.1) zs.1 (x.1 . zs.1))
          ((x.1 x.2) zs.2 (x.1 x.2 . zs.2))
          ((x.1 x.2 x.3) zs.3 (x.1 x.2 x.3 . zs.3))
          ((x.1 x.2 x.3 x.4) zs.4 (x.1 x.2 x.3 x.4 . zs.4))
          ((x.1 x.2 x.3 x.4 x.5) zs.5 (x.1 x.2 x.3 x.4 x.5 . zs.5))))
      (equal?
        (exists (q r) (solve 6 (concat q '(u v) `(a b c . ,r))))
        '(((a b c) (u v) (a b c u v))
          ((a b c x.1) (u v) (a b c x.1 u v))
          ((a b c x.1 x.2) (u v) (a b c x.1 x.2 u v))
          ((a b c x.1 x.2 x.3) (u v) (a b c x.1 x.2 x.3 u v))
          ((a b c x.1 x.2 x.3 x.4) (u v) (a b c x.1 x.2 x.3 x.4 u v))
          ((a b c x.1 x.2 x.3 x.4 x.5) (u v) (a b c x.1 x.2 x.3 x.4 x.5 u v))))
      (equal?
        (exists (q) (solve 6 (concat q '() q)))
        '((() () ())
          ((x.1) () (x.1))
          ((x.1 x.2) () (x.1 x.2))
          ((x.1 x.2 x.3) () (x.1 x.2 x.3))
          ((x.1 x.2 x.3 x.4) () (x.1 x.2 x.3 x.4))
          ((x.1 x.2 x.3 x.4 x.5) () (x.1 x.2 x.3 x.4 x.5)))))))       

(printff "~s ~s~%" 'test-concat (test-concat))

(define base-concat
  (relation (xs ys zs)
    (exists (xs)
      (fact '() xs xs))))

(define nonbase-concat
  (relation (xs ys zs)
    (exists (x xs zs)
      ((to-show `(,x . ,xs) ys `(,x . ,zs))
       (concat xs ys zs)))))

(define concat (extend-relation (xs ys zs) base-concat nonbase-concat))

(printff "~s ~s~%" 'test-concat/extend (test-concat))

(define curried-concat
  (relation@ (xs ys zs)
    (select
      (exists (xs)
        (fact '() xs xs))
      (exists (x xs zs)
        ((to-show `(,x . ,xs) ys `(,x . ,zs))
         (@ curried-concat xs ys zs))))))

(define test-curried-concat
  (lambda ()
    (equal?
      (exists (q) (solve 6 (((curried-concat q) '()) q)))
      '((())
        ((x.1))
        ((x.1 x.2))
        ((x.1 x.2 x.3))
        ((x.1 x.2 x.3 x.4))
        ((x.1 x.2 x.3 x.4 x.5))))))

(printff "~s ~s~%" 'test-curried-concat (test-curried-concat))

;;;; Types from here on out.

(define int-rel
  (relation (g x t)
    (reify-!
      (lambda (!)
        (exists (g x)
          ((to-show g x "int")
           (all ((pred integer?) x) !)))))))

(define bool-rel
  (relation (g x t)
    (reify-!
      (lambda (!)
        (exists (g x)
          ((to-show g x "bool")
           (all ((pred boolean?) x) !)))))))

(define !- (extend-relation (g x t) int-rel bool-rel))

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
  (relation (g x t)
    (reify-!
      (lambda (!)
        (exists (g x)
          ((to-show g `(zero? ,x) "bool")
           (all ! (!- g x "int") !)))))))
  
(define sub1-rel
  (relation (g x t)
    (reify-!
      (lambda (!)
        (exists (g x)
          ((to-show g `(sub1 ,x) "int")
           (all ! (!- g x "int") !)))))))

(define +-rel
  (relation (g exp t)
    (reify-!
      (lambda (!)
        (exists (g x y)
          ((to-show g `(+ ,x ,y) "int")
           (all ! (!- g x "int") ! (!- g y "int") !)))))))

(define !- (let ([!- !-]) (extend-relation (g exp t) !- zero?-rel sub1-rel +-rel)))

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
  (relation (g exp t)
    (reify-!
      (lambda (!)
        (exists (g t test conseq alt)
          ((to-show g `(if ,test ,conseq ,alt) t)
           (all !
             (!- g test "bool") !
             (!- g conseq t) !
             (!- g alt t) !)))))))

(define !- (let ([!- !-]) (extend-relation (g exp t) !- if-rel)))

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
  (relation (g v t)
    (reify-!
      (lambda (!)
        ((to-show g v t)
         (all ((pred symbol?) v) ! (env g v t) !))))))

(define env
  (relation (g v t)
    (reify-cutk
      (lambda (cutk)
        (exists (v t g w type-w)              
          (select
            ((to-show `(non-generic ,v ,t ,g) v t)
             (!! cutk))
            ((to-show `(non-generic ,v ,t ,g) v type-w)
             (all (!! cutk) (unequal? t type-w) (!fail cutk)))
            ((to-show `(non-generic ,w ,type-w ,g) v t)
             (all (!! cutk) (unequal? w v) (env g v t)))))))))

(define unequal?
  (relation (a b)
    (reify-cutk
      (lambda (cutk)
	(select
	  ((to-show a a) (!fail cutk))
	  ((to-show a b) (fails (fail))))))))

(define !- (let ([!- !-]) (extend-relation (g v t) !- lexvar-rel)))

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

(define lambda-rel
  (relation (g exp t)
    (reify-!
      (lambda (!)
        (exists (g t v body type-v)
          ((to-show g `(lambda (,v) ,body) `("->" ,type-v ,t))
           (all ! (!- `(non-generic ,v ,type-v ,g) body t) !)))))))

(define !- (let ([!- !-]) (extend-relation (g exp t) !- lambda-rel)))

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

(printff "~s ~s~%" 'variables-4a (test-!-4a))

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
        [(assq t env)
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


