;; minikanrensupport.ss

(define-syntax def-syntax
  (syntax-rules ()
    [(_ (name . lhs) rhs)
     (define-syntax name
       (syntax-rules ()
         [(_ . lhs) rhs]))]))

(print-gensym #f)

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

(define-syntax let*-and
  (syntax-rules ()
    [(_ false-exp () body0 body1 ...) (begin body0 body1 ...)]
    [(_ false-exp ([var0 exp0] [var1 exp1] ...) body0 body1 ...)
     (let ([var0 exp0])
       (if var0
         (let*-and false-exp ([var1 exp1] ...) body0 body1 ...)
         false-exp))]))

(define-syntax test-check
  (syntax-rules ()
    [(_ title tested-expression expected-result)
     (begin
       (cout "Testing " title nl)
       (let* ([expected expected-result]
              [produced tested-expression])
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced))))]))

(define nl (string #\newline))

(define (cout . args)
  (for-each (lambda (x)
              (if (procedure? x) (x) (display x)))
            args))

(define-record logical-variable (id) ())
(define logical-variable make-logical-variable)
(define var? logical-variable?)

(define commitment cons)             ;;; change to list
(define commitment->term cdr)        ;;; and change to cadr
(define commitment->var car)

(define empty-subst '())

(define _ (logical-variable '_))

(define vars-of
  (lambda (term)
    (let loop ([term term] [fv '()])
      (cond
        [(var? term) (if (memq term fv) fv (cons term fv))]
        [(pair? term) (loop (cdr term) (loop (car term) fv))]
        [else fv]))))

(define concretize
  (lambda (t)
    (subst-in t
      (let loop ([fv (reverse (vars-of t))] [env '()])
	(cond
	  [(null? fv) empty-subst]
	  [else (let ([id (logical-variable-id (car fv))])
		  (let ([num (let*-and 0 ([pr (assq id env)]) (+ (cdr pr) 1))])
		    (cons (commitment (car fv) (artificial-id id num))
		      (loop (cdr fv) (cons (cons id num) env)))))])))))

(define artificial-id
  (lambda (t-id num)
    (string->symbol
      (string-append
        (symbol->string t-id) "." (number->string num)))))

(define subst-in
  (lambda (t subst)
    (cond
      [(var? t)
       (let*-and t ([ct (assq t subst)])
         (subst-in (commitment->term ct) subst))]
      [(pair? t) (cons (subst-in (car t) subst) (subst-in (cdr t) subst))]
      [else t])))

(define unify
  (lambda (t u subst)
    (cond
      [(or (eq? t u) (eq? t _) (eq? u _)) subst]
      [(and (var? t) (var? u)) (unify-var/var t u subst)]
      [(var? t) (unify-var/nonvar t u subst)]
      [(var? u) (unify-var/nonvar u t subst)]
      [else (unify-nonvar/nonvar t u subst)])))

(define unify-var/nonvar
  (lambda (t u subst)
    (let ([ct (assq t subst)])
      (if ct
        (unify-nonvar/bound u ct subst)
        (if (pair? u)
          (unify-free/list t u subst)
          (extend-subst t u subst))))))

(define unify-var/var
  (lambda (t u subst)
    (let ([ct (assq t subst)]
          [cu (assq u subst)])
      (cond
        [(and ct cu)
         (unify-i/i (commitment->term ct) (commitment->term cu) subst)]
        [ct (unify-free/bound u ct subst)]
        [cu (unify-free/bound t cu subst)]
        [else (extend-subst t u subst)]))))

(define unify-i/i
  (lambda (t u subst)
    (unify t u subst)))

(define unify-free/bound
  (lambda (t cu subst)
    (let loop ([cu cu])
      (let ([u (commitment->term cu)])
        (cond
          [(eq? u t) subst]
          [(var? u)
           (cond
             [(assq u subst) => loop]
             [else (extend-subst t u subst)])]
          [else (extend-subst t u subst)])))))

(define unify-nonvar/nonvar
  (lambda (t u subst)
    (if (and (pair? t) (pair? u))
      (let*-and #f ([subst (unify (car t) (car u) subst)])
        (unify (cdr t) (cdr u) subst))
      (if (equal? t u) subst #f))))

(define extend-subst
  (lambda (var term subst)
    (cons (commitment var term) subst)))

(define unify-nonvar/bound
  (lambda (t cu subst)
    (let loop ([cu cu])
      (let ([u (commitment->term cu)])
        (cond                                
          [(var? u)
           (cond
             [(assq u subst) => loop]
             [(pair? t) (unify-free/list u t subst)]
             [else (extend-subst u t subst)])]
          [else (unify-nonvar/nonvar u t subst)])))))

(define unify-free/list
  (lambda (t u subst)
    (extend-subst t (remove-anon u) subst)))
  
(define remove-anon
  (letrec
    ([contains-anon?
       (lambda (t)
         (or (eq? t _)
             (and (pair? t)
                  (or (contains-anon? (car t)) (contains-anon? (cdr t))))))]
     [copy-no-anon
       (lambda (t)
         (cond
           [(eq? t _) (logical-variable 'anon)]
           [(pair? t) (cons (copy-no-anon (car t)) (copy-no-anon (cdr t)))]
           [else t]))])
  (lambda (t)
    (if (contains-anon? t)
      (copy-no-anon t)
      t))))



