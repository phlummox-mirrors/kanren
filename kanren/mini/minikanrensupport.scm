(define-syntax def-syntax
  (syntax-rules ()
    [(_ (name . lhs) rhs)
     (define-syntax name
       (syntax-rules ()
         [(_ . lhs) rhs]))]))

(print-gensym #f)

(define-syntax let*-values
  (syntax-rules ()
    [(_ () body bodies ...) (begin body bodies ...)]
    ((_ ([(var ...) rhs-exp] [vars* rhs-exp*] ...) bodies ...)
     (call-with-values (lambda () rhs-exp)
       (lambda (var ...) (let*-values ([vars* rhs-exp*] ...) bodies ...))))))

(define-syntax lambda@
  (syntax-rules ()
    [(_ () body0 body1 ...) (lambda () body0 body1 ...)]
    [(_ (formal) body0 body1 ...) (lambda (formal) body0 body1 ...)]
    [(_ (formal0 formal1 formal2 ...) body0 body1 ...)
     (lambda (formal0)
       (lambda@ (formal1 formal2 ...) body0 body1 ...))]))

(define-syntax @  
  (syntax-rules ()
    [(_ rator) (rator)]
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

(define prefix
  (lambda (n strm)
    (prefix-aux (- n 1) strm)))

(define prefix-aux
  (lambda (n strm)
    (cond
      [(null? strm) '()]
      [else
        (cons (reify-answer (car strm))
          (cond
            [(zero? n) '()]
            [else (prefix-aux (- n 1) (@ (cdr strm)))]))])))

(define prefix*
  (lambda (strm)
    (cond
      [(null? strm) '()]
      [else
        (cons (reify-answer (car strm))
          (prefix* (@ (cdr strm))))])))

(define reify-answer
  (lambda (answer)
    (reify (car answer) (cdr answer))))

(define reify
  (lambda (v s)
    (reify-fresh
      (reify-nonfresh v s))))

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

; (define-record logical-variable (id) ())
; (define var make-logical-variable)
; (define var? logical-variable?)
; (define var-id logical-variable-id)

(define empty-s '())

(define var-id
  (lambda (x)
    (vector-ref x 0)))

(define var
  (lambda (id)
    (vector id)))

(define var?
  (lambda (x)
    (vector? x)))

(define ground?
  (lambda (v)
    (cond
      ((var? v) #f)
      ((pair? v)
       (and (ground? (car v)) (ground? (cdr v))))
      (else #t))))

(define association
  (lambda (x s)
    (assq x s)))

(define rhs
  (lambda (b)
    (cdr b)))

(define reify-nonfresh
  (lambda (v s)
    (r-nf (walk v s) s)))

(define r-nf
  (lambda (v s)
    (cond
      [(pair? v)
       (cons
         (r-nf (walk (car v) s) s)
         (r-nf (walk (cdr v) s) s))]
      [else v])))

(define walk
  (lambda (v s)
    (cond
      [(var? v)
       (cond
         [(association v s) =>
          (lambda (pr)
            (rhs (walk-pr pr s)))]
         [else v])]
      [else v])))

(define walk-pr
  (lambda (pr s)
    (cond
      [(var? (rhs pr))
       (cond
         [(association (rhs pr) s) =>
          (lambda (pr)
            (walk-pr pr s))]
         [else pr])]
      [else pr])))

(define ext-s
  (lambda (x v s)
    (cons (cons x v) s)))
 
;;;; reify

;;; Thoughts: reify should be the composition of
;;; reify/non-fresh with reify/fresh.  reify/non-fresh
;;; is also known as reify-nonfresh.  reify/fresh was also
;;; knows as reify.

;;;;; This is the code of reify

(define reify-fresh
  (lambda (v)
    (r-f v '() empty-s
      (lambda (p* s) (reify-nonfresh v s)))))

(define r-f
  (lambda (v p* s k)
    (cond
      ((var? v)
       (let ((id (var-id v)))
         (let ((n (index (var-id v) p*)))
           (k (cons `(,id . ,n) p*)
              (ext-s v (reify-id id n) s)))))
      ((pair? v)
       (r-f (walk (car v) s) p* s
         (lambda (p* s)
           (r-f (walk (cdr v) s) p* s k))))
      (else (k p* s)))))

(define index
  (lambda (id p*)
    (cond
      [(assq id p*)
       => (lambda (p)
            (+ (cdr p) 1))]
      (else 0))))

(define reify-id
  (lambda (id index)
    (string->symbol
      (string-append
        (symbol->string id)
        "$_{_"
        (number->string index)
        "}$"))))

(define reify-id
  (lambda (id index)
    (string->symbol
      (string-append
        (symbol->string id)
        (string #\.)
        (number->string index)))))

(define reify-test
  (lambda ()
    (reify-fresh
      (let ([x (var 'x)]
            [xx (var 'x)]
            [xxx (var 'x)])
        `(,x 3 ,xx 5 ,xxx ,xxx ,xx ,x)))))

(define unify-check
  (lambda (v w s)
    (let ((v (walk v s))
          (w (walk w s)))
      (cond
        ((eq? v w) s)
        ((var? v)
         (cond
           ((occurs? v w s) #f)
           (else (ext-s v w s))))
        ((var? w)
         (cond
           ((occurs? w v s) #f)
           (else (ext-s w v s))))
        ((and (pair? v) (pair? w))
         (cond
           ((unify-check (car v) (car w) s) =>
            (lambda (s)
              (unify-check (cdr v) (cdr w) s)))
           (else #f)))
        ((or (pair? v) (pair? w)) #f)
        ((equal? v w) s)
        (else #f)))))

(define unify
  (lambda (v w s)
    (let ((v (walk v s))
          (w (walk w s)))
      (cond
        ((eq? v w) s)
        ((var? v) (ext-s v w s))
        ((var? w) (ext-s w v s))
        ((and (pair? v) (pair? w))
         (cond
           ((unify (car v) (car w) s) =>
            (lambda (s)
              (unify (cdr v) (cdr w) s)))
           (else #f)))
        ((or (pair? v) (pair? w)) #f)
        ((equal? v w) s)
        (else #f)))))

(define unify-check
  (lambda (v w s)
    (let ((v (walk v s))
          (w (walk w s)))
      (cond
        ((eq? v w) s)
        ((var? v) (ext-s-check v w s))
        ((var? w) (ext-s-check w v s))
        ((and (pair? v) (pair? w))
         (cond
           ((unify (car v) (car w) s) =>
            (lambda (s)
              (unify (cdr v) (cdr w) s)))
           (else #f)))
        ((or (pair? v) (pair? w)) #f)
        ((equal? v w) s)
        (else #f)))))

(define ext-s-check
  (lambda (v w s)
    (cond
      [(occurs? v w) #f]
      [else (ext-s v w s)])))

(define occurs?
  (lambda (x v s)
    (cond
      [(var? v) (eq? v x)]
      [(pair? v)
       (or (occurs? x (walk (car v) s) s)
           (occurs? x (walk (cdr v) s) s))]
      [else #f])))

;;; empty-s, pointer to reify-nonfresh, var-id,
;;; reify-var, r-f, walk, string->symbol,
;;; number->string, string-append, symbol->string
;;; string, ext-s, assq.

(define _ (var '_))

(define unify_
  (lambda (v w s)
    (let ((v (walk v s))
          (w (walk w s)))
      (cond
        ((eq? v w) s)
        ((var? v) (ext-s_ v w s))
        ((var? w) (ext-s_ w v s))
        ((and (pair? v) (pair? w))
         (cond
           ((unify_ (car v) (car w) s) =>
            (lambda (s)
              (unify_ (cdr v) (cdr w) s)))
           (else #f)))
        ((or (pair? v) (pair? w)) #f)
        ((equal? v w) s)
        (else #f)))))

(define ext-s_
  (lambda (v w s)
    (cond
      [(eq? v _) s]
      [(eq? w _) s]
      [(has_ w) (ext-s v (no-anons w) s)]
      [else (ext-s v w s)])))

(define no-anons
  (lambda (v)
    (cond
      [(pair? v)
       (cons (no-anons (car v)) (no-anons (cdr v)))]
      [(eq? v _) (var '_)]
      [else v])))

(define has_
  (lambda (v)
    (cond
      [(pair? v)
       (or (has_ (car v)) (has_ (cdr v)))]
      [else (eq? v _)])))

(define count-cons 0)

