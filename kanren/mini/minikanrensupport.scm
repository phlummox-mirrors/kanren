'(define-syntax def-syntax
  (syntax-rules ()
    [(_ (name . lhs) rhs)
     (define-syntax name
       (syntax-rules ()
         [(_ . lhs) rhs]))]))

(print-gensym #f)

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

(define var       ;;;;; (and needs explaining)
  (lambda (id)
    (vector (symbol->string id))))

(define var?
  (lambda (x)
    (vector? x)))


; Process the substitutions in such a way so that the results are
; pleasant to print.
; for each unbound variable in a chain
;  var1 -> var2 -> var3 ... -> varn
; we create an association
;  var1 -> var*
; where var* is chosen to be canonical in a sense
; e.g., it has the lexicographically smaller name.

(define (remq x lst)
  (let ((cell (assq x lst)))
    (and cell
      (let loop ((lst lst) (res '()))
	(if (eq? cell (car lst))
	  (cons cell (append res (cdr lst)))
	  (loop (cdr lst) (cons (car lst) res)))))))

(define beautify-subst
  (lambda (subst)
    (define (least lst)
      (let loop ((e (car lst)) (lst (cdr lst)))
	(cond 
	  ((null? lst) e)
	  ((string<? (var-id (car lst)) (var-id e)) (loop (car lst) (cdr lst)))
	  (else (loop e (cdr lst))))))
    (define (beautify free free-rev)
      (let ((least-l (map (lambda (a) (cons (car a) (least a))) free-rev)))
	(let loop ((free free))
	  (if (null? free) '()
	    (let* ((a (car free))
		   (least-name (cdr (assq (cdr a) least-l))))
	      (if (eq? (car a) least-name) (loop (cdr free))
		(cons (cons (car a) least-name) (loop (cdr free)))))))))
    ; first, we partition vars into bound and free
    (let loop ((s subst) (bound '()) (free '()) (free-rev '()))
      (if (null? s) (append (beautify free free-rev) bound)
	(let ((s0 (car s)) (sr (cdr s)))
	  (cond
	    ((not (var? (cdr s0))) ; bound
	      (loop sr (cons s0 bound) free free-rev))
	    ((assq (cdr s0) bound)
	     (loop sr (cons s0 bound) free free-rev))
	    (else
	      (let ((wr (walk-var (cdr s0) subst)))
		(if (var? wr)
		  (loop sr bound (cons (cons (car s0) wr) free)
		    (let ((rev (remq wr free-rev)))
		      (if rev (cons (cons wr (cons (car s0) (cdar rev)))
				(cdr rev))
			(cons (list wr (car s0)) free-rev))))
		  (loop sr (cons s0 bound) free free-rev))))))))))

(define ground?
  (lambda (v)
    (cond
      ((var? v) #f)
      ((pair? v)
       (and (ground? (car v)) (ground? (cdr v))))
      (else #t))))

(define rhs
  (lambda (b)
    (cdr b)))

(define reify-nonfresh 
  (lambda (x s)
    (let ((s (beautify-subst s)))
      (let ((v (walk-var x s)))
	(cond
	  ((var? v) x)
	  (else (r-nf v s)))))))

(define r-nf
  (lambda (v s)
    (cond
      [(pair? v)
       (cons
         (r-nf (walk (car v) s) s)
         (r-nf (walk (cdr v) s) s))]
      [else v])))

(define walk-var
  (lambda (x s)
    (cond
      [(assq x s) =>
       (lambda (pr)
         (walk (cdr pr) s))]
      [else x])))

(define walk
  (lambda (v s)
    (cond
      [(var? v) (walk-var v s)]
      [else v])))

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

(define r-f           ;;;;; NEW
  (lambda (v p* s k)
    (cond
      ((var? v)
       (let ((str (var-id v)))
         (let ((id (string->symbol str)))
           (let ((n (index id p*)))
             (k (cons `(,id . ,n) p*)
                (ext-s v (reify-id str n) s))))))
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

(define reify-id      ;;;;; NEW
  (lambda (name-str index)
    (string->symbol
      (string-append
        name-str
        "$_{_"
        (number->string index)
        "}$"))))

(define reify-id      ;;;; NEW
  (lambda (s index)
    (string->symbol
      (string-append s (string #\.) (number->string index)))))

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

(define unify
  (lambda (v w s)
    (let ((v (walk v s))
          (w (walk w s)))
      (cond
        ((eq? v w) s)
        ((var? v) (if (var? w) (ext-s-ordered v w s) (ext-s v w s)))
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

'(define ext-s-ordered 
  (lambda (v w s) 
    (cond 
      ((string>? (var-id v) (var-id w)) (ext-s v w s)) 
      (else (ext-s w v s)))))

(define ext-s-ordered ext-s)

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

(define count-cons 0)


