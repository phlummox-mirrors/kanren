'(define-syntax def-syntax
  (syntax-rules ()
    ((_ (name . lhs) rhs)
     (define-syntax name
       (syntax-rules ()
         ((_ . lhs) rhs))))))

(print-gensym #f)

(define-syntax lambda@
  (syntax-rules ()
    ((_ () body0 body1 ...) (lambda () body0 body1 ...))
    ((_ (formal) body0 body1 ...) (lambda (formal) body0 body1 ...))
    ((_ (formal0 formal1 formal2 ...) body0 body1 ...)
     (lambda (formal0)
       (lambda@ (formal1 formal2 ...) body0 body1 ...)))))

(define-syntax @  
  (syntax-rules ()
    ((_ rator) (rator))
    ((_ rator rand) (rator rand))
    ((_ rator rand0 rand1 rand2 ...) (@ (rator rand0) rand1 rand2 ...))))


;   (lambda (v s) (walk-strong v 
;     (reify-fresh
;       (reify-nonfresh v s))))

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (cout "Testing " title nl)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

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


(define ext-s
  (lambda (x v s)
    (cons (cons x v) s)))


; Some terminology related to variables and substitutions
;
; A substitution subst is a finite map { xi -> ti ... }
; where xi is a logic variable.
; ti is a term ::= variable | Scheme-atom | (cons term term)
; A variable x is free in the substitution subst if x \not\in Dom(subst)
;
; Given a term t and a substitution subst, a weak reduction
;   t -->w  t'
; is defined as
;   x -->w subst[x]  if x is a var and x \in Dom(subst)
;   t -->w t otherwise
;
; A strong reduction
;   t -->s t' 
; is defined as
;   x -->s subst[x]  if x is a var and x \in Dom(subst)
;   (cons t1 t2) -->s (cons t1' t2')
;          where t1 -->s t1'  t2 -->s t2'
;   t -->s t otherwise
;
; The notion of reduction can be extended to substitutions themselves:
;   { xi -> ti ...} -->w { xi -> ti' } where ti -> ti'
; ditto for -->s.
; Let -->w* be a reflexive transitive closure of -->w, and 
; let -->w! be a fixpoint of -->w. Ditto for -->s* and -->s!
; For acyclic substitutions, the fixpoints exist.
;
; The confluence of the reduction is guaranteed by the particular form
; of the substitution produced by the unifier (the unifier always
; deals with the weak normal forms of submitted terms).
;
; The similarity of the weak normalization with call-by-value and
; the strong normalization with the applicative-order reduction should
; be apparent.
;
; Variable x is called ultimately free if
; x -->w! x' and x' is free in the subtutution in question.
;
; Two ultimately free variables x and y belong to the same equivalence class
; if x -->w! u and y -->w! u
; The (free) variable u is the natural class representative.
; For the purpose of presentation, one may wish for a better representative.
; Given a set of equivalent variables xi -->w! u,
; a pretty representative is a member z of that set such that the
; string name of 'z' is lexicographically smaller than the string names 
; of the other variables in that set.
;
; If a variable x is ultimately free in subst and x ->w! u, 
; then there is a binding
; v1 -> v2 where both v1 and v2 are variables and v2 ->w! u. Furthermore,
; the set of all such v1 union {u} is the whole equivalence class of x.
; That property is guaranteed by the unifier. That property lets us
; build an inverse index to find the equivalence class of x.


; Compute the list of (free) variables of a term t, in the depth-first 
; term-traversal order.
(define free-vars
  (lambda (t)
    (reverse (fv t '()))))

(define fv
  (lambda (t acc)
    (cond
      ((pair? t) (fv (cdr t) (fv (car t) acc)))
      ((var? t) (if (memq t acc) acc (cons t acc)))
      (else acc))))


; Given a term v and a subst s, return v', the weak normal form of v:
; v -->w! v' with respect to s
(define walk
  (lambda (v s)
    (cond
      ((not (var? v)) v)
      ((assq v s) =>
	(lambda (b) (walk (cdr b) s)))
      (else v))))

; Given a term v and a subst s, return v', the strong normal form of v:
; v -->s! v' with respect to s
(define walk-strong
  (lambda (v s)
    (cond
      ((pair? v)
	(cons (walk-strong (car v) s) (walk-strong (cdr v) s)))
      ((not (var? v)) v)
      ((assq v s) =>
	(lambda (b) (walk-strong (cdr b) s)))
      (else v))))

(define reify
  (lambda (v s)
    (let ((t (walk-strong v s)))
      (let ((fv (free-vars t)))
	(walk-strong t (find-pretty-names fv 0))))))

; Given the list of free variables and the initial index,
; create a subst { v -> pretty-name-indexed }
; where pretty-name-indexed is the combination of "x" (indicating
; a free variable) and the index ".0", ".1", etc.
(define find-pretty-names
  (lambda (fv index)
    (if (null? fv) empty-s
      (ext-s (car fv) (reify-id index)
	(find-pretty-names (cdr fv) (+ 1 index))))))


(define reify-id      ;;;;; NEW
  (lambda (index)
    (string->symbol
      (string-append
        "$x_{"
        (number->string index)
        "}$"))))

(define reify-id      ;;;; NEW
  (lambda (index)
    (string->symbol
      (string-append "x" (string #\.) (number->string index)))))


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
      ((occurs? v w) #f)
      (else (ext-s v w s)))))

(define occurs?
  (lambda (x v s)
    (cond
      ((var? v) (eq? v x))
      ((pair? v)
       (or (occurs? x (walk (car v) s) s)
           (occurs? x (walk (cdr v) s) s)))
      (else #f))))

(define count-cons 0)


