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


;   (lambda (v s) (walk-strong v 
;     (reify-fresh
;       (reify-nonfresh v s))))

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
; Let -->w* be a transitive closure of -->w, and let -->w! be a fixpoint
; of -->w. Ditto for -->s* and -->s!
; For acyclic substitutions, the fixpoints exist.
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



; given a variable x and a subst s and the continuation k,
; compute x', the strong normal form of x, and the list of
; equivalence classes VEQ, and pass them to k.
;  x -->s! x'
;  VEQ ::= ( (u x1 x2 ...) ... )
; where u is free, x1 -->w! u ...
; and for each xi there is t such that x -->s* t and xi \in FV(t)
;
; Note that (u x1 x2 ...) is not the whole equivalence class represented
; by u in s, but only a part of it -- the part that is `relevant'
; to the reduction of the variable x. That is, the class contains only
; those variables that are encountered during the reduction of x.
; For backwards compatibility, we impose an ordering constrint on VEQ:
; the classes in VEQ are reversely ordered so that corresponding variables are
; encountered during the depth-first left-to-right reduction strategy
; for x.

(define reify-nonfresh*
  (lambda (x s k)
    (let loop ((x x) (vars-encountered '()) (veq '()) (k k))
      (cond
	((pair? x)			; drop vars-encountered, x is not free
	  (loop (car x) '() veq
	    (lambda (x1 veq1)
	      (loop (cdr x) '() veq1
		(lambda (x2 veq2) (k (cons x1 x2) veq2))))))
	((not (var? x)) ; x is an atom -- normal form
	 (k x veq))
	((assq x s) =>			; x is bound in s, reduce
	  (lambda (b)
	    (loop (rhs b) (cons x vars-encountered) veq k)))
	(else				; x is free: normal form
	  (k x (adds x vars-encountered veq)))))))

; adds x xs l
;  where l is an associative list
; prepends an association (x . xs) to l if x does not occur in l
; If l contains an association (x . xs1), return l with an association
; (cons x (merge xs xs1)), preserving the order of the associations in l

(define adds
  (lambda (x xs l)
    (cond
      ((assq x l) =>
	(lambda (b)
	  (repl b (cons x (merge xs (cdr b))) l)))
      (else (cons (cons x xs) l)))))

; merge two lists
(define merge
  (lambda (l1 l2)
    (cond
      ((null? l1) l2)
      ((memq (car l1) l2) (merge (cdr l1) l2))
      (else (cons (car l1) (merge (cdr l1) l2))))))

; replace the element b with b1 in l, preserving the order
(define repl
  (lambda (b b1 l)
    (if (eq? b (car l)) (cons b1 (cdr l))
      (cons (car l) (repl b b1 (cdr l))))))

; Remove the element e from the list preserving the order
(define rem
  (lambda (e l)
    (cond
      ((null? l) l)
      ((eq? e (car l)) (cdr l))
      (else (cons (car l) (rem e (cdr l)))))))


; Given ((x1 x2 ...) ...) compute the substitution
; {x1 -> pn ...}
; where pn is the indexed name of the pretty representative of (x1 x2 ...)
; Different (in the sense of eq?) logical variables may have the same name.
; So, the names of their pretty-representatives might turn out the same.
; thus we maintain a counter (started at 0) for each equivalent name 
; and add the counter to the name of the selected pretty representatives.

(define varname-beautifier
  (let
    ((find-pretty-rep-name
       (lambda (lst)
	 (let loop ((e (var-id (car lst))) (lst (cdr lst)))
	   (if (null? lst) e
	     (let ((e1 (var-id (car lst))))
	       (loop (if (string<? e1 e) e1 e) (cdr lst))))))))
  (lambda (veq)
    (let ((pns (map (lambda (eqc)
		      (cons (find-pretty-rep-name eqc) (car eqc))) veq)))
      (let outer ((pns pns) (acc empty-s))
	(if (null? pns) acc
	  (let* ((h (car pns)) (pns (cdr pns)))
	    (cond
	      ((assoc (car h) pns)  => ; name of h is not unique
		(lambda (b)
		  (let inner ((index 1) (b b) (pns pns) 
			      (acc (ext-s (cdr h) (reify-id (car h) 0) acc)))
		    (if (not b) (outer pns acc)
		      (let ((pns (rem b pns)))
			(inner (+ 1 index) (assoc (car b) pns) pns
			  (ext-s (cdr b) (reify-id (car b) index) acc)))))))
	      (else
		(outer pns (ext-s (cdr h) (reify-id (car h) 0) acc)))))))))))


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

(define reify walk-strong)

; In teh future, reify-nonfresh may take the name of the user-supplied
; beautifier
(define reify-nonfresh
  (lambda (x s)
    (reify-nonfresh* x s
      (lambda (r veq)
	;(pretty-print veq)
	(let ((bveq (varname-beautifier (reverse veq))))
	  (walk-strong r bveq))))))



;;;; reify

;;; Thoughts: reify should be the composition of
;;; reify/non-fresh with reify/fresh.  reify/non-fresh
;;; is also known as reify-nonfresh.  reify/fresh was also
;;; knows as reify.

;;;;; This is the code of reify

'(define reify-fresh
  (lambda (v)
    (r-f v '() empty-s
      (lambda (p* s) (reify-nonfresh v s)))))

(define reify-fresh (lambda (v) v))

'(define r-f           ;;;;; NEW
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

'(define index
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

'(define reify-test
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

(define count-cons 0)


