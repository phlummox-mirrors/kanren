(def-syntax (query (fk subst id ...) ant expr expr* ...)
  (exists (id ...)
    (@ ant (lambda@ (fk subst) expr expr* ...) (lambda () '()) empty-subst)))

(def-syntax (project (id ...) ant)
  (lambda@ (sk fk subst)
    (let ([id (subst-in id subst)] ...) (@ ant sk fk subst))))

(def-syntax (== t u)
  (lambda@ (sk fk subst)
    (let ([subst (unify t u subst)]) (if subst (@ sk fk subst) (fk)))))

(def-syntax (ef-maker name fk^ subst^ fk subst fk$ subst$)
  (def-syntax (name a b c)
    (lambda@ (sk fk^ subst^)
      (@ a (lambda@ (fk subst) (@ b sk fk$ subst$)) (lambda () (@ c sk fk^ subst^)) subst^))))

(ef-maker ef fk^ subst^ fk subst fk subst)
(ef-maker ef/only fk^ subst^ fk subst fk^ subst)
(ef-maker ef/forget fk^ subst^ fk subst fk subst^)
(ef-maker ef/only/forget fk^ subst^ fk subst fk^ subst^)

(define-syntax all
  (syntax-rules ()
    [(_) (lambda@ (sk fk subst) (@ sk fk subst))]
    [(_ ant) ant]
    [(_ ant ant* ...) (ef ant (all ant* ...) (any))]))

(define-syntax any
  (syntax-rules ()
    [(_) (lambda@ (sk fk subst) (fk))]
    [(_ ant) ant]
    [(_ ant ant* ...) (ef ant (all) (any ant* ...))]))

(def-syntax (exists (id ...) ant) (let ([id (logical-variable 'id)] ...) ant))
(def-syntax (eigen (id ...) ant) (let ([id (gensym)] ...) ant))
(def-syntax (predicate expr) (if expr (all) (any)))
(def-syntax (instantiated t) (project (t) (predicate (not (var? t)))))
(def-syntax (fails ant) (ef/only/forget ant (any) (all)))
(def-syntax (only/forget ant) (ef/only/forget ant (all) (any)))
(def-syntax (only ant) (ef/only ant (all) (any)))
(def-syntax (forget ant) (ef/forget ant (all) (any)))
(def-syntax (all! ant ...) (only (all ant ...)))
(def-syntax (all!! ant ...) (only (all (only ant) ...)))
(def-syntax (when-only ant ant* ...) (all (only ant) ant* ...))

(def-syntax (trace-vars title (id ...))
  (project (id ...)
    (begin (for-each (lambda (id_ t) (printf "~s ~a ~s~n" id_ title t))
	     '(id ...) (concretize `(,id ...)))
      (newline)
      (all))))