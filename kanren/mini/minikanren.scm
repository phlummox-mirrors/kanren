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


(define-syntax relation
  (syntax-rules (to-show)
    [(_ (ex-id* ...) (to-show Term* ...) ant)
     (relation-aux (ex-id* ...) () (Term* ...) (Term* ...) ant)]))

(define-syntax relation-aux
  (syntax-rules ()
    [(_ ex-ids (var* ...) () (Term* ...) ant)
     (lambda (var* ...)
       (exists ex-ids
	 (ef/only (all!! (== var* Term*) ...) ant (any))))]
    [(_ ex-ids (var* ...) (Term Term* ...) Terms ant)
     (relation-aux ex-ids (var* ... g) (Term* ...) Terms ant)]))

(def-syntax (fact (ex-id* ...) Term* ...)
  (relation (ex-id* ...) (to-show Term* ...) (all)))

(def-syntax (extend-relation (arity-id* ...) rel* ...)
  (construct-relation any (arity-id* ...) () rel* ...))

(define-syntax construct-relation
  (syntax-rules ()
    [(_ any (arity-id* ...) ([g rel] ...))
     (let ([g rel] ...)
       (lambda (arity-id* ...)
         (any (g arity-id* ...) ...)))]
    [(_ any (arity-id* ...) (let-pair ...) rel rel* ...)
     (construct-relation any (arity-id* ...) (let-pair ... [g rel]) rel* ...)]))

(def-syntax (intersect-relation (arity-id* ...) rel* ...)
  (construct-relation all (arity-id* ...) () rel* ...))
  
