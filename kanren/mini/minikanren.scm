(def-syntax (exists (id ...) ant ant* ...)
  (let ([id (logical-variable 'id)] ...) (all ant ant* ...)))

(def-syntax (eigen (id ...) ant ant* ...)
  (let ([id (gensym)] ...) (all ant ant* ...)))

(def-syntax (run-raw (id ...) ant fk subst succeed-expr fail-expr)
  (exists (id ...)
    (@ ant (lambda@ (fk subst) succeed-expr) (lambda () fail-expr) empty-subst)))

(def-syntax (project-host (id ...) subst expr)
  (let ([id (subst-in id subst)] ...) expr))

(def-syntax (run (id ...) ant fk subst succeed-expr fail-expr)
  (run-raw (id ...) ant fk subst
    (project-host (id ...) subst
      (let ([c* (concretize `(,id ...))])
	(let*-values ([(id c*) (values (car c*) (cdr c*))] ...)
	  succeed-expr)))
    fail-expr))
    
(def-syntax (project (id ...) ant ant* ...)
  (lambda@ (sk fk subst)
    (project-host (id ...) subst (@ (all ant ant* ...) sk fk subst))))

(def-syntax (== t u)
  (lambda@ (sk fk subst)
    (let ([subst (unify t u subst)]) (if subst (@ sk fk subst) (fk)))))

(def-syntax (ef-maker name fk^ subst^ fk subst fk$ subst$)
  (def-syntax (name a b c)
    (lambda@ (sk fk^ subst^)
      (@ a (lambda@ (fk subst) (@ b sk fk$ subst$)) (lambda () (@ c sk fk^ subst^)) subst^))))

(def-syntax (succeed) (lambda@ (sk fk subst) (@ sk fk subst)))
(def-syntax (fail) (lambda@ (sk fk subst) (fk)))

(define-syntax all
  (syntax-rules ()
    [(_) (succeed)]
    [(_ ant) ant]
    [(_ ant ant* ...) (ef ant (all ant* ...) (fail))]))

(define-syntax any
  (syntax-rules ()
    [(_) (fail)]
    [(_ ant) ant]
    [(_ ant ant* ...) (ef ant (succeed) (any ant* ...))]))

(ef-maker ef fk^ subst^ fk subst fk subst)
(ef-maker ef/only fk^ subst^ fk subst fk^ subst)
(ef-maker ef/forget fk^ subst^ fk subst fk subst^)
(ef-maker ef/only/forget fk^ subst^ fk subst fk^ subst^)

(def-syntax (predicate expr) (if expr (succeed) (fail)))
(def-syntax (fails ant) (ef/only/forget ant (fail) (succeed)))
(def-syntax (only/forget ant) (ef/only/forget ant (succeed) (fail)))
(def-syntax (only ant) (ef/only ant (succeed) (fail)))
(def-syntax (forget ant) (ef/forget ant (succeed) (fail)))
(def-syntax (all! ant ...) (only (all ant ...)))
(def-syntax (all!! ant ...) (only (all (only ant) ...)))
(def-syntax (when-only ant ant* ...) (all (only ant) ant* ...))

(def-syntax (trace-vars title (id ...))
  (project (id ...)
    (begin (for-each (lambda (id_ t) (printf "~s ~a ~s~n" id_ title t))
	     '(id ...) (concretize `(,id ...)))
      (newline)
      (succeed))))

(def-syntax (run-once (id ...) ant succeed-expr)
  (run (id ...) ant fk subst succeed-expr #f))

(def-syntax (run-list (id ...) ant succeed-item-expr)
  (run (id ...) ant fk subst (cons succeed-item-expr (fk)) '()))

(def-syntax (run-stream (id ...) ant succeed-item-expr)
  (run (id ...) ant fk subst (cons succeed-item-expr fk) '()))

(def-syntax (answers (id ...) ant)
  (run (id ...) (all ant (trace-vars "::" (id ...))) fk subst (fk) #f))

(def-syntax (answer (id ...) ant)
  (run-once (id ...) (all ant (trace-vars "::" (id ...))) (void)))

(def-syntax (answer* max-num (id ...) ant)
  (let ([n max-num])
    (if (> n -1)
        (let loop ([ans (run (id ...) (all ant (trace-vars "::" (id ...))) fk subst fk #f)]
                   [n n])
          (if (not (or (zero? n) (not ans)))
              (loop (ans) (sub1 n))
              (if (not ans) #f #t))))))


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


