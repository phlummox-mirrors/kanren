; KANREN prelude specific to SCM-Scheme
;
; $Id$

(define gensym gentemp)

(define errorf error)

; like cout << arguments << args
; where argument can be any Scheme object. If it's a procedure
; (without args) it's executed rather than printed (like newline)

(define (cout . args)
  (for-each (lambda (x)
              (if (procedure? x) (x) (display x)))
    args))

(define (cerr . args)
  (for-each (lambda (x)
              (if (procedure? x) (x (current-error-port))
		(display x (current-error-port))))
    args))

(define nl (string #\newline))

; Support for let*-values form: SRFI-11

(require 'values)

(define-syntax let*-values
  (syntax-rules ()
    ((let*-values () . bodies) (begin . bodies))
    ((let*-values (((var) initializer) . rest) . bodies)
      (let ((var initializer))		; a single var optimization
	(let*-values rest . bodies)))
    ((let*-values ((vars initializer) . rest) . bodies)
      (call-with-values (lambda () initializer) ; the most generic case
	(lambda vars (let*-values rest . bodies))))))



			; Implementation of SRFI-0
			; Only feature-identifiers srfi-0 and scm
			; assumed predefined. See below why this
			; syntax-rule may NOT use an let-syntax.
(define-syntax cond-expand
  (syntax-rules (else scm srfi-0 and or not)
    ((cond-expand)
      (error "Unfulfilled cond-expand"))
    ((cond-expand (else . cmd-or-defs*))
      (begin . cmd-or-defs*))
    ((cond-expand "feature-id" scm kt kf) kt)
    ((cond-expand "feature-id" srfi-0 kt kf) kt)
    ((cond-expand "feature-id" x kt kf) kf)
    ((cond-expand "satisfies?" (and) kt kf) kt)
    ((cond-expand "satisfies?" (and clause) kt kf)
      (cond-expand "satisfies?" clause kt kf))
    ((cond-expand "satisfies?" (and clause . rest) kt kf)
      (cond-expand "satisfies?" clause
	(cond-expand "satisfies?" (and . rest) kt kf) kf))
    ((cond-expand "satisfies?" (or) kt kf) kf)
    ((cond-expand "satisfies?" (or clause) kt kf)
      (cond-expand "satisfies?" clause kt kf))
    ((cond-expand "satisfies?" (or clause . rest) kt kf)
      (cond-expand "satisfies?" clause kt
	(cond-expand "satisfies?" (or . rest) kt kf)))
    ((cond-expand "satisfies?" (not clause) kt kf)
      (cond-expand "satisfies?" clause kf kt))
    ((cond-expand "satisfies?" x kt kf)
      (cond-expand "feature-id" x kt kf))

    ((cond-expand (feature-req . cmd-or-defs*) . rest-clauses)
      (cond-expand "satisfies?" feature-req
	  (begin . cmd-or-defs*)
	  (cond-expand . rest-clauses)))))

(require 'record)
; The following is enough for KANREN. Or just require srfi-9
; if provided
(define-syntax define-record-type
  (syntax-rules ()
    ((_ record-name (constr field ...) pred (field-name getter) ...)
      (begin
	(define rtd (make-record-type
		      (symbol->string 'record-name)
		      (list 'field ...)))
	(define constr (record-constructor rtd (list 'field ...)))
	(define pred   (record-predicate rtd))
	(define getter (record-accessor rtd 'field-name))
	...
	))))

	  
(require 'pretty-print)

; These are present in Chez
(define (remq el lst)
  (let loop ((lst lst))
    (cond
      ((null? lst) lst)
      ((eq? el (car lst)) (loop (cdr lst)))
      (else (cons (car lst) (loop (cdr lst)))))))
(define (time v) v)
(define printf cout)

