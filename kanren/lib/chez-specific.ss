; KANREN prelude specific to Chez-Scheme
;
; $Id$

;(load "plshared.ss")

(define chez-error error)
(define error
  (lambda (msg . args)
    (chez-error 'runtime-error "~a~%" (cons msg args))))
(define errorf chez-error)

; like cout << arguments << args
; where argument can be any Scheme object. If it's a procedure
; (without args) it's executed rather than printed (like newline)

(define (cout . args)
  (for-each (lambda (x)
              (if (procedure? x) (x) (display x)))
            args))

;(define cerr cout)
(define (cerr . args)
  (for-each (lambda (x)
              (if (procedure? x) (x (console-output-port))
		(display x (console-output-port))))
            args))

(define nl (string #\newline))


; Support for let*-values form: SRFI-11

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
			; Only feature-identifiers srfi-0, chez, and
			; petite-chez are assumed predefined.
			; This
			; syntax-rule may NOT use an let-syntax.
(define-syntax cond-expand
  (syntax-rules (else chez petite-chez srfi-0 and or not)
    ((cond-expand)
      (error "Unfulfilled cond-expand"))
    ((cond-expand (else . cmd-or-defs*))
      (begin . cmd-or-defs*))
    ((cond-expand "feature-id" chez kt kf) kt)
    ((cond-expand "feature-id" petite-chez kt kf) kt)
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


(print-gensym #f)

;(load "plprelims.ss")

;(load "expand-only.ss")

;quasiquote has been coded by Oscar Waddell.
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
