; KANREN prelude specific to Bigloo-Scheme
;
; $Id$

(define bigloo-error error)
(define error
  (lambda (msg . args)
    (bigloo-error "myerror" msg args)))
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
              (if (procedure? x) (x (current-error-port)) (display x (current-error-port))))
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

; These are present in Chez
(define (remv el lst)
  (let loop ((lst lst))
    (cond
      ((null? lst) lst)
      ((eqv? el (car lst)) (loop (cdr lst)))
      (else (cons (car lst) (loop (cdr lst)))))))
(define pretty-print pp)
(define (time v) v)

(define (printf . args) (apply print args))

; (define (OS:time::double)
;   (pragma::double "time(0)"))

; (define (statistics)
;   (vector
;     #f
;     (*fl 1000.0 (OS:time)) ; CPU-time
;     ))
