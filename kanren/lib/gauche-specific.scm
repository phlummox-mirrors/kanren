; KANREN prelude specific to Gauche-Scheme
;
; $Id$

(use srfi-11)
(use srfi-9)
(use gauche.time)

(define errorf error)
(define (printf fmt . args) (apply format #t fmt args))
(define pretty-print print)

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


