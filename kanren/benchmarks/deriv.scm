;; http://www.sics.se/quintus/deriv.pl

; $Id$

(define d
  (extend-relation (a1 a2 a3)
    (relation (u v x du dv)
      (to-show `(+ ,u ,v) x `(+ ,du ,dv))
      (all!!
	(d u x du)
	(d v x dv)))
    (relation (u v x du dv)
      (to-show `(- ,u ,v) x `(- ,du ,dv))
      (all!!
	(d u x du)
	(d v x dv)))
    (relation (u v x du dv)
      (to-show `(* ,u ,v) x `(+ (* ,du ,v) (* ,u ,dv)))
      (all!!
	(d u x du)
	(d v x dv)))
    (relation (u v x du dv)
      (to-show `(/ ,u ,v) x `(/ (- (* ,du ,v) (* ,u ,dv)) (^ ,v 2)))
      (all!!
	(d u x du)
	(d v x dv)))
    (relation (u n x du n1)
      (to-show `(^ ,u ,n) x `(* ,du  (* ,n (^ ,u ,n1))))
      (all!!
	(project (n)
	  (== n1 (- n 1)))
	(d u x du)))
    (relation (u (once x) du)
      (to-show `(minus ,u) x `(minus ,du))
      (d u x du))
    (relation (u (once x) du)
      (to-show `(e ,u) x `(* (e ,u) ,du))
      (d u x du))
    (relation (u (once x) du)
      (to-show `(log ,u) x `(/ ,du ,u))
      (d u x du))
    (fact (x) x x 1)
    (fact () _ _ 0)))

(define ops8
  (relation (head-let e)
    (d '(* (+ x 1) (* (+ (^ x 2) 2) (+ (^ x 3) 3))) 'x e)))

(define divide10
  (relation (head-let e)
    (d '(/ (/ (/ (/ (/ (/ (/ (/ (/ x x) x) x) x) x) x) x) x) x) 'x e)))

(define log10
  (relation (head-let e)
    (d '(log(log(log(log(log(log(log(log(log(log x)))))))))) 'x e)))

(define times10
  (relation (head-let e)
    (d '(* (* (* (* (* (* (* (* (* x x) x) x) x) x) x) x) x) x) 'x e)))

(define bench
  (lambda ()
    (pretty-print
      (time
	(solve 1 (e1 e2 e3 e4)
	  (all!! (ops8 e1) (divide10 e2) (log10 e3) (times10 e4)))))))
