; The send-more-money puzzle
;    S E N D
;    M O R E
; ----------
;  M O N E Y
;
; Different letters stand for different digits, and neither S nor M
; are zeros.
;
; We use the miniKanren arithmetics
; $Id$


; Pure rembere predicate (called reme): the choice function

; choose an element e from the list lst
;  (choose lst e rest) holds
; if e \in lst and rest = lst \ {e}

(define appendo
  (lambda (l1 l2 l3)
    (condi
      ((== l1 '()) (== l2 l3))
      (else 
        (fresh (x l11 l31)
          (== l1 (cons x l11))
          (== l3 (cons x l31))
          (appendo l11 l2 l31))))))


; common-prefix l l1 l2
; holds iff l is a prefix of both l1 and l2.
(define common-prefix
   (lambda (l l1 l2)
     (condi
        ((== l '()))
        (else
          (fresh (x l* l1* l2*)
            (== l  (cons x l*))
            (== l1 (cons x l1*))
            (== l2 (cons x l2*))
            (common-prefix l* l1* l2*))))))

; A pure rembere: l = lo U {x}
(define reme
  (lambda (x l lo)
    (fresh (l1 l2)
      (alli
      (common-prefix l1 l lo)
      (appendo l1 (cons x l2) l)
      (appendo l1 l2 lo)))))


; (run 6 (q) (fresh (e rest) (reme e '(1 2 3) rest) (== q (list e rest))))
; (run 6 (q) (fresh (e rest) (reme e rest '(1 2 3)) (== q (list e rest))))

(define (solve-puzzle q)
  (let ((all-digits (map build '(0 1 2 3 4 5 6 7 8 9)))
	(ten (build 10))
	(zero (build 0)))

  ; relate the number and the list of digits
  (define (make-number digits n)
    (let loop ((digits digits) (acc zero))
      (condi
	((== digits '()) (== n acc))
	(else
	  (fresh (d rest acc1 acc2)
	    (alli
	      (== digits (cons d rest))
	      (xo acc ten acc1)
	      (+o acc1 d acc2)
	      (loop rest acc2)))))))
   
    ; choose a subset from all-digits
    (define (choose-digits digits all-digits remained-digits)
      (condi
	((== digits '()) (== all-digits remained-digits))
	(else 
	  (fresh (d rest set1)
	    (alli
	      (== digits (cons d rest))
	      (reme d all-digits set1)
	      (choose-digits rest set1 remained-digits))))))

    ; d1 + d2 + ci = do + 10*co
    ; ci and co can only be 1 and 0
    (define (add-carry ci d1 d2 do co)
      (fresh (d11 dr)
	(conde ((== ci zero)) ((== ci '(1))))
	(+o ci d1 d11)
	(+o d11 d2 dr)
	(conde
	  ((== dr do) (== co zero))
	  ((+o do ten dr) (== co '(1))))))

    (fresh (s e n d m o r y send more money c1 c2 c3 rd1 rd2 rd3)
      (alli
      (choose-digits (list m s o) all-digits rd1)
      (poso s)
      (poso m)
      (add-carry c3   s m o m)
      (choose-digits (list e n) rd1 rd2)
      (add-carry c2   e o n c3)
      (choose-digits (list r d y) rd2 rd3)
      (add-carry zero d e y c1)
      (add-carry c1   n r e c2)

      ; verify
      (make-number (list s e n d) send)
      (make-number (list m o r e) more)
      (make-number (list m o n e y) money)
      (+o send more money)
      (project (send more money)
	(== q (list (trans send) (trans more) (trans money))))))))

; (run 1 (q) (solve-puzzle q))
; > (run 2 (q) (solve-puzzle q))
; ((9567 1085 10652))
