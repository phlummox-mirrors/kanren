;;; Our attempt at adding exponentiation

; Pure, declarative, and constructive binary arithmetics
;
; aka: Addition, Multiplication, Division as always terminating,
; pure and declarative relations that can be used in any mode whatsoever.
; The relations define arithmetics over binary (base-2) integral numerals
; of arbitrary size.
;
; aka: division as relation.
; The function divo below is a KANREN relation between four binary numerals
; n, m, q, and r such that the following holds
;	exists r. 0<=r<m, n = q*m + r
;
; See pure-arithm.scm in this directory for Peano arithmetics.

; The arithmetic relations possess interesting properties.
; For example, given the relation (divo N M Q R) which holds
; iff N = M*Q + R and 0<=R<M, we can try:
;   -- (divo 1 0 Q _). It fails and does not try to enumerate
;      all natural numbers.
;   -- (divo 5 M 1 _). It finds all such M that divide (perhaps unevenly)
;      5 with the quotient of 1. The answer is the set (5 4 3).
; Again, (divo 5 M 7 _) simply fails and does not loop forever.
; We can use the (*o X Y Z) relation either to multiply two numbers
; X and Y -- or to find all factorizations of Z. See the test below.
; Furthermore, we can try to evaluate (++o X 1 Y) and get the stream
; of answers, among which is ((0 *anon.0 . *anon.1) (1 *anon.0 . *anon.1))
; which essentially says that 2*x and 2*x +1 are successors, for all x>0!
;
; Such relations are easy to implement in an impure system such as Prolog,
; with the help of a predicate 'var'. The latter can tell if its argument
; is an uninstantiated variable. However, 'var' is impure. The present
; file shows the implementation of arithmetic relations in a _pure_
; logic system.
; The present approach places the correct upper bounds on the
; generated numbers to make sure the search process will terminate.
; Therefore, our arithmetic relations are not only sound
; (e.g., if (*o X Y Z) holds then it is indeed X*Y=Z) but also
; complete (if X*Y=Z is true then (*o X Y Z) holds) and
; refutationally complete (if X*Y=Z is false then (*o X Y Z) fails,
; in finite time).
;
; The numerals are represented in the binary little-endian
; (least-significant bit first) notation. The higher-order bit must be 1.
; ()  represents 0
; (1) represents 1
; (0 1) represents 2
; (1 1) represents 3
; (0 0 1) represents 4
; etc.
;
; This code has been translated to Prolog. The Prolog version has
; termination proofs.
;
; $Id$

; Auxiliary functions to build and show binary numerals
;

(load "sempublic.ss")

(define tex #f)

(define-syntax test-check
  (syntax-rules ()
    [(_ title tested-expression expected-result)
     (test-check title tested-expression expected-result #t)]
    [(_ title tested-expression expected-result show-flag)
     (begin
       (let* ([expected expected-result]
              [produced tested-expression])
         (if (equal? expected produced)
             (if tex
                 (if show-flag
                     (generate-tex 'tested-expression produced)
                     (void))
                 (cout title " works!" nl))
             (errorf 'test-check
                     "Failed ~s: ~a~%Expected: ~a~%Computed: ~a~%"
                     title 'tested-expression expected produced))))]))

(define generate-tex
  (lambda (exp result)
    (printf "\\twocol{\\smallskip~n\\i1 \\begin{schemebox}~n")
    (pretty-print exp)
    (printf "\\end{schemebox}}~n{\\begin{schemeresponsebox}~n")
    (pretty-print (tex-data result))
    (printf "\\end{schemeresponsebox}}\n\n")))

(define tex-data
  (lambda (x)
    (cond
      [(pair? x) (cons (tex-data (car x)) (tex-data (cdr x)))]
      [(symbol? x)
       (cond
         [(var-symbol? x) (translate-to-tex x)]
         [else x])]
      [else x])))

(define var-symbol?
  (lambda (x)
    (memq #\. (string->list (symbol->string x)))))

(define reify-id-tex
  (lambda (id index)
    (string->symbol
      (string-append
        (symbol->string id)
        "$_{_{"
        (number->string index)
        "}}$"))))

(define translate-to-tex
  (lambda (x)
    (reify-id-tex
      (string->symbol (list->string (prefix-id (string->list (symbol->string x)))))
      (string->number (list->string (cdr (var-symbol? x)))))))

(define prefix-id
  (lambda (x)
    (cond
     [(eq? (car x) #\.) '()]
     [else (cons (car x) (prefix-id (cdr x)))])))

(define-syntax succ
  (syntax-rules ()
    [(_) succeed]
    [(_ e e* ...)
     (lambda@ (sk fk s)
       (begin
         e
         (@ (succ e* ...) sk fk s)))]))
       
(define-syntax fa
  (syntax-rules ()
    [(_) fail]
    [(_ e e* ...)
     (lambda@ (sk fk s)
       (begin
         e
         (@ (fa e* ...) sk fk s)))]))

(define build
  (lambda (n)
    (cond
      [(zero? n) '()]
      [else (cons (if (even? n) 0 1) (build (quotient n 2)))])))

(define trans
  (lambda (n)
    (cond
      [(null? n) 0]
      [else (+ (car n) (* 2 (trans (cdr n))))])))

; Not a zero
(define pos
  (lambda (n)
    (fresh (_ __)
      (== `(,_ . ,__) n))))

; At least two
(define gt1
  (lambda (n)
    (fresh (_ __ ___)
      (== `(,_ ,__ . ,___) n))))

(define half-adder
  (lambda (x y r c-out)
    (all
      (bit-xor x y r)
      (bit-and x y c-out))))

(define full-adder
  (lambda (c-in x y r c-out)
    (fresh (w xy wz)
      (half-adder x y w xy)
      (half-adder w c-in r wz)
      (bit-or xy wz c-out))))

(define bit-and
  (lambda (x y r)
    (cond@
      ((all (== 0 x) (== 0 y)) (== 0 r))
      ((all (== 1 x) (== 0 y)) (== 0 r))
      ((all (== 0 x) (== 1 y)) (== 0 r))      
      ((all (== 1 x) (== 1 y)) (== 1 r))
      (else fail))))

(define bit-or
  (lambda (x y r)
    (cond@
      ((all (== 0 x) (== 0 y)) (== 0 r))
      ((all (== 1 x) (== 0 y)) (== 1 r))
      ((all (== 0 x) (== 1 y)) (== 1 r))      
      ((all (== 1 x) (== 1 y)) (== 1 r))
      (else fail))))

(define bit-xor
  (lambda (x y r)
    (cond@
      ((all (== 0 x) (== 0 y)) (== 0 r))
      ((all (== 1 x) (== 0 y)) (== 1 r))
      ((all (== 0 x) (== 1 y)) (== 1 r))      
      ((all (== 1 x) (== 1 y)) (== 0 r))
      (else fail))))


; adder: c-in m n k
; holds if c-in + m + n = k
; where m, n, and k are binary numerals
; and c-in is either 0 or 1

(define adder
  (lambda (c-in n m k)
    (condi
      [(== 0 c-in) (== '() m) (== '() n) (== '() k)]
      [(== 0 c-in) (== '() m) (pos n) (== n k)]      
      [(== 0 c-in) (== '() n) (pos m) (== m k)]
      [(== 1 c-in) (== '() m) (== '() n) (== '(1) k)]      
      [(== 1 c-in) (== '() m) (pos n) (adder 0 n '(1) k)]
      [(== 1 c-in) (== '() n) (pos m) (adder 0 '(1) m k)]
      [(== '(1) n) (== '(1) m) (gen-adder c-in n m k)]
      [(== '(1) n) (gt1 m) (gen-adder c-in n m k)]
      [(== '(1) m) (gt1 n) (gen-adder c-in n m k)]
      [(gt1 n) (gt1 m) (gen-adder c-in n m k)]
      [else fail])))

(define gen-adder
  (lambda (c-in n m k)
    (fresh (nb nr mb mr kb kr)
      (== `(,nb . ,nr) n)
      (== `(,mb . ,mr) m)
      (== `(,kb . ,kr) k)
      (fresh (c-out)
        (alli
          (full-adder c-in nb mb kb c-out)
          (adder c-out nr mr kr))))))

; a + b = c
(define +o
  (lambda (n m k)
    (adder 0 n m k)))

; a - b = c
(define -o
  (lambda (n m k)
    (+o m k n)))

(define <=o
  (lambda (n m)
    (cond@
      ((<o n m) succeed)
      ((== n m) succeed)
      (else fail))))

(define <o  ; n < m iff exists x > 0 such that n + x = m
  (lambda (n m)
    (cond@
      ((all (== '() n) (pos m)) succeed)
      ((all (== '(1) n) (gt1 m)) succeed)
      ((all (gt1 n) (gt1 m)) (both-gt1 n m))
      (else fail))))

(define both-gt1
  (lambda (n m)
    (fresh (nb nr mb mr)
      (== `(,nb . ,nr) n)
      (== `(,mb . ,mr) m)
      (condi
        ((<o nr mr) succeed)
        ((== nr mr)
         (all (== nb 0) (== 1 mb)))
        (else fail)))))


; (<ol3 q p n m) holds iff
; q = '() and (pos p) or
; width(q) < (min width(p), width(n) + width(m) + 1)
; The way that n is counted down is subtle.  When
; it hits 0, m takes the role of n, since it may have some
; bits left.  When n and m are both 0, both cases fail.
; q and p are counted down naturally.
(define <ol3
  (lambda (q p n m)
    (cond@
      [(== '() q) (pos p)]
      [else
        (fresh (qr pr _ __)
          (== `(,_ . ,qr) q)
          (== `(,__ . ,pr) p)
          (condi
            [(fresh (mr _)
               (== '() n)
               (== `(,_ . ,mr) m) 
               (<ol3 qr pr mr '()))]
            [(fresh (nr _)
                (== `(,_ . ,nr) n) 
                (<ol3 qr pr nr m))]
            [else fail]))])))
    

;; infinite loop (no answer)
;; (run (q) (fresh (x y) (*o '(1 1) `(0 0 1 ,x . ,y) `(1 0 0 ,x . ,y)) (== `(,x ,y) q)))
;; (solution (q x y) (**o '(1 1) `(0 0 1 ,x . ,y) `(1 0 0 ,x . ,y)))
;;
;; or
;;
;; (run (q) (fresh (x y z) (*o `(1 . ,x) `(0 1 . ,y) `(1 . ,z))))
;;
;; or even worse
;;
;; (run (q) (fresh (x y) (*o `(1 . ,x) `(0 1) `(1 . ,y))))
;;
;; or worst of all
;;
;; (run (q) (*o `(1 . ,q) `(0 1) `(1 . ,q)))
;;
;; and
;;
;; (run (q) (*o `(1 . ,q) `(1 1) `(1 . ,q)))

(define *o
  (lambda (n m p)
    (condi
      [(== '() n) (== '() m) (== '() p)]
      [(== '() n) (pos m) (== '() p)]
      [(== '() m) (pos n) (== '() p)]
      [(== '(1) n) (== '(1) m) (== '(1) p)]
      [(== '(1) n) (gt1 m) (== m p)]
      [(== '(1) m) (gt1 n) (== n p)]
      [(gt1 n) (gt1 m) (gen-mult n m p)]
      [else fail])))

(define gen-mult
  (lambda (n m p)
    (condi
      [(gen-mult-even/even n m p) succeed]
      [(gen-mult-even/odd n m p) succeed]
      [(gen-mult-even/odd m n p) succeed]
      [(gen-mult-odd/odd m n p) succeed]
      [else fail])))

(define gen-mult-even/even
  (lambda (n m p)
    (fresh (n/2 m/2 p/4)
      (== `(0 . ,n/2) n)
      (== `(0 . ,m/2) m)         
      (== `(0 0 . ,p/4) p)
      (*o n/2 m/2 p/4))))

(define gen-mult-even/odd
  (lambda (n m p)
    (condi
      [(gen-mult-two/odd n m p) succeed]
      [(gen-mult-gt2even/odd n m p) succeed]
      [else fail])))

(define gen-mult-two/odd
  (lambda (n m p)
    (fresh (<m-1>/2 p/4 res)
      (== `(0 1) n)
      (== `(1 . ,<m-1>/2) m)         
      (== `(0 0 . ,p/4) res)
      (*o '(1) <m-1>/2 p/4)
      (+o res n p))))

(define gen-mult-gt2even/odd
  (lambda (n m p)
    (fresh (n/2 <m-1>/2 p/4 res)
      (gt2 n)
      (== `(0 . ,n/2) n)
      (== `(1 . ,<m-1>/2) m)         
      (== `(0 0 . ,p/4) res)
      (<ol3 p/4 p n m)
      (*o n/2 <m-1>/2 p/4)
      (+o res n p))))


(define gen-mult-odd/odd
  (lambda (n m p)
    (fresh (<n-1>/2 <m-1>/2 p/4 res res2 res3)
      (== `(1 . ,<n-1>/2) n)
      (== `(1 . ,<m-1>/2) m)
      (== `(0 0 . ,p/4) res)
      (<ol3 p/4 p n m)
      (*o <n-1>/2 <m-1>/2 p/4)
      (+o res `(0 . ,<n-1>/2) res2)
      (+o res2 `(0 . ,<m-1>/2) res3)
      (+o res3 '(1) p))))



(define comp-l
  (lambda (n m base-comp)
    (cond@
      [(== '() n) (base-comp m)]
      [else
        (fresh (x y _ __)
          (== `(,_ . ,x) n)
          (== `(,__ . ,y) m)
          (comp-l x y base-comp))])))


; Compare the length of two numerals.  (<ol a b) holds holds if a=0
; and b>0, or if (floor (log2 a)) < (floor (log2 b)) That is, we
; compare the length (logarithms) of two numerals For a positive
; numeral, its bitlength = (floor (log2 n)) + 1
(define <ol
  (lambda (n m)
    (cond@
      [(== '() n) (pos m)]
      [(== '(1) n) (gt1 m)]      
      [else
        (fresh (x y _ __)
          (== `(,_ . ,x) n)
          (== `(,__ . ,y) m)
          (gt1 n)
          (pos n)
          (<ol x y))])))

(define =ol
  (lambda (n m)
    (cond@
      [(== '() n) (== '() m)]
      [(== '(1) n) (== '(1) m)]
      [else
        (fresh (x y _ __)
          (== `(,_ . ,x) n)
          (== `(,__ . ,y) m)
          (pos x)
          (pos y)
          (=ol x y))])))

(define <=ol
  (lambda (n m)
    (cond@
      [(<ol n m) succeed]
      [(=ol n m) succeed]
      [else fail])))


;; This is the theorem we want to generate (see next to last rule).
;; ((1 . y) (0 . y) (1) (1))   y is pos  ; n is 3 or gtr   m is 2 or gtr
;;
;; Unfortunately, we now get duplicate answers for one of our test cases, because of overlap.
(define divo
  (lambda (n m q r)
    (condi
      [(== '() q) (<=ol n m) (== r n) (<o n m)]
      [(== '(1) q) (== '(1) m) (<o m n) (=ol m n) (<o r m) (-o n m r)]
      [(== '(1) q) (gt2 m) (<o m n) (=ol m n) (<o r m) (-o n m r)]  ; overlaps when x is 2 or more
      [(== n m) (pos m) (== '(1) q) (== '() r)]      
      [(gt1 q) (== '(1) m) (== n q) (== '() r)]
      [(fresh (x) (== `(0 . ,x) n) (== '(0 1) m) (gt1 x) (== x q)) (== '() r)]
      [(fresh (x) (== `(1 . ,x) n) (== '(0 1) m) (== x q)) (== '(1) r)]  ; overlap when x is 1
      [(== '(1) q) (fresh (x) (== `(1 . ,x) n) (== `(0 . ,x) m) (pos x)) (== '(1) r)] ; the new rule      
      [else (fresh (res)
              (gt2 m)
              (<ol m n)
              (<o r m)
              (<ol res `(0 . ,n))
              (-o n res r)
              (*o q m res))])))

(define 1or>2
  (lambda (n)
    (cond@
      [(== '(1) n) succeed]
      [else (gt2 n)])))

(define gt2
  (lambda (n)
    (cond@
      [(== '(1 1) n) succeed]
      [else (fresh (a b c d)
              (== `(,a ,b ,c . ,d) n))])))
                 
(define bexp
  (lambda (a n)
    (cond
      [(eq? '() n) '(1)]
      [(= (car n) 0)
       (b* (bexp a (cdr n)) (bexp a (cdr n)))]
      [(= (car n) 1)
       (b* a (bexp a (bmonus1 n)))]      
      [else #f])))

(define b*
  (lambda (n m)
    (cond
     [(and (eq? '() n) (eq? '() m)) '()]     
     [(and (eq? '() n) (pair? m)) '()]
     [(and (eq? '() m) (pair? n)) '()]
     [(and (equal? '(1) n) (equal? '(1) m)) '(1)]     
     [(and (equal? '(1) n) (pair? (cdr m))) m]
     [(and (equal? '(1) m) (pair? (cdr n))) n]     
     [(and (pair? (cdr n)) (pair? (cdr m)))
      (cond
       [(and (= 0 (car n)) (= 0 (car m)))
        (cons 0 (cons 0 (b* (cdr n) (cdr m))))]
       [(and (= 1 (car n)) (= 0 (car m)))
        (b+ m (cons 0 (cons 0 (b* (cdr n) (cdr m)))))]
       [(and (= 0 (car n)) (= 1 (car m)))
        (b+ n (cons 0 (cons 0 (b* (cdr n) (cdr m)))))]
       [(and (= 1 (car n)) (= 1 (car m)))
        (bmonus1 (b+ (b* (bmonus1 n) (bmonus1 m)) (b+ n m)))]
       [else #f])]
     [else #f])))

(define b+
  (lambda (n m)
    (cond
     [(and (eq? '() n) (eq? '() m)) '()]     
     [(and (eq? '() n) (pair? m)) m]
     [(and (eq? '() m) (pair? n)) n]
     [(and (pair? n) (pair? m))     
      (cond
       [(and (= 0 (car n)) (= 0 (car m)))
        (cons 0 (b+ (cdr n) (cdr m)))]
       [(and (= 1 (car n)) (= 0 (car m)))
        (cons 1 (b+ (cdr n) (cdr m)))]
       [(and (= 0 (car n)) (= 1 (car m)))
        (cons 1 (b+ (cdr n) (cdr m)))]
       [(and (= 1 (car n)) (= 1 (car m)))
        (cons 0 (b+ '(1) (b+ (cdr n) (cdr m))))]
       [else #f])]
     [else #f])))

(define bmonus1
  (lambda (n)
    (cond
     [(eq? '() n) '()]
     [(and (= (car n) 1) (pair? (cdr n))) (cons 0 (cdr n))]
     [(and (= (car n) 1) (not (pair? (cdr n)))) '()]
     [(= (car n) 0) (cons 1 (bmonus1 (cdr n)))]
     [else #f])))



(define count-up
  (lambda (i n)
    (cond@
      ((== i n) succeed)
      (else (count-up (+ i 1) n)))))


;;;  alli is not in the book yet
'(cout "Test recursive enumerability of alli" nl)
'(let ((n 7))
  (do ((i 0 (+ 1 i))) ((> i n))
    (do ((j 0 (+ 1 j))) ((> j n))
      (test-check
	(string-append "alli enumerability: " (number->string i)
          " " (number->string j))
        (run (q)
          (fresh (x y)
            (alli (count-up 0 x) (count-up 0 y))
            (== x i)
            (== y j)
            (== `(,x ,y) q)))
        `(,i ,j)
        #f))))

(cout "testing 3 * q = 6\n")
(pretty-print (run (q) (*o (build 3) q (build 6))))

'(cout "Testing strong commutativity" nl)
'(pretty-print
  (prefix 50
    (run-stream (q)
      (fresh (a b c)
        (adder 0 a b c)
          (== `(,a ,b ,c) q)
          (once
            (fresh (x y z)
              (adder 0 x y z)
              (== x b)
              (== y a)
              (== z c)))))))

'(pretty-print
  (prefix 50
    (run-stream (q)
      (fresh (a b c)
        (adder 1 a b c)
          (== `(,a ,b ,c) q)
          (once
            (fresh (x y z)
              (adder 1 x y z)
              (== x b)
              (== y a)
              (== z c)))))))

'(cout "Test recursive enumerability of addition" nl)
'(let ((n 7))
  (do ((i 0 (+ 1 i))) ((> i n))
    (do ((j 0 (+ 1 j))) ((> j n))
      (let ((p (+ i j)))
	(test-check
	  (string-append "enumerability: " (number->string i)
	    "+" (number->string j) "=" (number->string p))
	  (run (q)
	    (fresh (x y z) 
	      (all (+o x y z)
  		  (== x (build i))
          (== y (build j))
          (== z (build p))
		  (== q (list x y z)))))
	  `(,(build i) ,(build j) ,(build p))
          #f)))))


(test-check "addition"
  (run (q)
    (fresh (x)
      (+o (build 29) (build 3) x)
      (project (x) (== (trans x) q))))
  32)

(test-check "addition2"
  (run (q)
    (fresh (x)
      (+o (build 3) x (build 29))
      (project (x) (== (trans x) q))))
  26)

(test-check "all numbers that sum to 4"
  (prefix 10
    (run-stream (w)
    (fresh (y z)
      (+o y z (build 4))
      (project (y z) (== `(,(trans y) ,(trans z)) w)))))
 '((4 0) (0 4) (1 3) (3 1) (2 2)))
 
;; 

(test-check "print a few numbers such as X + 1 = Y"
  (prefix 5
    (run-stream (w)
      (fresh (x y)
        (+o x (build 1) y) (== `(,x ,y) w))))
  '((() (1))                                  ; 0 + 1 = 1
    ((1) (0 1))                               ; 1 + 1 = 2
    ((0 __.0 . ___.0) (1 __.0 . ___.0))       ; 2*x and 2*x+1 for all x
                                        
    ((1 1) (0 0 1))                           ; the successor of 3 is 4
    ((1 0 __.0 . ___.0) (0 1 __.0 . ___.0)))) ; 1 added to an odd is an even.

(test-check "subtraction-1"
  (run (q)
    (fresh (x)
      (-o (build 29) (build 3) x)
      (project (x) (== (trans x) q))))
  26)

(test-check "subtraction-2"
  (run (q)
    (fresh (x)
      (-o (build 29) x (build 3))
      (project (x) (== (trans x) q))))
  26)

(test-check "subtraction-3"
  (run (q)
    (fresh (x)
      (-o x (build 3) (build 26))
      (project (x) (== (trans x) q))))
  29)

(test-check "subtraction-4"
  (run (q)
    (fresh (x)
      (-o (build 29) (build 29) x)
      (project (x) (== (trans x) q))))
  0)

(test-check "subtraction-5"
  (run (q)
    (fresh (x)
      (-o (build 29) (build 29) x)
      (project (x) (== (trans x) q))))
  0)

(test-check "subtraction-6"
  (run (q)
    (fresh (x)
      (-o (build 29) (build 30) x)
      (project (x) (== (trans x) q))))
  #f)

(test-check "print a few numbers such as y - z = 4"
  (prefix 15
    (run-stream (w)
      (fresh (x y)
        (-o x y (build 4))
        (== `(,x ,y) w))))
  '(((0 0 1) ())
	((1 0 1) (1))
	((0 1 1) (0 1))
	((1 1 1) (1 1))
	((0 0 0 1) (0 0 1))
	((1 0 0 1) (1 0 1))
	((0 1 0 1) (0 1 1))
	((1 1 0 1) (1 1 1))
	((0 0 1 __.0 . ___.0) (0 0 0 __.0 . ___.0))
	((1 0 1 __.0 . ___.0) (1 0 0 __.0 . ___.0))
	((0 1 1 __.0 . ___.0) (0 1 0 __.0 . ___.0))
	((1 1 1 __.0 . ___.0) (1 1 0 __.0 . ___.0))
	((0 0 0 0 1) (0 0 1 1))
	((1 0 0 0 1) (1 0 1 1))
	((0 1 0 0 1) (0 1 1 1))))

(test-check "print a few numbers such as x - y = z"
  (prefix 15
    (run-stream (w)
      (fresh (x y z)
        (-o x y z)
        (== `(,x ,y ,z) w))))
  '((() () ())
    ((_.0 . __.0) (_.0 . __.0) ())
    ((_.0 . __.0) () (_.0 . __.0))
    ((0 1) (1) (1))
    ((1 __.0 . ___.0) (1) (0 __.0 . ___.0))
    ((1 __.0 . ___.0) (0 __.0 . ___.0) (1))
    ((0 0 1) (1) (1 1))
    ((0 0 1) (0 1) (0 1))
    ((0 1 __.0 . ___.0) (1) (1 0 __.0 . ___.0))
    ((0 0 1) (1 1) (1))
    ((0 0 0 1) (1) (1 1 1))
    ((1 0 1) (1 1) (0 1))
    ((0 0 1 __.0 . ___.0) (1) (1 1 0 __.0 . ___.0))
    ((0 1 __.0 . ___.0) (1 0 __.0 . ___.0) (1))
    ((0 0 0 0 1) (1) (1 1 1 1))))

(newline)

(test-check "comparison-1"
  (run (q)
    (fresh (x)
      (<o x (build 4))
      (project (x) (== (trans x) q))))
  0)

(test-check "comparison-2"
  (run (q)
    (fresh (x)
      (== x (build 3))
      (<o x (build 4))
      (project (x) (== (trans x) q))))
  3)

(test-check "comparison-3"
  (run (q)
    (fresh (x)
      (== x (build 4))
      (<o x (build 3))
      (project (x) (== (trans x) q))))
  #f)

(test-check "print some numbers x that are less than y"
  (prefix 9 (run-stream (q) (fresh (x y) (<o x y) (== `(,x ,y) q))))
  '((() (_.0 . __.0))
    ((1) (_.0 __.0 . ___.0))
    ((_.0 1) (_.1 __.0 __.1 . ___.0))
    ((0 __.0 . ___.0) (1 __.0 . ___.0))
    ((_.0 __.0 1) (_.1 __.1 __.2 __.3 . ___.0))
    ((_.0 0 __.0 . ___.0) (_.1 1 __.0 . ___.0))
    ((_.0 __.0 __.1 1) (_.1 __.2 __.3 __.4 __.5 . ___.0))
    ((_.0 __.0 0 __.1 . ___.0) (_.1 __.2 1 __.1 . ___.0))
    ((_.0 __.0 __.1 __.2 1)
     (_.1 __.3 __.4 __.5 __.6 __.7 . ___.0))))

(test-check "print all numbers less than 6"
  (prefix 10 (run-stream (x) (<o x (build 6))))
  '(() (1) (_.0 1) (_.0 0 1)))

(test-check "print a few numbers that are greater than 4"
  (prefix 20 (run-stream (x) (<o (build 4) x)))
  '((_.0 __.0 __.1 __.2 . ___.0) (1 0 1) (_.0 1 1)))

(test-check "multiplication-1"
  (run (q)
    (fresh (x)
      (*o (build 2) (build 3) x)
      (project (x) (== (trans x) q))))
  6)

(test-check "multiplication-2"
  (run (q)
    (fresh (x)
      (*o (build 3) x (build 12))
      (project (x) (== (trans x) q))))
  4)

(test-check "multiplication-3"
  (run (q)
    (fresh (x)
      (*o x (build 3) (build 12))
      (project (x) (== (trans x) q))))
  4)

(test-check "multiplication-4"
  (run (q)
    (fresh (x)
      (*o x (build 5) (build 12))))
  #f)

(test-check "multiplication-5"
  (run (q)
    (fresh (x)
      (== x (build 2))
      (*o x (build 2) (build 4))
      (project (x) (== (trans x) q))))
  2)

(test-check "multiplication-fail-1"
  (run (q)
    (fresh (x)
      (== x (build 3))
      (*o x (build 2) (build 4))
      (project (x) (== (trans x) q))))
  #f)

(test-check "multiplication-all-1"
  (prefix 10
    (run-stream (x)
      (fresh (y z)
        (*o y z (build 6))
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((1 6) (6 1) (2 3) (3 2)))

(test-check "multiplication-all-2"
  (prefix 10
    (run-stream (x)
      (fresh (y z)
        (*o y z (build 24))
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((1 24) (24 1) (2 12) (8 3) (12 2) (3 8) (4 6) (6 4)))

(test-check "multiplication-all-3"
  (prefix 7
    (run-stream (x)        
      (fresh (y z)
        (*o (build 3) y z)
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((0 0) (1 3) (2 6) (3 9) (4 12) (5 15) (6 18)))

(test-check "multiplication-all-4"
  (prefix 5
    (run-stream (x)        
      (fresh (y z)
        (*o y (build 3) z)
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((0 0) (1 3) (2 6) (3 9) (4 12)))

(test-check "multiplication-all-5"
  (prefix 26
    (run-stream (q)        
      (fresh (x y z)
        (*o x y z)
        (== `(,x ,y ,z) q))))
  '((() () ())
    (() (_.0 . __.0) ())
    ((_.0 . __.0) () ())
    ((1) (1) (1))
    ((1) (_.0 __.0 . ___.0) (_.0 __.0 . ___.0))
    ((_.0 __.0 . ___.0) (1) (_.0 __.0 . ___.0))
    ((0 1) (0 1) (0 0 1))
    ((0 1) (1 1) (0 1 1))
    ((0 1) (0 __.0 __.1 . ___.0) (0 0 __.0 __.1 . ___.0))
    ((1 1) (0 1) (0 1 1))
    ((0 __.0 __.1 . ___.0) (0 1) (0 0 __.0 __.1 . ___.0))
    ((0 0 1) (1 1) (0 0 1 1))
    ((0 0 1) (0 0 1) (0 0 0 0 1))
    ((1 1) (1 1) (1 0 0 1))
    ((0 0 1) (0 1 1) (0 0 0 1 1))
    ((0 1) (1 __.0 __.1 . ___.0) (0 1 __.0 __.1 . ___.0))
    ((0 0 1) (0 0 __.0 __.1 . ___.0) (0 0 0 0 __.0 __.1 . ___.0))
    ((1 1) (0 0 1) (0 0 1 1))
    ((0 1 1) (0 0 1) (0 0 0 1 1))
    ((0 1 1) (1 1) (0 1 0 0 1))
    ((0 0 __.0 __.1 . ___.0) (0 0 1) (0 0 0 0 __.0 __.1 . ___.0))
    ((1 0 1) (1 1) (1 1 1 1))
    ((0 0 0 1) (0 1 1) (0 0 0 0 1 1))
    ((0 0 0 1) (1 1) (0 0 0 1 1))
    ((0 0 0 1) (0 0 0 1) (0 0 0 0 0 0 1))
    ((1 __.0 __.1 . ___.0) (0 1) (0 1 __.0 __.1 . ___.0))))

(test-check "multiplication-even-1"
  (prefix 10
    (run-stream (q)        
      (fresh (y z)
        (*o (build 2) y z)
        (== `(,y ,z) q))))
  '((() ())
    ((1) (0 1))
    ((0 1) (0 0 1))
    ((1 1) (0 1 1))
    ((0 __.0 __.1 . ___.0) (0 0 __.0 __.1 . ___.0))
    ((1 __.0 __.1 . ___.0) (0 1 __.0 __.1 . ___.0))))

(test-check "division-1"
  (run (q)
    (fresh (x _)
      (divo (build 4) (build 2) x _)
      (project (x) (== (trans x) q))))
  2)

(test-check "division-fail-1"
  (run (q)
    (fresh (x _)
      (divo (build 4) (build 0) x _)
      (project (x) (== (trans x) q))))
  #f)

(test-check "division-2"
  (run (q)
    (fresh (x _)
      (all
        (divo (build 4) (build 3) x _)
        (project (x) (== (trans x) q)))))
  1)

(test-check "division-3"
  (run (q)
    (fresh (x _)
      (divo (build 4) (build 4) x _)
      (project (x) (== (trans x) q))))
  1)

(test-check "division-4"
  (run (q)
    (fresh (x _)
      (divo (build 4) (build 5) x _)
      (project (x) (== (trans x) q))))
  0)

(test-check "division-5"
  (run (q)
    (fresh (x _)
      (divo (build 33) (build 3) x _)
      (project (x) (== (trans x) q))))
  11)

(test-check "remainder-4"
  (run (q)
    (fresh (x _)
      (divo (build 4) (build 5) _ x)
      (project (x) (== (trans x) q))))
  4)

(test-check "division-5"
  (run (q)
    (fresh (x _)
      (divo (build 33) (build 3) x _)
      (project (x) (== (trans x) q))))
  11)

(test-check "division-6"
  (run (q)
    (fresh (x _)
      (divo (build 33) x (build 11) _)
      (project (x) (== (trans x) q))))
  3)

(test-check "division-7"
  (run (q)
    (fresh (x _)
      (divo x (build 3) (build 11) _)
      (project (x) (== (trans x) q))))
  33)

(test-check "division-8"
  (run (q)
    (fresh (x _)
      (divo x (build 5) _ (build 4))
      (project (x) (== (trans x) q))))
  4)

(test-check "division-9"
  (run (q)
    (fresh (x _)
      (divo x (build 5) (build 3) (build 4))
      (project (x) (== (trans x) q))))
  19)

(test-check "division-10"
  (run (q)
    (fresh (x _)
      (divo x _ (build 3) (build 4))
      (project (x) (== (trans x) q))))
  22)

(test-check "division-fail-2"
  (run (q)
    (fresh (x _)
      (divo (build 5) x (build 7) _)
      (project (x) (== (trans x) q))))
  #f)

(test-check "division-11"
  (run (q)
    (fresh (x _)
      (divo (build 33) (build 5) x _)
      (project (x) (== (trans x) q))))
  6)

(test-check "all numbers such as 5/Z = 1"
  (prefix 5
    (run-stream (q)        
      (fresh (z _)
        (divo (build 5) z (build 1) _)
        (project (z) (== (trans z) q)))))
  '(4 5 4 3))
;; Should not have any duplicates!


(test-check "all inexact factorizations of 12"
  (run* (w)
    (fresh (m q r n)
      (== n (build 12))
      (<=o m n)
      (divo n m q r)
      (project (n m q r) (== `(,(trans n) ,(trans m) ,(trans q) ,(trans r)) w))))
  '((12 1 12 0)
    (12 2 6 0)
    (12 3 4 0)
    (12 6 2 0)
    (12 4 3 0)
    (12 5 2 2)
    (12 7 1 5)
    (12 11 1 1)
    (12 10 1 2)
    (12 9 1 3)
    (12 8 1 4)
    (12 12 1 0)))

(test-check "div-all-3"
  (prefix 12
    (run-stream (w)
      (fresh (x y z r)
        (divo x y z r)
        (== `(,x ,y ,z ,r) w))))
  '((() (_.0 . __.0) () ())
    ((1 __.0 1) (0 __.0 1) (1) (1))
    ((1) (_.0 __.0 . ___.0) () (1))
    ((_.0 . __.0) (_.0 . __.0) (1) ())
    ((_.0 1) (__.0 _.1 __.1 . ___.0) () (_.0 1))
    ((1 __.0 c.0 1) (0 __.0 c.0 1) (1) (1))
    ((_.0 __.0 1) (__.1 __.2 _.1 __.3 . ___.0) () (_.0 __.0 1))
    ((_.0 __.0 . ___.0) (1) (_.0 __.0 . ___.0) ())
    ((_.0 __.0 __.1 1) (__.2 __.3 __.4 _.1 __.5 . ___.0) () (_.0 __.0 __.1 1))
    ((1 __.0 c.0 _.0 1) (0 __.0 c.0 _.0 1) (1) (1))
    ((_.0 __.0 __.1 __.2 1) (__.3 __.4 __.5 __.6 _.1 __.7 . ___.0) () (_.0 __.0 __.1 __.2 1))
    ((0 _.0 __.0 . ___.0) (0 1) (_.0 __.0 . ___.0) ())))

;    ((1 __.0 1) (0 __.0 1) (1) (1))    
;    ((1 __.0 c.0 1) (0 __.0 c.0 1) (1) (1))
;    ((1 __.0 c.0 _.0 1) (0 __.0 c.0 _.0 1) (1) (1))




(test-check "div-even"
  (run* (w)
    (fresh (y z r)
      (divo `(0 . ,y) (build 2) z r)
      (== `(,y ,z ,r) w)))
  '(((1) (1) ()) ((_.0 __.0 . ___.0) (_.0 __.0 . ___.0) ())))

(test-check "mul-even"
  (run* (q)
    (fresh (x y)
      (*o x (build 2) `(0 . ,y))
      (== `(,x ,y) q)))
  '(((1) (1))
    ((0 1) (0 1))
    ((1 1) (1 1))
    ((0 __.0 __.1 . ___.0) (0 __.0 __.1 . ___.0))
    ((1 __.0 __.1 . ___.0) (1 __.0 __.1 . ___.0))))


(cout "Testing strong multiplicative commutativity" nl)
(pretty-print
  (prefix 50
    (run-stream (q)
      (fresh (a b c)
        (*o a b c)
          (== `(,a ,b ,c) q)
          (once
            (fresh (x y z)
              (*o x y z)
              (== x b)
              (== y a)
              (== z c)))))))

(if (not tex)
  (begin
    (display "Test recursive enumerability")
    (newline)))

(let ((n 7))
  (do ((i 0 (+ 1 i))) ((> i n))
    (do ((j 0 (+ 1 j))) ((> j n))
      (let ((p (* i j)))
	    (test-check
	      (string-append "enumerability: " (number->string i)
	        "*" (number->string j) "=" (number->string p))
	    (run (q) 
          (fresh (x y z) 
	        (*o x y z)
	        (== (build i) x)
            (== (build j) y)
            (== (build p) z)
            (== `(,x ,y ,z) q)))
	    `(,(build i) ,(build j) ,(build p)))))))
