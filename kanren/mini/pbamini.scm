;;; The winner!!

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

(define both-fresh-and-same
  (lambda (n m)
    (all
      (fails (fails (== #t n) (== #t m)))
      (fails (== #t n) (== #f m)))))

(define <o  
  (lambda (n m)
    (condo
      [(both-fresh-and-same n m) fail]
      [else
        (cond@
          ((all (== '() n) (pos m)) succeed)
          ((all (== '(1) n) (gt1 m)) succeed)
          ((fresh (_ nr __ mr)
             (== `(,_ . ,nr) n)
             (== `(,__ . ,mr) m)
             (condi
               ((<o nr mr) succeed)
               ((== nr mr) (all (== _ 0) (== 1 __)))
               (else fail))
             (pos nr)
             (pos mr))
           succeed)
          (else fail))])))

(define =o
  (lambda (n m)
    (condi
      [(== '() n) (== '() m)]
      [(== '(1) n) (== '(1) m)]
      [(fresh (x y) (== `(,x . ,y) n) (== `(,x . ,y) m))]
      [else fail])))


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
  
;; infinite loops in both Kanren and mini-Kanren
;;
;; (run (q) (fresh (x y) (*o '(1 1) `(1 ,x . ,y) `(,x . ,y))))
;; (solution (q) (exists (x y) (**o '(1 1) `(1 ,x . ,y) `(,x . ,y))))
;;
;; (run (q) (*o `(1 . ,q) `(1 1) `(1 . ,q)))
;; (solution (q) (**o `(1 . ,q) `(1 1) `(1 . ,q)))

;; Infinite loops in Kanren, but not in mini-Kanren
;;
;; (solution (q x y) (**o '(1 1) `(0 0 1 ,x . ,y) `(1 0 0 ,x . ,y)))
;; (solution (q x y z) (**o `(1 . ,x) `(0 1 . ,y) `(1 . ,z)))

(define *o
  (lambda (n m p)
    (condi
      ((== '() n) (== '() m) (== p '()))
      ((== '() n) (pos m) (== p '()))
      ((== '() m) (pos n) (== p '()))
      ((== '(1) n) (== '(1) m) (== '(1) p))      ; 1 * m = m
      ((== '(1) n) (gt1 m) (== m p))      ; 1 * m = m
      ((== '(1) m) (gt1 n) (== n p))      ; 1 * m = m      

      ((fresh (nr mr pr)
         (== `(0 . ,nr) n)
         (== `(0 . ,mr) m)         
         (== `(0 0 . ,pr) p)
         (pos nr)
         (pos mr)
         (pos pr)         
         (*o nr mr pr)
         )
       succeed)

      ((fresh (nr mr pr)
         (== `(0 . ,nr) n)
         (== `(1 . ,mr) m)                  
         (== `(0 . ,pr) p)
         (pos nr)
         (pos mr)
         (pos pr)         
         (*o nr m pr)
         )  ;;; can we get away without addition?
       succeed)

      ((fresh (nr mr pr)
         (== `(0 . ,mr) m)
         (== `(1 . ,nr) n)                  
         (== `(0 . ,pr) p)
         (pos mr)
         (pos nr)
         (pos pr)         
         (*o n mr pr)
         )  ;;; can we get away without addition?
       succeed)
      
      ; (2*nr+1) * m = 2*(n*m) + m
      ; m > 0; also nr>0 for well-formedness
      ; the result is certainly greater than 1.
      ; we note that m > 0 and so 2*(nr*m) < 2*(nr*m) + m
      ; and (floor (log2 (nr*m))) < (floor (log2 (2*(nr*m) + m)))
      ((fresh (nr p1 _ __)
         (== `(1 ,_ . ,__) m)		; m is odd and n > 1
         (== `(1 . ,nr) n)
         (pos nr)
         (gt1 p)
         (<ol3 p1 p n m)
         (*o nr m p1)
         (+o `(0 . ,p1) m p))
       succeed)
      (else fail))))

; Compare the length of two numerals.  (<ol a b) holds holds if a=0
; and b>0, or if (floor (log2 a)) < (floor (log2 b)) That is, we
; compare the length (logarithms) of two numerals For a positive
; numeral, its bitlength = (floor (log2 n)) + 1


(define <ol
  (lambda (n m)
    (condo
      [(both-fresh-and-same n m) fail]     
      [else
       (cond@
         [(== '() n) (pos m)]
         [(== '(1) n) (gt1 m)]  
         [(fresh (x y _ __)
            (== `(,_ . ,x) n)
            (== `(,__ . ,y) m)
            (<ol x y)
            (gt1 n))
          succeed]
         [else fail])])))

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


;; This is the theorem we want to generate (see next to last rule).
;; ((1 . y) (0 . y) (1) (1))   y is pos  ; n is 3 or gtr   m is 2 or gtr

(define divo
  (lambda (n m q r)
    (condi
      [(== '() q) (<ol n m) (== r n) (<o n m)]
      [(<ol m n) (<o r m)
       (fresh (res)      
         (<ol res `(0 . ,n))
         (-o n res r)
         (*o q m res))]
      [(pos n) (=ol m n) (<o r m) (== q '(1)) (-o n m r)]
      [(pos n) (== '() q) (=ol m n) (== r n) (<o n m)]
      [else fail])))

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

(test-check "comparison-4"
  (run (q) (fresh (x y) (<o q q)))
  #f)

(test-check "comparison-5"
  (run$ (q) (fresh (x y) (<o x y) (== `(,x ,y) q)))
  '((() (_.0 . __.0))
    ((1) (_.0 __.0 . ___.0))
    ((0 _.0 . __.0) (1 _.0 . __.0))
    ((_.0 1) (__.0 _.1 __.1 . ___.0))
    ((_.0 0 _.1 . __.0) (__.1 1 _.1 . __.0))
    ((_.0 _.1 1) (__.0 __.1 _.2 __.2 . ___.0))
    ((_.0 _.1 0 _.2 . __.0) (__.1 __.2 1 _.2 . __.0))
    ((_.0 _.1 _.2 1) (__.0 __.1 __.2 _.3 __.3 . ___.0))
    ((_.0 _.1 _.2 0 _.3 . __.0) (__.1 __.2 __.3 1 _.3 . __.0))
    ((_.0 _.1 _.2 _.3 1) (__.0 __.1 __.2 __.3 _.4 __.4 . ___.0))))

(test-check "comparison-6"
  (run$ (q) (fresh (x y) (<o `(0 . ,x) `(1 . ,y)) (== `(,x ,y) q)))  
  '(((_.0 . __.0) (_.0 . __.0))
    ((1) (_.0 __.0 . ___.0))
    ((0 _.0 . __.0) (1 _.0 . __.0))
    ((_.0 1) (__.0 _.1 __.1 . ___.0))
    ((_.0 0 _.1 . __.0) (__.1 1 _.1 . __.0))
    ((_.0 _.1 1) (__.0 __.1 _.2 __.2 . ___.0))
    ((_.0 _.1 0 _.2 . __.0) (__.1 __.2 1 _.2 . __.0))
    ((_.0 _.1 _.2 1) (__.0 __.1 __.2 _.3 __.3 . ___.0))
    ((_.0 _.1 _.2 0 _.3 . __.0) (__.1 __.2 __.3 1 _.3 . __.0))
    ((_.0 _.1 _.2 _.3 1) (__.0 __.1 __.2 __.3 _.4 __.4 . ___.0))))

(test-check "comparison-7"
  (run$ (q) (fresh (x y) (<o `(1 . ,x) `(1 . ,y)) (== `(,x ,y) q)))
  '((() (__.0 . ___.0))
    ((1) (_.0 __.0 . ___.0))
    ((0 _.0 . __.0) (1 _.0 . __.0))
    ((_.0 1) (__.0 _.1 __.1 . ___.0))
    ((_.0 0 _.1 . __.0) (__.1 1 _.1 . __.0))
    ((_.0 _.1 1) (__.0 __.1 _.2 __.2 . ___.0))
    ((_.0 _.1 0 _.2 . __.0) (__.1 __.2 1 _.2 . __.0))
    ((_.0 _.1 _.2 1) (__.0 __.1 __.2 _.3 __.3 . ___.0))
    ((_.0 _.1 _.2 0 _.3 . __.0) (__.1 __.2 __.3 1 _.3 . __.0))
    ((_.0 _.1 _.2 _.3 1) (__.0 __.1 __.2 __.3 _.4 __.4 . ___.0))))

(test-check "comparison-8"
  (run$ (q) (fresh (x y) (<o `(0 . ,q) `(1 . ,q))))  
  '((_.0 . __.0)))

(test-check "comparison-9"
  (run (q) (fresh (x y) (<ol q q)))
  #f)

(test-check "comparison-10"
  (run$ (q) (fresh (x y) (<ol x y) (== `(,x ,y) q)))
  '((() (_.0 . __.0))
    ((1) (_.0 __.0 . ___.0))
    ((_.0 1) (__.0 _.1 __.1 . ___.0))
    ((_.0 _.1 1) (__.0 __.1 _.2 __.2 . ___.0))
    ((_.0 _.1 _.2 1) (__.0 __.1 __.2 _.3 __.3 . ___.0))
    ((_.0 _.1 _.2 _.3 1) (__.0 __.1 __.2 __.3 _.4 __.4 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 1) (__.0 __.1 __.2 __.3 __.4 _.5 __.5 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 _.5 1) (__.0 __.1 __.2 __.3 __.4 __.5 _.6 __.6 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 1) (__.0 __.1 __.2 __.3 __.4 __.5 __.6 _.7 __.7 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 1) (__.0 __.1 __.2 __.3 __.4 __.5 __.6 __.7 _.8 __.8 . ___.0))))

(test-check "comparison-11"
  (run$ (q) (fresh (x y) (<ol `(0 . ,x) `(1 . ,y)) (== `(,x ,y) q)))  
  '(((1) (_.0 __.0 . ___.0))
    ((_.0 1) (__.0 _.1 __.1 . ___.0))
    ((_.0 _.1 1) (__.0 __.1 _.2 __.2 . ___.0))
    ((_.0 _.1 _.2 1) (__.0 __.1 __.2 _.3 __.3 . ___.0))
    ((_.0 _.1 _.2 _.3 1) (__.0 __.1 __.2 __.3 _.4 __.4 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 1) (__.0 __.1 __.2 __.3 __.4 _.5 __.5 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 _.5 1) (__.0 __.1 __.2 __.3 __.4 __.5 _.6 __.6 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 1) (__.0 __.1 __.2 __.3 __.4 __.5 __.6 _.7 __.7 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 1) (__.0 __.1 __.2 __.3 __.4 __.5 __.6 __.7 _.8 __.8 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 1) (__.0 __.1 __.2 __.3 __.4 __.5 __.6 __.7 __.8 _.9 __.9 . ___.0))))

(test-check "comparison-12"
  (run$ (q) (fresh (x y) (<ol `(1 . ,x) `(1 . ,y)) (== `(,x ,y) q)))
  '((() (__.0 . ___.0))
    ((1) (_.0 __.0 . ___.0))
    ((_.0 1) (__.0 _.1 __.1 . ___.0))
    ((_.0 _.1 1) (__.0 __.1 _.2 __.2 . ___.0))
    ((_.0 _.1 _.2 1) (__.0 __.1 __.2 _.3 __.3 . ___.0))
    ((_.0 _.1 _.2 _.3 1) (__.0 __.1 __.2 __.3 _.4 __.4 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 1) (__.0 __.1 __.2 __.3 __.4 _.5 __.5 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 _.5 1) (__.0 __.1 __.2 __.3 __.4 __.5 _.6 __.6 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 1) (__.0 __.1 __.2 __.3 __.4 __.5 __.6 _.7 __.7 . ___.0))
    ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 1) (__.0 __.1 __.2 __.3 __.4 __.5 __.6 __.7 _.8 __.8 . ___.0))))

(test-check "comparison-13"
  (run (q) (fresh (x y) (<ol `(0 . ,q) `(1 . ,q))))  
  #f)


(test-check "print some numbers x that are less than y"
  (prefix 9 (run-stream (q) (fresh (x y) (<o x y) (== `(,x ,y) q))))
  '((() (_.0 . __.0))
    ((1) (_.0 __.0 . ___.0))
    ((0 _.0 . __.0) (1 _.0 . __.0))
    ((_.0 1) (__.0 _.1 __.1 . ___.0))
    ((_.0 0 _.1 . __.0) (__.1 1 _.1 . __.0))
    ((_.0 _.1 1) (__.0 __.1 _.2 __.2 . ___.0))
    ((_.0 _.1 0 _.2 . __.0) (__.1 __.2 1 _.2 . __.0))
    ((_.0 _.1 _.2 1) (__.0 __.1 __.2 _.3 __.3 . ___.0))
    ((_.0 _.1 _.2 0 _.3 . __.0) (__.1 __.2 __.3 1 _.3 . __.0))))

(define 4ref
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
  (run* (x) (<o (build 4) x))
  '((__.0 __.1 _.0 __.2 . ___.0) (1 0 1) (__.0 1 1)))

(define 4ref
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

(test-check "multiplication-6"
  (run (q) (fresh (w x y z) (*o `(0 ,x ,y . ,z) `(,w 1) `(1 ,x ,y . ,z))))
  #f)

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
    ((0 1) (1 _.0 . __.0) (0 1 _.0 . __.0))
    ((0 1) (0 _.0 __.0 . ___.0) (0 0 _.0 __.0 . ___.0))
    ((1 _.0 . __.0) (0 1) (0 1 _.0 . __.0))
    ((0 _.0 __.0 . ___.0) (0 1) (0 0 _.0 __.0 . ___.0))
    ((0 0 1) (1 _.0 . __.0) (0 0 1 _.0 . __.0))
    ((0 0 1) (0 0 1) (0 0 0 0 1))
    ((1 1) (1 1) (1 0 0 1))
    ((0 0 1) (0 1 _.0 . __.0) (0 0 0 1 _.0 . __.0))
    ((0 1 1) (1 1) (0 1 0 0 1))
    ((0 0 1) (0 0 _.0 __.0 . ___.0) (0 0 0 0 _.0 __.0 . ___.0))
    ((1 _.0 . __.0) (0 0 1) (0 0 1 _.0 . __.0))
    ((0 1 _.0 . __.0) (0 0 1) (0 0 0 1 _.0 . __.0))
    ((0 0 0 1) (1 _.0 . __.0) (0 0 0 1 _.0 . __.0))
    ((0 0 _.0 __.0 . ___.0) (0 0 1) (0 0 0 0 _.0 __.0 . ___.0))
    ((1 1) (1 0 1) (1 1 1 1))
    ((0 0 0 1) (0 1 _.0 . __.0) (0 0 0 0 1 _.0 . __.0))
    ((0 1 1) (1 0 1) (0 1 1 1 1))
    ((0 0 0 1) (0 0 0 1) (0 0 0 0 0 0 1))
    ((1 1) (0 1 1) (0 1 0 0 1))))

(test-check "multiplication-even-1"
  (run* (q)        
    (fresh (y z)
      (*o (build 2) y z)
      (== `(,y ,z) q)))
  '((() ())
    ((1) (0 1))
    ((0 1) (0 0 1))
    ((1 _.0 . __.0) (0 1 _.0 . __.0))
    ((0 _.0 __.0 . ___.0) (0 0 _.0 __.0 . ___.0))))

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
  9)

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
  '(3 5 4))
;; Should not have any duplicates!


(test-check "all inexact factorizations of 12"
  (run* (w)
    (fresh (m q r n)
      (== n (build 12))
      (any (<o m n) (== m n))
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
    ((_.0 1) (1) (_.0 1) ())
    ((1) (_.0 __.0 . ___.0) () (1))
    ((1) (1) (1) ())
    ((_.0 1) (__.0 _.1 __.1 . ___.0) () (_.0 1))
    ((_.0 __.0 1) (1) (_.0 __.0 1) ())
    ((_.0 _.1 1) (__.0 __.1 _.2 __.2 . ___.0) () (_.0 _.1 1))
    ((0 1) (1 1) () (0 1))
    ((_.0 _.1 _.2 1)
     (__.0 __.1 __.2 _.3 __.3 . ___.0)
     ()
     (_.0 _.1 _.2 1))
    ((_.0 __.0 _.1 1) (1) (_.0 __.0 _.1 1) ())
    ((_.0 _.1 _.2 _.3 1)
     (__.0 __.1 __.2 __.3 _.4 __.4 . ___.0)
     ()
     (_.0 _.1 _.2 _.3 1))
    ((_.0 1) (_.0 1) (1) ())))

(define 4ref
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
  (prefix 5
    (run-stream (w)
      (fresh (y z r)
        (divo `(0 . ,y) (build 2) z r)
        (== `(,y ,z ,r) w))))
  '(((0 1) (0 1) ())
    ((1) (1) ())
    ((1 1) (1 1) ())
    ((0 __.0 1) (0 __.0 1) ())
    ((1 __.0 1) (1 __.0 1) ())))

(define 4ref
  '(((1) (1) ()) ((_.0 __.0 . ___.0) (_.0 __.0 . ___.0) ())))

(test-check "mul-even"
  (run* (q)
    (fresh (x y)
      (*o x (build 2) `(0 . ,y))
      (== `(,x ,y) q)))
  '(((1) (1))
    ((0 1) (0 1))
    ((1 _.0 . __.0) (1 _.0 . __.0))
    ((0 _.0 __.0 . ___.0) (0 _.0 __.0 . ___.0))))


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
