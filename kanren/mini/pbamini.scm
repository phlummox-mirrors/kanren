(load "sempublic.scm")

'(define-syntax trace-vars
  (syntax-rules ()
    [(_ name (id* ...))
     succeed]))

(define tex #f)

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (test-check title tested-expression expected-result #t))
    ((_ title tested-expression expected-result show-flag)
     (begin
       (let* ((expected expected-result)
              (produced tested-expression))
         (if (equal? expected produced)
             (if tex
                 (if show-flag
                     (generate-tex 'tested-expression produced)
                     (void))
                 (cout title " works!" nl))
             (errorf 'test-check
                     "Failed ~s: ~a~%Expected: ~a~%Computed: ~a~%"
                     title 'tested-expression expected produced)))))))

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
      ((pair? x) (cons (tex-data (car x)) (tex-data (cdr x))))
      ((symbol? x)
       (cond
         ((var-symbol? x) (translate-to-tex x))
         (else x)))
      (else x))))

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
     ((eq? (car x) #\.) '())
     (else (cons (car x) (prefix-id (cdr x)))))))

(define build
  (lambda (n)
    (cond
      ((zero? n) '())
      (else (cons (if (even? n) 0 1) (build (quotient n 2)))))))

(define trans
  (lambda (n)
    (cond
      ((null? n) 0)
      (else (+ (car n) (* 2 (trans (cdr n))))))))

(define c==
  (lambda (a)
    (lambda (b)
      (== a b))))

(define poso
  (lambda (n)
    (fresh (_ __)
      (== `(,_ . ,__) n))))

(define >1o
  (lambda (n)
    (fresh (_ __)
      (== `(,_ . ,__) n)
      (poso __))))

'(define half-adder
 (lambda (x y r c-out)
   (all
     (bit-xor x y r)
     (bit-and x y c-out))))

(define bop-maker
  (lambda (table)
    (lambda (x y r)
      (for@ (c== `(,x ,y ,r)) table))))

(define bit-and
  (bop-maker '((0 0 0) (1 0 0) (0 1 0) (1 1 1))))

(define nullo
  (lambda (x)
    (== '() x)))

(define caro
  (lambda (x a)
    (fresh (_)
      (== `(,a . ,_) x))))

(define cdro
  (lambda (x d)
    (fresh (_)
      (== `(,_ . ,d) x))))

(define for@
  (lambda (f l)
    (cond@
      ((nullo l) fail)
      ((fresh (a)
         (caro l a)
         (project (a)
           (f a)))
       succeed)
      (else
        (fresh (d)
          (cdro l d)
          (for@ f d))))))

;; Examples of for@ usage
; (run* (q) (for@ (lambda (f) (f (build 9) q)) `(,caro ,cdro)))
; (1 (0 0 1))

;(run* (q)
;  (for@
;    (lambda (x) (caro x q))
;    `(,(build 0)
;      ,(build 1)
;      ,(build 2)
;      ,(build 3)
;      ,(build 4)
;      ,(build 5))))

; > (run* (q) (for@ (lambda (x) (all (poso x) (== x q))) (map build '(0 1 2 3 4 5))))
; ((1) (0 1) (1 1) (0 0 1) (1 0 1))
; > (run* (q) (for@ (lambda (x) (all (>1o x) (== x q))) (map build '(0 1 2 3 4 5))))
; ((0 1) (1 1) (0 0 1) (1 0 1))

; oddnes and evenness for positive numbers
; > (run* (q) (for@ (lambda (x) (caro x q)) (map build '(0 1 2 3 4 5))))
; (1 0 1 0 1)


(define pairo
  (lambda (ls)
    (fresh (_ __)
      (== `(,_ . ,__) ls))))


(define half-adder
  (lambda (x y r c)
    (for@
      (c== `(,x ,y ,r ,c))
      '((0 0 0 0) (1 0 1 0) (0 1 1 0) (1 1 0 1)))))

'(define full-adder
  (lambda (b x y r c)
    (fresh (w xy wz)
      (half-adder x y w xy)
      (half-adder w b r wz)
      (bit-xor xy wz c))))

(define full-adder
  (lambda (b x y r c)
    (cond@
      ((== b 0) (== x 0) (== y 0) (== r 0) (== c 0))
      ((== b 1) (== x 0) (== y 0) (== r 1) (== c 0))
      ((== b 0) (== x 1) (== y 0) (== r 1) (== c 0))
      ((== b 1) (== x 1) (== y 0) (== r 0) (== c 1))
      ((== b 0) (== x 0) (== y 1) (== r 1) (== c 0))
      ((== b 1) (== x 0) (== y 1) (== r 0) (== c 1))
      ((== b 0) (== x 1) (== y 1) (== r 0) (== c 1))
      ((== b 1) (== x 1) (== y 1) (== r 1) (== c 1))
      (else fail))))

(define bit-or
  (lambda (x y r)
    (for@
      (c== `(,x ,y ,r))
      '((0 0 0) (1 0 1) (0 1 1) (1 1 1)))))

(define bit-xor
  (lambda (x y r)
    (for@
      (c== `(,x ,y ,r))
      '((0 0 0) (1 0 1) (0 1 1) (1 1 0)))))

(define build-bit
  (lambda (b k)
    (cond@
      ((== 0 b) (== '() k))
      ((== 1 b) (== '(1) k))
      (else fail))))

(define commute
  (lambda (sym asym)
    (lambda (n m k)
      (condi
        ((sym n m k) succeed)
        ((asym n m k) succeed)
        ((asym m n k) succeed)
        (else fail)))))

(define sym+
  (lambda (n m p)
    (condi
      ((== '() n) (== '() m)
       (== '() p))
      ((== '(1) n) (== '(1) m)
       (== '(0 1) p))
      ((>1o n) (>1o m)
       (gen+ n m p))
      (else fail))))

(define asym+
  (lambda (n m p)
    (condi
      ((== '() n) (poso m) 
       (== m p))
      ((== '(1) n) (>1o m)
       (gen1+ m p))
      ((>1o n) (>1o m)
       (fresh (x y z)
         (== `(0 . ,x) n)
         (== `(1 . ,y) m)                  
         (== `(1 . ,z) p)
         (+o x y z)))
      (else fail))))

(define gen1+
  (lambda (m p)
    (fresh (mr z)
      (condi
        ((poso mr) (== `(0 . ,mr) m) (== `(1 . ,mr) p))
        ((== `(1 . ,mr) m) (== `(0 . ,z) p) (+o '(1) mr z))
        (else fail)))))

(define gen-odd/odd+
  (lambda (x y z)
    (fresh (t t1)
      (alli
	(<ol x `(0 0 . ,z))
	(<ol y `(0 0 . ,z))
	(boundx t t1 x `(0 . ,y))
        (gen1+ t z)
        (+o x y t)))))

(define gen+
  (lambda (n m p)
    (condi
      ((fresh (x y z) 
         (== `(0 . ,x) n)
         (== `(0 . ,y) m)
         (== `(0 . ,z) p)
         (+o x y z))
       succeed)
      ((fresh (x y z)
         (== `(1 . ,x) n)
         (== `(1 . ,y) m)
         (== `(0 . ,z) p)
         (gen-odd/odd+ x y z)
	 ;(trace-vars 'done (x y z))
	 )
       succeed)
      (else fail))))

(define +o (commute sym+ asym+))


'(define +o (lambda (m n p) 
	     (all (trace-vars 3 (m n p)) ((commute sym+ asym+) m n p))))

(define -o
  (lambda (n m k)
    (+o m k n)))

(define =o ;;; hardly necessary.
  (lambda (n m)
    (== n m)))

(define <o  ; n < m iff exists x >0 such that n + x = m
  (lambda (n m)
    (fresh (x)
      (poso x)
      (+o n x m))))

; (<ol3 q p n m) holds iff
; q = '() and (poso p) or
; width(q) < (min width(p), width(n) + width(m) + 1)
; The way that n is counted down is subtle.  When
; it hits 0, m takes the role of n, since it may have some
; bits left.  When n and m are both 0, both cases fail.
; q and p are counted down naturally.

(define boundx
  (lambda (r p n m)
    (fresh (q b)
      (== `(,b . ,q) r)
      (bound-auxx q p n m))))

(define bound-auxx
  (lambda (q p n m)
    (cond@
      ((== '() q) (poso p))
      (else
        (fresh (x y _ __)
          (== `(,_ . ,x) q)
          (== `(,__ . ,y) p)
          (condi
            ((fresh (z _)
               (== '() n)
               (== `(,_ . ,z) m) 
               (bound-auxx x y z '()))
             succeed)
            ((fresh (z _)
               (== `(,_ . ,z) n) 
               (bound-auxx x y z m)))
            (else fail)))))))

  
;; infinite loops in both Kanren and mini-Kanren
;;
;; (run (q) (fresh (x y) (xo '(1 1) `(1 ,x . ,y) `(,x . ,y))))
;; (solution (q) (exists (x y) (**o '(1 1) `(1 ,x . ,y) `(,x . ,y))))
;;
;; (run (q) (fresh (r) (xo `(1 . ,r) `(1 1) `(1 . ,r))))
;; (solution (q) (**o `(1 . ,q) `(1 1) `(1 . ,q)))

(define symx
  (lambda (n m p)
    (condi
      ((== '() n) (== '() m)
       (== '() p))
      ((== '(1) n) (== '(1) m)
       (== '(1) p))
      ((>1o n) (>1o m)
       (genx n m p))
      (else fail))))

(define asymx
  (lambda (n m p)
    (condi
      ((== '() n) (poso m) 
       (== '() p))
      ((== '(1) n) (>1o m)
       (== m p))
      ((>1o n) (>1o m)
       (fresh (x y z)
         (== `(0 . ,x) n)
         (== `(1 . ,y) m)                  
         (== `(0 . ,z) p)
         (xo x m z)))
      (else fail))))

(define genx  ;;; always fails
  (lambda (n m p)
    (condi
      ((fresh (x y z) 
         (== `(0 . ,x) n)
         (== `(0 . ,y) m)
         (== `(0 0 . ,z) p)
         (xo x y z))
       succeed)
      ((fresh (x y r s t)
         (== `(1 . ,x) n)
         (== `(1 . ,y) m)
         (boundx r p n m)
         (genx `(0 . ,x) `(0 . ,y) r)
         (+o `(0 . ,x) `(0 . ,y) s)
         (+o r s t)
         (+o t '(1) p))
       succeed)
      (else fail))))

(define xo (commute symx asymx))



; Compare the length of two numerals.  (<ol a b) holds holds if a=0
; and b>0, or if (floor (log2 a)) < (floor (log2 b)) That is, we
; compare the length (logarithms) of two numerals For a positive
; numeral, its bitlength = (floor (log2 n)) + 1

(define <ol
  (lambda (n m)
    (cond@
      ((== '() n) (poso m))
      ((== '(1) n) (>1o m))
      ((>1o n) (>1o m)
       (fresh (x y _ __)
         (== `(,_ . ,x) n)
         (== `(,__ . ,y) m)
         (<ol x y)))
      (else fail))))

; holds if both a and b are zero
; or if (floor (log2 a)) = (floor (log2 b))

(define =ol
  (lambda (n m)
    (cond@
      ((== '() n) (== '() m))
      ((== '(1) n) (== '(1) m))
      ((>1o n) (>1o m)
        (fresh (x y _ __)
          (== `(,_ . ,x) n)
          (== `(,__ . ,y) m)
          (=ol x y)))
      (else fail))))


;(run (x) (+o '(1 1) '(1 0 1) x))
;#!eof


;; divide 8 by 7
;; (0 0 0 1) by (1 1 1)

(define divo
  (lambda (n m q r)
    (condi
      [(== '() q) (=ol n m) (== r n) (<o n m)]
      [(== '() q) (<ol n m) (== r n) (<o n m)]      
      [(== '(1) q) (=ol m n) (<o r m) (-o n m r)]
      [(>1o q) (== '(1) m) (== n q) (== '() r)]
      [else (fresh (res)
              (>1o m)
              (<ol m n)
              (<o r m)
              (<ol res `(0 . ,n))
              (-o n res r)
              (xo q m res))])))

(define build-bit
  (lambda (b k)
    (cond@
      ((== 0 b) (== '() k))
      ((== 1 b) (== '(1) k))
      (else fail))))


(define count-up
  (lambda (i n)
    (cond@
      ((== i n) succeed)
      (else (count-up (+ i 1) n)))))

(cout "Test recursive enumerability of addition" nl)
(let ((n 7))
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


;;; losers
(test-check "multiplication-all-2"
  (prefix 10
    (run-stream (x)
      (fresh (y z)
        (xo y z (build 24))
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((2 12) (1 24) (12 2) (24 1) (4 6) (8 3) (6 4) (3 8))
  )

(test-check "division-7"
  (run (q)
    (fresh (x _)
      (divo x (build 3) (build 11) _)
      (project (x) (== (trans x) q))))
  33)

'(test-check "div-even"  ;; this loops indefinitely.
  (prefix 5
    (run-stream (w)
      (fresh (y z r)
        (divo `(0 . ,y) (build 2) z r)
        (== `((0 . ,y) ,(build 2) ,z ,r) w))))
  '(((0 1) (0 1) (1) ())
 ((0 0 1) (0 1) (0 1) ())
 ((0 1 1) (0 1) (1 1) ())
 ((0 0 _.0 1) (0 1) (0 _.0 1) ())
 ((0 1 _.0 1) (0 1) (1 _.0 1) ())))

(cout "Testing strong multiplicative commutativity" nl)
(pretty-print
  (prefix 50
    (run-stream (q)
      (fresh (a b c)
        (xo a b c)
          (== `(,a ,b ,c) q)
          (once
            (fresh (x y z)
              (xo x y z)
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
                (xo x y z)
                (== (build i) x)
            (== (build j) y)
            (== (build p) z)
            (== `(,x ,y ,z) q)))
            `(,(build i) ,(build j) ,(build p)))))))
;#!eof
(cout "Testing strong commutativity with 1" nl)
(pretty-print
  (prefix 10
    (run-stream (q)
      (fresh (a b c t)
       (alli
	  (+o '(1) a t)
	  (+o t b c)
	  (== `(,a ,b ,c) q)
	 (trace-vars 1 (a b c))
	 (once
	   (fresh (x y z t)
	     (alli (+o x '(1) t)
	       (+o t y z))
	     (== x b)
	     (== y a)
	     (== z c))))))))

(define compositeo
  (lambda (n)
    (fresh (x y)
      (>1o n)
      (>1o x)
      (>1o y)
      (xo x y n))))

(define bump
  (lambda (n x)
    (cond@
      ((== n x) succeed)
      (else
        (fresh (m)
          (-o n '(1) m)
          (bump m x))))))

;; Generate all composite numbers up to 20.
'(test-check "compositeo"
  (run* (q)
    (bump (build 20) q)
    (once (compositeo q)))
  '((0 0 1 0 1)
    (0 1 0 0 1)
    (0 0 0 0 1)
    (1 1 1 1)
    (0 1 1 1)
    (0 0 1 1)
    (0 1 0 1)
    (1 0 0 1)
    (0 0 0 1)
    (0 1 1)
    (0 0 1)))



;;; winners

(test-check "times-0-0"
  (run* (q) (xo (build 0) (build 0) q))
  '(()))

(test-check "times-1-1"
  (run* (q) (xo (build 1) (build 1) q))
  '((1)))

(test-check "times-2-2"
  (run* (q) (xo (build 2) (build 2) q))
  '((0 0 1)))

(test-check "times-0-1"
  (run* (q) (xo (build 0) (build 1) q))
  '(()))

(test-check "times-1-2"
  (run* (q) (xo (build 1) (build 2) q))
  '((0 1)))

(test-check "times-2-3"
  (run* (q) (xo (build 2) (build 3) q))
  '((0 1 1)))

(test-check "times-3-3"
  (run* (q) (xo (build 3) (build 3) q))
  '((1 0 0 1)))

(test-check "gt1test1"
  (run* (q) (>1o q))  
  '((_.0 _.1 . __.0)))

(test-check "postest1"
  (run* (q) (poso q))
  '((_.0 . __.0)))

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
(pretty-print (run (q) (xo (build 3) q (build 6))))

(cout "Testing strong commutativity" nl)
(pretty-print
  (prefix 50
    (run-stream (q)
      (fresh (a b c)
        (+o a b c)
          (== `(,a ,b ,c) q)
          (once
            (fresh (x y z)
              (+o x y z)
              (== x b)
              (== y a)
              (== z c)))))))

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
 '((2 2) (0 4) (4 0) (1 3) (3 1)))
 
(test-check "print a few numbers such as X + 1 = Y"
  (prefix 5
    (run-stream (w)
      (fresh (x y)
        (+o x (build 1) y) (== `(,x ,y) w))))
  '(((1) (0 1))
    (() (1))
    ((0 _.0 . __.0) (1 _.0 . __.0))
    ((1 1) (0 0 1))
    ((1 0 _.0 . __.0) (0 1 _.0 . __.0)))
  ) ; 1 added to an odd is an even.

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
  '(((0 0 0 1) (0 0 1))
 ((0 0 1) ())
 ((0 1 1) (0 1))
 ((1 0 0 1) (1 0 1))
 ((0 0 1 _.0 . __.0) (0 0 0 _.0 . __.0))
 ((1 0 1) (1))
 ((0 1 0 1) (0 1 1))
 ((1 1 0 1) (1 1 1))
 ((0 0 0 0 1) (0 0 1 1))
 ((1 0 1 _.0 . __.0) (1 0 0 _.0 . __.0))
 ((0 1 1 _.0 . __.0) (0 1 0 _.0 . __.0))
 ((1 1 1) (1 1))
 ((0 0 0 1 _.0 . __.0) (0 0 1 0 _.0 . __.0))
 ((1 0 0 0 1) (1 0 1 1))
 ((0 1 0 0 1) (0 1 1 1))))

(test-check "print a few numbers such as x - y = z"
  (prefix 15
    (run-stream (w)
      (fresh (x y z)
        (-o x y z)
        (== `(,x ,y ,z) w))))
  '((() () ())
 ((_.0 . __.0) () (_.0 . __.0))
 ((0 1) (1) (1))
 ((_.0 . __.0) (_.0 . __.0) ())
 ((0 0 1) (0 1) (0 1))
 ((1 _.0 . __.0) (1) (0 _.0 . __.0))
 ((0 1 1) (1 1) (1 1))
 ((1 _.0 . __.0) (0 _.0 . __.0) (1))
 ((0 1 _.0 . __.0) (0 1) (0 0 _.0 . __.0))
 ((1 0 1) (0 1) (1 1))
 ((0 0 0 1) (1 1) (1 0 1))
 ((1 0 1) (1 1) (0 1))
 ((0 0 0 1) (0 0 1) (0 0 1))
 ((0 0 1) (1) (1 1))
 ((0 1 0 1) (1 1) (1 1 1))))

(newline)

(test-check "comparison-1"
  (run (q)
    (fresh (x)
      (<o x (build 4))
      (project (x) (== (trans x) q))))
  2)

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

;;; (test-check "comparison-4" (run (q) (fresh (x y) (<o q q))) #f)

(test-check "comparison-5"
  (run$ (q) (fresh (x y) (<o x y) (== `(,x ,y) q)))
  '(((1) (0 1))
 (() (_.0 . __.0))
 ((0 1) (0 0 1))
 ((0 _.0 . __.0) (1 _.0 . __.0))
 ((1 1) (0 1 1))
 ((1) (1 _.0 . __.0))
 ((0 1) (0 1 _.0 . __.0))
 ((1 1) (1 0 1))
 ((1 1) (0 0 0 1))
 ((0 1) (1 0 1)))
  )

(test-check "comparison-6"
  (run$ (q) (fresh (x y) (<o `(0 . ,x) `(1 . ,y)) (== `(,x ,y) q)))
  '(((1) (0 1))
 ((_.0 . __.0) (_.0 . __.0))
 ((1) (1 _.0 . __.0))
 ((0 1) (0 0 1))
 ((0 _.0 . __.0) (1 _.0 . __.0))
 ((1 1) (0 1 1))
 ((0 1) (1 0 1))
 ((0 1) (0 1 _.0 . __.0))
 ((1 1) (1 0 1))
 ((1 1) (0 0 0 1))))

(test-check "comparison-7"
  (run$ (q) (fresh (x y) (<o `(1 . ,x) `(1 . ,y)) (== `(,x ,y) q)))
  '((() (_.0 . __.0))
 ((1) (0 1))
 ((0 _.0 . __.0) (1 _.0 . __.0))
 ((0 1) (0 0 1))
 ((1) (1 _.0 . __.0))
 ((1 1) (0 1 1))
 ((1 1) (1 0 1))
 ((0 0 _.0 . __.0) (0 1 _.0 . __.0))
 ((0 1) (1 0 1))
 ((1 0 1) (0 0 0 1))))

(define inf-loop-again
  (lambda ()
    (run$ (q) (fresh (x y) (<o `(0 . ,q) `(1 . ,q))))))

(define inf-loop-again
  (lambda ()
    (run (q) (fresh (x y) (<ol q q)))))

(test-check "comparison-10"
  (run$ (q) (fresh (x y) (<ol x y) (== `(,x ,y) q)))
  '((() (_.0 . __.0))
        ((1) (_.0 _.1 . __.0))
        ((_.0 1) (_.1 _.2 _.3 . __.0))
        ((_.0 _.1 1) (_.2 _.3 _.4 _.5 . __.0))
        ((_.0 _.1 _.2 1) (_.3 _.4 _.5 _.6 _.7 . __.0))
        ((_.0 _.1 _.2 _.3 1) (_.4 _.5 _.6 _.7 _.8 _.9 . __.0))
        ((_.0 _.1 _.2 _.3 _.4 1)
         (_.5 _.6 _.7 _.8 _.9 _.10 _.11 . __.0))
        ((_.0 _.1 _.2 _.3 _.4 _.5 1)
         (_.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 . __.0))
        ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 1)
         (_.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 . __.0))
        ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 1)
         (_.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 . __.0))))

(test-check "comparison-12"
  (run$ (q) (fresh (x y) (<ol `(1 . ,x) `(1 . ,y)) (== `(,x ,y) q)))
  '((() (_.0 . __.0))
    ((1) (_.0 _.1 . __.0))
        ((_.0 1) (_.1 _.2 _.3 . __.0))
        ((_.0 _.1 1) (_.2 _.3 _.4 _.5 . __.0))
        ((_.0 _.1 _.2 1) (_.3 _.4 _.5 _.6 _.7 . __.0))
        ((_.0 _.1 _.2 _.3 1) (_.4 _.5 _.6 _.7 _.8 _.9 . __.0))
        ((_.0 _.1 _.2 _.3 _.4 1)
         (_.5 _.6 _.7 _.8 _.9 _.10 _.11 . __.0))
        ((_.0 _.1 _.2 _.3 _.4 _.5 1)
         (_.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 . __.0))
        ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 1)
         (_.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 . __.0))
        ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 1)
         (_.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 . __.0))))

(define infinite-loop-again
  (lambda ()
    (run (q) (fresh (x y) (<ol `(0 . ,q) `(1 . ,q))))))

(test-check "print some numbers x that are less than y"
  (prefix 9 (run-stream (q) (fresh (x y) (<o x y) (== `(,x ,y) q))))
  '(((1) (0 1))
 (() (_.0 . __.0))
 ((0 1) (0 0 1))
 ((0 _.0 . __.0) (1 _.0 . __.0))
 ((1 1) (0 1 1))
 ((1) (1 _.0 . __.0))
 ((0 1) (0 1 _.0 . __.0))
 ((1 1) (1 0 1))
 ((1 1) (0 0 0 1)))
  )


(test-check "infinite loop for addition?"
  (run (q) (fresh (_ __) (+o q `(1 0 ,_ . ,__) `(1 1 ,_ . ,__))))
  '(0 1))

(test-check "print all numbers less than 6"
  (prefix 10 (run-stream (x) (<o x (build 6))))
  '((0 1) () (1 1) (1 0 1) (0 0 1) (1)))

(test-check "print a few numbers that are greater than 4"
  (run$ (x) (<o (build 4) x))
  '((0 0 0 1)
 (1 0 0 1)
 (0 1 0 1)
 (1 0 1)
 (0 0 1 _.0 . __.0)
 (1 1 0 1)
 (0 1 1)
 (1 0 1 _.0 . __.0)
 (0 0 0 0 1)
 (1 1 1))
  )

(define sad-to-see-this-go
  '((__.0 __.1 _.0 _.1 . __.2) (1 0 1) (__.0 1 1)))

(test-check "multiplication-1"
  (run (q)
    (fresh (x)
      (xo (build 2) (build 3) x)
      (project (x) (== (trans x) q))))
  6)

(test-check "multiplication-2"
  (run (q)
    (fresh (x)
      (xo (build 3) x (build 12))
      (project (x) (== (trans x) q))))
  4)

(test-check "multiplication-3"
  (run (q)
    (fresh (x)
      (xo x (build 3) (build 12))
      (project (x) (== (trans x) q))))
  4)

(test-check "multiplication-4"
  (run (q)
    (fresh (x)
      (xo x (build 5) (build 12))))
  #f)

(test-check "multiplication-5"
  (run (q)
    (fresh (x)
      (== x (build 2))
      (xo x (build 2) (build 4))
      (project (x) (== (trans x) q))))
  2)

(test-check "multiplication-6"
  (run (q) (fresh (w x y z) (xo `(0 ,x ,y . ,z) `(,w 1) `(1 ,x ,y . ,z))))
  #f)

(test-check "multiplication-fail-1"
  (run (q)
    (fresh (x)
      (== x (build 3))
      (xo x (build 2) (build 4))
      (project (x) (== (trans x) q))))
  #f)

(test-check "multiplication-all-1"
  (prefix 10
    (run-stream (x)
      (fresh (y z)
        (xo y z (build 6))
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((1 6) (6 1) (2 3) (3 2)))

(test-check "multiplication-all-3"
  (prefix 7
    (run-stream (x)        
      (fresh (y z)
        (xo (build 3) y z)
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((3 9) (0 0) (5 15) (1 3) (7 21) (6 18) (9 27))
  )

(test-check "multiplication-all-4"
  (prefix 5
    (run-stream (x)        
      (fresh (y z)
        (xo y (build 3) z)
        (project (y z)
          (== `(,(trans y) ,(trans z)) x)))))
  '((3 9) (0 0) (5 15) (1 3) (7 21)))

(test-check "multiplication-all-5"
  (prefix 26
    (run-stream (q)        
      (fresh (x y z)
        (xo x y z)
        (== `(,x ,y ,z) q))))
  '((() () ())
 (() (_.0 . __.0) ())
 ((1) (1) (1))
 ((_.0 . __.0) () ())
 ((0 1) (0 1) (0 0 1))
 ((1) (_.0 _.1 . __.0) (_.0 _.1 . __.0))
 ((1 1) (1 1) (1 0 0 1))
 ((_.0 _.1 . __.0) (1) (_.0 _.1 . __.0))
 ((0 1) (0 _.0 _.1 . __.0) (0 0 _.0 _.1 . __.0))
 ((0 1 1) (1 1) (0 1 0 0 1))
 ((1 1) (1 0 1) (1 1 1 1))
 ((1 1) (0 1 1) (0 1 0 0 1))
 ((0 0 1) (0 0 1) (0 0 0 0 1))
 ((0 1) (1 _.0 . __.0) (0 1 _.0 . __.0))
 ((1 1) (1 1 1) (1 0 1 0 1))
 ((1 _.0 . __.0) (0 1) (0 1 _.0 . __.0))
 ((0 _.0 _.1 . __.0) (0 1) (0 0 _.0 _.1 . __.0))
 ((0 1 1) (1 0 1) (0 1 1 1 1))
 ((1 0 1) (1 1) (1 1 1 1))
 ((1 0 1) (0 1 1) (0 1 1 1 1))
 ((0 1 1) (0 1 1) (0 0 1 0 0 1))
 ((0 0 1 1) (1 1) (0 0 1 0 0 1))
 ((1 1 1) (1 1) (1 0 1 0 1))
 ((1 1) (0 0 1 1) (0 0 1 0 0 1))
 ((0 0 1 1) (0 1 1) (0 0 0 1 0 0 1))
 ((0 1 1) (1 1 1) (0 1 0 1 0 1))))

(test-check "multiplication-even-1"
  (run* (q)        
    (fresh (y z)
      (xo (build 2) y z)
      (== `(,y ,z) q)))
  '(((0 1) (0 0 1))
 ((1 _.0 . __.0) (0 1 _.0 . __.0))
 ((0 _.0 _.1 . __.0) (0 0 _.0 _.1 . __.0))
 (() ())
 ((1) (0 1))))

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
  '(5 3 4))
;; Should not have any duplicates!


(test-check "all inexact factorizations of 12"
  (run* (w)
    (fresh (m q r n)
      (== (build 12) n)
      (any (<o m n) (== m n))
      (divo n m q r)
      (project (n m q r) (== `(,(trans n) ,(trans m) ,(trans q) ,(trans r)) w))))
  '((12 4 3 0)
 (12 3 4 0)
 (12 11 1 1)
 (12 2 6 0)
 (12 1 12 0)
 (12 9 1 3)
 (12 6 2 0)
 (12 5 2 2)
 (12 10 1 2)
 (12 7 1 5)
 (12 8 1 4)
 (12 12 1 0)))

(test-check "div-all-3"
  (prefix 12
    (run-stream (w)
      (fresh (x y z r)
        (divo x y z r)
        (== `(,x ,y ,z ,r) w))))
  '(((0 1) (1 1) () (0 1))
 (() (_.0 . __.0) () ())
 ((0 0 1) (0 1 1) () (0 0 1))
 ((1) (1) (1) ())
 ((0 0 1) (1 1 1) () (0 0 1))
 ((1) (0 1) () (1))
 ((0 _.0 1) (1 _.0 1) () (0 _.0 1))
 ((_.0 _.1 . __.0) (1) (_.0 _.1 . __.0) ())
 ((1 0 1) (1 1 1) () (1 0 1))
 ((1) (1 _.0 . __.0) () (1))
 ((1 0 1) (0 1 1) () (1 0 1))
 ((1 1) (0 1) (1) (1))))

(define old-div-all-3
  (lambda ()
  '((() (_.0 . __.0) () ())
    ((_.0 1) (1) (_.0 1) ())
    ((1) (_.0 _.1 . __.0) () (1))
    ((1) (1) (1) ())
    ((_.0 1) (__.0 _.1 _.2 . __.1) () (_.0 1))
    ((_.0 _.1 1) (1) (_.0 _.1 1) ())
    ((_.0 _.1 1) (__.0 __.1 _.2 _.3 . __.2) () (_.0 _.1 1))
    ((0 1) (1 1) () (0 1))
    ((_.0 _.1 _.2 1) (__.0 __.1 __.2 _.3 _.4 . __.3) () (_.0 _.1 _.2 1))
    ((_.0 _.1 _.2 1) (1) (_.0 _.1 _.2 1) ())
    ((_.0 _.1 _.2 _.3 1) (__.0 __.1 __.2 __.3 _.4 _.5 . __.4) () (_.0 _.1 _.2 _.3 1))
    ((__.0 1) (__.0 1) (1) ()))))

;    ((1 __.0 1) (0 __.0 1) (1) (1))    
;    ((1 __.0 c.0 1) (0 __.0 c.0 1) (1) (1))
;    ((1 __.0 c.0 _.0 1) (0 __.0 c.0 _.0 1) (1) (1))




(define 4ref
  '(((0 1) (0 1) ())
    ((1) (1) ())
    ((1 1) (1 1) ())
    ((0 _.0 1) (0 _.0 1) ())
    ((1 _.0 1) (1 _.0 1) ())))

(define 4ref
  '(((1) (1) ()) ((_.0 __.0 . ___.0) (_.0 __.0 . ___.0) ())))

(test-check "mul-even"
  (run* (q)
    (fresh (x y)
      (xo x (build 2) `(0 . ,y))
      (== `(,x ,y) q)))
  '(((0 1) (0 1))
    ((1) (1))
    ((0 _.0 _.1 . __.0) (0 _.0 _.1 . __.0))
    ((1 _.0 . __.0) (1 _.0 . __.0))))




(pretty-print
 (prefix 10
   (run-stream (q)
     (fresh (x y z r)
       (divo x y z r)
       (== `(,x ,y ,z ,r) q)
        (project (q)
         (cond
           ((ground? q) succeed)
           (else fail)))))))

(pretty-print
  (prefix 10
    (run-stream (q)
      (fresh (x y z r)
        (divo x y z r)
        (== `(,x ,y ,z ,r) q)
        (project (q)
         (cond
           ((ground? q) fail)
           (else succeed)))))))

(define gen&test
   (lambda (op)
     (lambda (i j k)
       (fresh (x y z)
         (once
           (op x y z)
           (== i x)
           (== j y)
           (== k z))))))


(define enumerate
  (lambda (op)
    (lambda (r n)
      (fresh (i j k)
        (bump n i)
        (bump n j)
        (op i j k)
        ((gen&test op) i j k)
        (== `(,i ,j ,k) r)))))

(define test-enumerate
  (lambda (n)
    (prefix (expt (+ n 1) 2)
      (run-stream (q)
        ((enumerate +o) q (build n))))))

(define test-enumerate
  (lambda (n op)
    (prefix (expt (+ n 1) 2)
      (run-stream (q)
        ((enumerate op) q (build n))))))
      


;; Not so great--- (primeo v) always fails if v is a variable.
(define primeo
  (lambda (n)
    (fails (compositeo n))))

(define x-always-0
  (lambda (x)
    (any
      (== 0 x)
      (x-always-0 x))))

(define any*
  (lambda (a)
    (cond@
      (a succeed)
      (else (any* a)))))

(define always (any* succeed))

'(run (q)
  (all
    (any (== 0 q) (== 1 q))
    always)
  (== q 1))

(run (q)
  (alli
    (any (== 0 q) (== 1 q))
    always)
  (== q 1))


'(define reify-id
  (lambda (id index)
    (string->symbol
      (string-append
        (symbol->string id)
        "$_{_{"
        (number->string index)
        "}}$"))))