; Palindrom products
;
; Find all six-digit numbers (that are palindromes) that are the 
; product of two three-digit numbers.
;
; We observe that a six-digit palindrom can be represented as
;   a*100000 + b*10000 + c*1000 + c*100 + b*10 + a
;   = a*100001 + b*10010 + c*1100
;   = 11*( a*9091 + b*910 + c*100 )
; where a,b, c are digits and a>0.
; So, the problem is to find such numbers a, b, c, k, xyz 
; where a in [1..9], b,c in [0..9], k in [10..90] and xyz in [100..999]
; so that k * xyz = a*9091 + b*910 + c*100
;
; Here's the solution in Haskell:
;
; [(k,xyz) | a<-[1..9], b<-[0..9], c<-[0..9], k<-[10..90], 
; 	(xyz,r)<-[quotRem (9091*a + 910*b + 100*c) k], 
; 	r==0, xyz >= 100, xyz < 1000]
;
; Or, to count them better while avoiding duplicates
;
; [11*(9091*a + 910*b + 100*c) | a<-[1..9], b<-[0..9], c<-[0..9], 
;      not $ null [k | k<-[10..90], 
;             (xyz,r) <-[quotRem (9091*a + 910*b + 100*c) k], 
;             r==0, xyz >= 100, xyz < 1000]]
;
; It's just one expression. The expression ``not $ null [k | condition]''
; is just the fancy way of saying ``exists k. condition''
; (or, in Kanren terms, (fresh (k) condition)). There are 279 solutions.
;
; $Id$

; We give two solution, both of which rely on the pure arithmetics.
;
; Here's the first solution. It uses `once'. For a pure solution, see
; below.

(define (digit a)
  (conde
    ((== a (build 0)))
    ((== a (build 1)))
    ((== a (build 2)))
    ((== a (build 3)))
    ((== a (build 4)))
    ((== a (build 5)))
    ((== a (build 6)))
    ((== a (build 7)))
    ((== a (build 8)))
    ((== a (build 9)))))

; The first version of the first solution
; Not too fast:
; (time (run 1 (q) (palprod1 q)))
;     2773 collections
;     92183 ms elapsed cpu time, including 1090 ms collecting
;     94037 ms elapsed real time, including 1154 ms collecting
;     2999789528 bytes allocated, including 2999861624 bytes reclaimed
;
; Note that without the (conde ((=ol k ...))) block in the middle,
; the time is 490 secs (13790 collections)
(define (palprod1 q)
  (fresh (a a9091 b b910 c c100 t1 sum k)
    (digit a)
    (poso a)
    (xo a (build 9091) a9091)
    (digit b)
    (xo b (build 910) b910)
    (+o a9091 b910 t1)
    (digit c)
    (xo c (build 100) c100)
    (+o t1 c100 sum)

    (project (sum) 
      (begin (display (* 11 (trans sum))) (newline) succeed))

    ; k is within [10..90]
    ; wherever possible, we represent a whole range of numbers
    ; as lists with uninstantiated binary digits.
    ; Sort of a quantum computation....
    (conde
      ((=ol k (build 8)) (<o (build 9) k))
      ((=ol k (build 16)))
      ((=ol k (build 32)))
      ((=ol k (build 64)) (<o k (build 91)))
      )

    (once
      (fresh (xyz)
	; first, we limit xyz by range. Separate bits of xyz are
	; not instantiated...
	(<ol xyz (build 1024))
	(<ol (build 32) xyz)
	(xo k xyz sum)
	; Now, we check that xyz is really in range [100..999]
	(<o xyz (build 1000))
	(<o (build 99) xyz)))

    (== q sum)))


; Now, we apply an optimization. We know that if |a| is the size of
; the number a, that is, 2^(|a|-1) <= a < 2^|a|, then
; either |a*b| = |a| + |b|  or  |a*b| = |a| + |b| - 1


; holds if |a| + |b| = |c|
(define (+ol a b c)
  (fresh (a1 ar c1 cr)
    (conde
      ((== a '()) (=ol b c))
      ((== a (cons a1 ar)) (== c (cons c1 cr)) (+ol ar b cr)))))


; > (time (run 1 (q) (palprod2 q)))
; 100001
; 101101
; (time (run 1 ...))
;     1620 collections
;     58054 ms elapsed cpu time, including 668 ms collecting
;     58728 ms elapsed real time, including 648 ms collecting
;     1752479616 bytes allocated, including 1752090008 bytes reclaimed
; ((1 1 1 0 0 1 1 1 1 1 0 0 0 1))

(define (palprod2 q)
  (fresh (a a9091 b b910 c c100 t1 sum k)
    (digit a)
    (poso a)
    (xo a (build 9091) a9091)
    (digit b)
    (xo b (build 910) b910)
    (+o a9091 b910 t1)
    (digit c)
    (xo c (build 100) c100)
    (+o t1 c100 sum)

    (project (sum) 
      (begin (display (* 11 (trans sum))) (newline) succeed))
    ; k is within [10..90]
    ; wherever possible, we represent a whole range of numbers
    ; as lists with uninstantiated binary digits.
    ; Sort of a quantum computation....
    (conde
      ((=ol k (build 8)) (<o (build 9) k))
      ((=ol k (build 16)))
      ((=ol k (build 32)))
      ((=ol k (build 64)) (<o k (build 91)))
      )

    (once
      (project (sum) ; saves one collection: 1619 rather than 1620...
      (fresh (xyz)
	; first, we limit xyz by range. Separate bits of xyz are
	; not instantiated...
	(<ol xyz (build 1024))
	(<ol (build 32) xyz)

	; Now we check that k * xyz can give the number of the size
	; of sum
	(conde
	  ((+ol k xyz sum))
	  ((+ol k xyz (cons 0 sum))))

	(xo k xyz sum)			; Do the multiplication

	; Now, we check that xyz is really in range [100..999]
	; and that k is within [10..90]
	(<o xyz (build 1000))
	(<o (build 99) xyz))))

    (== q sum)))

