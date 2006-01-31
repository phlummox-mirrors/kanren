;   Benchmark query, in mini-kanren
;
;   David H. D. Warren
;
;   query population and area database to find countries
;   of approximately equal population density

; $Id$
;
; SWI-Prolog, (Version 5.0.10), Pentium IV, 2GHz:
; ?- time(dobench(10000)).
; 35,020,001 inferences in 36.78 seconds (952116 Lips)

(load "../mini/mk.scm")
(load "../mini/mkextraforms.scm")
(define benchmark_count 100)

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (display "Testing") (display title) (newline)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))


; query(quad(C1, D1, C2, D2)) :-
;         density(C1, D1),
;         density(C2, D2),
;         D1 > D2,
;         T1 is 20 * D1,
;         T2 is 21 * D2,
;         T1 < T2.

; density(C, D) :-
;         pop(C, P),
;         area(C, A),
;         D is P * 100 // A.

(define benchmark
  (letrec
    ((bquery
       (lambda (out)
	 (fresh (c1 d1 c2 d2)
	   (== `(quad ,c1 ,d1 ,c2 ,d2) out)
	   (density c1 d1)
	   (density c2 d2)
	   (project (d1 d2)
	     (== (and (> d1 d2)
		   (let ((t1 (* 20 d1))
			 (t2 (* 21 d2)))
		     (< t1 t2)))
	       #t)))))

     (choose2
       (lambda (l a b)			; l must be instantiated
	 (fresh ()
	   (== #t (pair? l))
	   (conde
	     ((== (car l) (cons a b)))
	     (else (choose2 (cdr l) a b))))))
	 
     (density
       (lambda (c d)
	 (fresh (p)
	   (choose2 population c p)
	   (project (c p)
	     (== d
	       (let ((a (cdr (assoc c area-lst))))
		 (* p (/ 100.0 a)))))))))
    bquery))

; populations in 100000s
(define population
  '(("china" . 8250)
    ("india" . 5863)
    ("ussr" . 2521)
    ("usa" . 2119)
    ("indonesia" . 1276)
    ("japan" . 1097)
    ("brazil" . 1042)
    ("bangladesh" . 750)
    ("pakistan" . 682)
    ("w_germany" . 620)
    ("nigeria" . 613)
    ("mexico" . 581)
    ("uk" . 559)
    ("italy" . 554)
    ("france" . 525)
    ("philippines" . 415)
    ("thailand" . 410)
    ("turkey" . 383)
    ("egypt" . 364)
    ("spain" . 352)
    ("poland" . 337)
    ("s_korea" . 335)
    ("iran" . 320)
    ("ethiopia"  . 272)
    ("argentina" . 251)))


; areas in 1000s of square miles
(define area-lst
  '(("china"       . 3380)
    ("india"       . 1139)
    ("ussr"        . 8708)
    ("usa"         . 3609)
    ("indonesia"   . 570)
    ("japan"       . 148)
    ("brazil"      . 3288)
    ("bangladesh"  . 55)
    ("pakistan"    . 311)
    ("w_germany"   . 96)
    ("nigeria"     . 373)
    ("mexico"      . 764)
    ("uk"          . 86)
    ("italy"       . 116)
    ("france"      . 213)
    ("philippines" . 90)
    ("thailand"    . 200)
    ("turkey"      . 296)
    ("egypt"       . 386)
    ("spain"       . 190)
    ("poland"      . 121)
    ("s_korea"     . 37)
    ("iran"        . 628)
    ("ethiopia"    . 350)
    ("argentina"   . 1080)))

(test-check 'query-benchmark
  (run 5 (out) (benchmark out))
  '((quad "indonesia" 223.859649122807 "pakistan" 219.2926045016077)
    (quad "uk" 650.0 "w_germany" 645.8333333333334)
    (quad "italy" 477.5862068965517 "philippines" 461.11111111111114)
    (quad "france" 246.4788732394366 "china" 244.08284023668637)
    (quad "ethiopia" 77.71428571428571 "mexico" 76.04712041884817)))

(display "Timing per iterations: ") (display benchmark_count) (newline)
(time (do ((i 0 (+ 1 i))) ((>= i benchmark_count))
	(run 5 (out) (benchmark out))))

; mk.scm, v1.2 (corresponds to the book)
; (time (do ((...)) ...))
;     62 collections
;     1230 ms elapsed cpu time, including 5 ms collecting
;     1251 ms elapsed real time, including 6 ms collecting
;     66764800 bytes allocated, including 67106536 bytes reclaimed

; kanren.ss version 3.45
; (time (do ((...)) ...))
;     52 collections
;     1275 ms elapsed cpu time, including 9 ms collecting
;     1312 ms elapsed real time, including 7 ms collecting
;     57261352 bytes allocated, including 56455376 bytes reclaimed
;
; kanren.ss version 4.0
;     39 collections
;     904 ms elapsed cpu time, including 7 ms collecting
;     914 ms elapsed real time, including 6 ms collecting
;     41670216 bytes allocated, including 42439072 bytes reclaimed
;
; kanren.ss version 4.17
;     38 collections
;     895 ms elapsed cpu time, including 5 ms collecting
;     946 ms elapsed real time, including 11 ms collecting
;     41320888 bytes allocated, including 41172536 bytes reclaimed
;
; kanren.ss version 4.50
;     30 collections
;     874 ms elapsed cpu time, including 6 ms collecting
;     882 ms elapsed real time, including 7 ms collecting
;     31748608 bytes allocated, including 32641448 bytes reclaimed

; dobench(Count) :-
;         data(Data),
;         repeat(Count),
;         benchmark(Data, _Result),
;         fail.
; dobench(_).
