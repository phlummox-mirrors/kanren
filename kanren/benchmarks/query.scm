;   Benchmark query
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


(define benchmark_count 10000)


; query(quad(C1, D1, C2, D2)) :- 
; 	density(C1, D1), 
; 	density(C2, D2),
; 	D1 > D2,
; 	T1 is 20 * D1,
; 	T2 is 21 * D2,
; 	T1 < T2.

; density(C, D) :- 
; 	pop(C, P),
; 	area(C, A),
; 	D is P * 100 // A.

(define benchmark
  (letrec
    ((bquery
      (relation (c1 d1 c2 d2)
	(to-show `(quad ,c1 ,d1 ,c2 ,d2))
	(all
	  (density c1 d1)
	  (density c2 d2)
	  (predicate (d1 d2)
	    (and (> d1 d2)
	      (let ((t1 (* 20 d1))
		    (t2 (* 21 d2)))
		(< t1 t2)))))))
      (density
	(relation (head-let c d)
	  (exists (p)
	    (all
	      (pop  c p)
	      (exists (a)
		(all!!
		  (area c a)
		  (let-inject ((d1 (p a) (* p (/ 100.0 a))))
		    (== d1 d)))))))))
    (lambda (out)
      (bquery out))))

(define benchmark
  (letrec
    ((bquery
      (relation (c1 d1 c2 d2)
	(to-show `(quad ,c1 ,d1 ,c2 ,d2))
	(all
	  (density c1 d1)
	  (density c2 d2)
	  (predicate (d1 d2)
	    (and (> d1 d2)
	      (let ((t1 (* 20 d1))
		    (t2 (* 21 d2)))
		(< t1 t2)))))))
      (density
	(relation (head-let c d)
	  (exists (p)
	    (all
	      (pop  c p)
	      (let-inject ((d1 (c p) 
			     (let ((a (cadr (assoc c area-lst))))
			       (* p (/ 100.0 a)))))
		    (== d1 d)))))))
    (lambda (out)
      (bquery out))))

; populations in 100000s
(define pop
  (extend-relation (a b)
    (fact () "china"		8250)
    (fact () "india"		5863)
    (fact () "ussr"		2521)
    (fact () "usa"		2119)
    (fact () "indonesia"	1276)
    (fact () "japan"		1097)
    (fact () "brazil"		1042)
    (fact () "bangladesh"	 750)
    (fact () "pakistan" 	 682)
    (fact () "w_germany"	 620)
    (fact () "nigeria"		 613)
    (fact () "mexico"		 581)
    (fact () "uk"		 559)
    (fact () "italy"		 554)
    (fact () "france"		 525)
    (fact () "philippines"	 415)
    (fact () "thailand"		 410)
    (fact () "turkey"		 383)
    (fact () "egypt"		 364)
    (fact () "spain"		 352)
    (fact () "poland"		 337)
    (fact () "s_korea"		 335)
    (fact () "iran"		 320)
    (fact () "ethiopia"		 272)
    (fact () "argentina"	 251)
))

; areas in 1000s of square miles
(define area
  (extend-relation (a b)
    (fact () "china"		3380)
    (fact () "india"		1139)
    (fact () "ussr"		8708)
    (fact () "usa"		3609)
    (fact () "indonesia"	 570)
    (fact () "japan"		 148)
    (fact () "brazil"		3288)
    (fact () "bangladesh"	  55)
    (fact () "pakistan"		 311)
    (fact () "w_germany"	  96)
    (fact () "nigeria"		 373)
    (fact () "mexico"		 764)
    (fact () "uk"		  86)
    (fact () "italy"		 116)
    (fact () "france"		 213)
    (fact () "philippines"	  90)
    (fact () "thailand"	         200)
    (fact () "turkey"		 296)
    (fact () "egypt"		 386)
    (fact () "spain"		 190)
    (fact () "poland"		 121)
    (fact () "s_korea"		  37)
    (fact () "iran"		 628)
    (fact () "ethiopia"	         350)
    (fact () "argentina"	1080)
    ))


(define area-lst
  '(("china"		3380)
    ("india"		1139)
    ("ussr"		8708)
    ("usa"		3609)
    ("indonesia"	 570)
    ("japan"		 148)
    ("brazil"		3288)
    ("bangladesh"	  55)
    ("pakistan"		 311)
    ("w_germany"	  96)
    ("nigeria"		 373)
    ("mexico"		 764)
    ("uk"		  86)
    ("italy"		 116)
    ("france"		 213)
    ("philippines"	  90)
    ("thailand"	         200)
    ("turkey"		 296)
    ("egypt"		 386)
    ("spain"		 190)
    ("poland"		 121)
    ("s_korea"		  37)
    ("iran"		 628)
    ("ethiopia"	         350)
    ("argentina"	1080)
    ))

(test-check 'query-benchmark
  (solve 5 (out) (benchmark out))
  '(((out.0 (quad "indonesia" 223.859649122807 "pakistan" 219.2926045016077)))
    ((out.0 (quad "uk" 650.0 "w_germany" 645.8333333333334)))
    ((out.0 (quad "italy" 477.5862068965517 "philippines" 461.11111111111114)))
    ((out.0 (quad "france" 246.4788732394366 "china" 244.08284023668637)))
    ((out.0 (quad "ethiopia" 77.71428571428571 "mexico" 76.04712041884817)))))

; Evaluate the following to see the resulting substitutions
'(query (benchmark _))

(display "Timing per iterations: ") (display benchmark_count) (newline)
'(time (do ((i 0 (+ 1 i))) ((>= i benchmark_count))
	(solve 5 (out) (benchmark out))))

; dobench(Count) :-
; 	data(Data),
; 	repeat(Count),
; 	benchmark(Data, _Result),
; 	fail.
; dobench(_).

