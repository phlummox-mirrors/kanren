; LIPS benchmark -- logical inferences per second
;
; Do the dumy inverse of a list of 30 elements
;
; nrev([],[]).
; nrev([X|Rest],Ans) :- nrev(Rest,L), extend(L,[X],Ans).

; extend([],L,L).
; extend([X|L1],L2,[X|L3]) :- extend(L1,L2,L3).


; data([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
;                            21,22,23,24,25,26,27,28,29,30]).

; $Id$


(define nrev
  (extend-relation (a1 a2)
    (fact () '() '())
    (relation (x rest ans)
      (to-show `(,x . ,rest) ans)
      (exists (ls)
        (all
          (nrev rest ls)
          (concat ls `(,x) ans))))))

(let ((lst '(1 2 3 4 5 6 7 8 9
              10 11 12 13 14 15 16 17 18
              19 20 21 22 23 24 25 26 27
              28 29 30)))
  (test-check 'test-nrev
    (time
      (solution (x) (nrev lst x)))
    `((x.0 ,(reverse lst)))))

(define get_cpu_time
  (lambda ()
    (vector-ref (statistics) 1)))

(define lots
  (extend-relation ()
    (relation ()
      (to-show)
      (exists (count)
        (all
          (predicate (newline))
          (predicate (newline))
          (eg_count count)
          (bench count)
          fail)))
    (fact ())))

(define test-lots
  (lambda ()
    (solve 1000 () (lots))))

(define eg_count
  (extend-relation (a1)
    (fact () 10)
    (fact () 20)
    (fact () 50)
    (fact () 100)
    (fact () 200)
    (fact () 500)
    (fact () 1000)
    (fact () 2000)
    (fact () 5000)
    (fact () 10000)))

(define bench
  (relation (count)
    (to-show count)
    (let ([t0 (get_cpu_time)])
      (dodummy count)
      (let ([t1 (get_cpu_time)])
        (dobench count)
        (let ([t2 (get_cpu_time)])
          (report count t0 t1 t2))))))

(define dobench
  (extend-relation (a1)
    (relation (count)
      (to-show count)
      (all
	(repeat count)
	(nrev '(1 2 3 4 5 6 7 8 9
		 10 11 12 13 14 15 16 17 18
		 19 20 21 22 23 24 25 26 27
		 28 29 30)
	  _)
	fail))
    (fact () _)))

(define dodummy
  (extend-relation (a1)
    (relation (count)
      (to-show count)
      (all
	(repeat count)
	(dummy _)
	fail))
    (fact () _)))

(define dummy
  (relation ()
    (to-show _)))

(define repeat
  (extend-relation (a1)
    (fact (n) n)
    (relation (n)
      (to-show n)
      (project (n)
        (all (> n 1) (repeat (- n 1)))))))

(define report
  (relation (count t0 t1 t2)
    (to-show count t0 t1 t2)
    (exists (lips units)
      (project (t0 t1 t2)
        (let ([time1 (- t1 t0)]
              [time2 (- t2 t1)])
          (let ([time (- time2 time1)])
            (all
              (calculate_lips count time lips units)
              (project (lips count)
                (predicate (printf "~n~s lips for ~s" lips count)))
              (project (units)
                (predicate
                  (printf " Iterations taking ~s  ~s ( ~s )~n " time units time))))))))))

(define calculate_lips
  (extend-relation (a1 a2 a3 a4)
    (relation (count time lips)
      (to-show count time lips 'msecs)
      (if-only (== time 0) (== lips 0)
        (project (count time)
          (let ([t1 (* 496 count 1000)]
		[t2 (+ time 0.0)])
            (== lips (/ t1 t2))))))))

;(test-lots)
