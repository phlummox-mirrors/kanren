(display "Zebra") (newline)

;   1. There are five houses in a row, each of a different color
;       and inhabited by men of different nationalities,
;       with different pets, drinks, and cigarettes.
;   2. The Englishman lives in the red house.
;   3. The Spaniard owns a dog.
;   4. Coffee is drunk in the green house.
;   5. The Ukrainian drinks tea.
;   6. The green house is directly to the right of the ivory house.
;   7. The Old Gold smoker owns snails.
;   8. Kools are being smoked in the yellow house.
;   9. Milk is drunk in the middle house.
;  10. The Norwegian lives in the first house on the left.
;  11. The Chesterfield smoker lives next to the fox owner.
;  12. Kools are smoked in the house next to the house where the horse is kept.
;  13. The Lucky Strike smoker drinks orange juice.
;  14. The Japanese smokes Parliaments.
;  15. The Norwegian lives next to the blue house.

(define member 
  (extend-relation (a1 a2)
    (fact (item) item `(,item . ,_))
    (relation (item rest) (to-show item `(,_ . ,rest)) (member item rest))))

(define next-to
  (relation (item1 item2 rest)
    (to-show item1 item2 rest)
    (any (on-right item1 item2 rest) (on-right item2 item1 rest))))

(define on-right
  (extend-relation (a0 a1 a2)
    (fact (item1 item2) item1 item2 `(,item1 ,item2 . ,_))
    (relation (item1 item2 rest)
      (to-show item1 item2 `(,_ . ,rest))
      (on-right item1 item2 rest))))
        
(define zebra
  (relation (h)
    (to-show h)
    (if-all!
      ((== h `((norwegian ,_ ,_ ,_ ,_) ,_ (,_ ,_ milk ,_ ,_) ,_ ,_))
       (member `(englishman ,_ ,_ ,_ red) h)
       (on-right `(,_ ,_ ,_ ,_ ivory) `(,_ ,_ ,_ ,_ green) h)
       (next-to `(norwegian ,_ ,_ ,_ ,_) `(,_ ,_ ,_ ,_ blue) h)
       (member `(,_ kools ,_ ,_ yellow) h)
       (member `(spaniard ,_ ,_ dog ,_) h)
       (member `(,_ ,_ coffee ,_ green) h) 
       (member `(ukrainian ,_ tea ,_ ,_) h)
       (member `(,_ luckystrikes oj ,_ ,_) h)
       (member `(japanese parliaments ,_ ,_ ,_) h)
       (member `(,_ oldgolds ,_ snails ,_) h)
       (next-to `(,_ ,_ ,_ horse ,_) `(,_ kools ,_ ,_ ,_) h)
       (next-to `(,_ ,_ ,_ fox ,_) `(,_ chesterfields ,_ ,_ ,_) h)
      )
      (all (member `(,_ ,_ water ,_ ,_) h)
	(member `(,_ ,_ ,_ zebra ,_) h)))))


(test-check "Zebra"
  (time (solution (h) (zebra h)))
  '((h.0 ((norwegian kools water fox yellow)
          (ukrainian chesterfields tea horse blue)
          (englishman oldgolds milk snails red)
          (spaniard luckystrikes oj dog ivory)
          (japanese parliaments coffee zebra green)))))

; Sample timing (Pentium IV, 2GHz, 1GB RAM)
; (time (solution (h) ...))
;     1 collection
;     22 ms elapsed cpu time, including 0 ms collecting
;     27 ms elapsed real time, including 0 ms collecting
;     981560 bytes allocated, including 1066208 bytes reclaimed

; For version 3.16 of kanren.ss
;    1 collection
;    25 ms elapsed cpu time, including 1 ms collecting
;    1082952 bytes allocated, including 1041640 bytes reclaimed
