;(load "scheduling.scm")
(load "book-si.scm")

(define-syntax test-check
   (syntax-rules ()
     ((_ title tested-expression expected-result)
      (begin
        (printf "Testing ~s~n" title)
        (let* ((expected expected-result)
               (produced tested-expression))
          (or (equal? expected produced)
              (error 'test-check
                     "Failed: ~a~%Expected: ~a~%Computed: ~a"
                     'tested-expression expected produced)))))))


'(define-syntax allw
  (syntax-rules ()
    ((_ arg ...) (all arg ...))))

(define-syntax allw
  (syntax-rules ()
    ((_ arg ...) (all succeed (begin (yield) arg) ...))))

'(define-syntax anyw
  (syntax-rules ()
    ((_ arg ...) (conde (arg) ...))))

(define-syntax anyw
  (syntax-rules ()
    ((_ arg ...) (conde (fail) ((begin (yield) arg)) ...))))

(define any*
   (lambda (g)
     (anyw
       (allw g succeed)
       (any* g))))


(define always (any* succeed))
(define never (any* fail))


;;------------------------------------------------------------------------ 



(define nullo
   (lambda (x)
     (== '() x)))

(define caro
   (lambda (ls a)
     (fresh (d)
       (== (cons a d) ls))))

(define cdro
   (lambda (ls d)
     (fresh (a)
       (== (cons a d) ls))))

(define conso
   (lambda (a d ls)
     (== (cons a d) ls)))



(define appendw
   (lambda (l1 l2 out)
     (anyw
       (allw (nullo l1) (== l2 out))
       (fresh (a d res)
         (allw
           (allw
             (conso a d l1)
             (conso a res out))
           (appendw d l2 res))))))

(define appendo
   (lambda (l1 l2 out)
     (any
       (all (nullo l1) (== l2 out))
       (fresh (a d res)
         (all
           (all
             (conso a d l1)
             (conso a res out))
           (appendo d l2 res))))))

(define swappendw
   (lambda (l1 l2 out)
     (anyw
       (fresh (a d res)
         (allw
           (allw
             (conso a d l1)
             (conso a res out))
           (swappendw d l2 res)))
       (allw (nullo l1) (== l2 out)))))


(define foo
   (lambda (x)
     (allw
       (== 5 x)
       (foo x))))

(define bar
   (lambda (x)
     (allw
       (bar x)
       (== 5 x))))


(define baz
   (lambda (x)
     (anyw
       (== 5 x)
       (baz x))))

(define bat
   (lambda (x)
     (anyw
       (bat x)
       (== 5 x))))


(define quux
   (lambda (x)
     (allw
       (== 5 x)
       (allw
         (quux x)
         (quux x)))))

(define quuux
   (lambda (x)
     (allw
       (quuux x)
       (allw
         (quuux x)
         (== 5 x)))))

(define blat
   (lambda (x)
     (allw
       (allw
         (blat x)
         (blat x))
       (== 5 x))))


(define blaz
   (lambda (x)
     (anyw
       (== 5 x)
       (anyw
         (blaz x)
         (blaz x)))))

(define flaz
   (lambda (x)
     (anyw
       (flaz x)
       (anyw
         (flaz x)
         (== 5 x)))))

(define glaz
   (lambda (x)
     (anyw
       (anyw
         (glaz x)
         (glaz x))
       (== 5 x))))



;;; anyw/allw tests


(test-check "allw-2"
   (run* (q) (allw fail always))
   '())


(test-check "allw-3"
   (run* (q) (allw (== q 3) (== q 3)))
   '(3))

(test-check "allw-4"
   (run* (q) (allw (== q 3) (== q 4)))
   '())


(test-check "anyw-1"
   (run 1 (q) (anyw never succeed))
   '(_.0))

(test-check "anyw-2"
   (run 1 (q) (anyw succeed never))
   '(_.0))


(test-check "appendw-1"
   (run* (q)
     (appendw '(a b c) '(d e) q))
   '((a b c d e)))


(test-check "swappendw-1"
   (run* (q)
     (swappendw '(a b c) '(d e) q))
   '((a b c d e)))


(test-check "baz-1"
   (run 1 (q)
     (baz q))
   '(5))

;!!!!
(test-check "bat-1"
   (run 1 (q)
     (bat q))
   '(5))




(test-check "foo-1"
   (run 1 (q)
     (foo 6))
   '())

(test-check "foo-2"
   (run* (q)
     (foo 6))
   '())

;!!!
'(test-check "bar-1"
   (run 1 (q)
     (bar 6))
   '())

;!!!
'(test-check "bar-2"
   (run* (q)
     (bar 6))
   '())



(test-check "quux-1"
   (run* (q)
     (quux 6))
   '())

;!!!
'(test-check "quuux-1"
   (run* (q)
     (quuux 6))
   '())

;!!!
'(test-check "blat-1"
   (run* (q)
     (blat 6))
   '())


(test-check "blaz-1"
   (run 1 (q)
     (blaz q))
   '(5))

(test-check "blaz-2"
   (run 5 (q)
     (blaz q))
   '(5 5 5 5 5))

;!!!
(test-check "glaz-1"
   (run 1 (q)
     (glaz q))
   '(5))

;!!!
(test-check "glaz-2"
   (run 5 (q)
     (glaz q))
   '(5 5 5 5 5))

;!!!
(test-check "flaz-1"
   (run 1 (q)
     (flaz q))
   '(5))
;!!!
; it passes if the queue size is set to 10
(test-check "flaz-2"
   (run 5 (q)
     (flaz q))
   '(5 5 5 5 5))


(test-check "appendw-1"
   (run 5 (x)
     (fresh (y z)
       (appendw x y z)))
   '(()
     (_.0)
     (_.0 _.1)
     (_.0 _.1 _.2)
     (_.0 _.1 _.2 _.3)))


(test-check "appendw-2"
   (run 5 (q)
     (fresh (x y z)
       (appendw x y z)
       (== `(,x ,y ,z) q)))
   '((() _.0 _.0)
     ((_.0) _.1 (_.0 . _.1))
     ((_.0 _.1) _.2 (_.0 _.1 . _.2))
     ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
     ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))))



(test-check "swappendw-1"
   (run 5 (x)
     (fresh (y z)
       (swappendw x y z)))
   '(()
     (_.0)
     (_.0 _.1)
     (_.0 _.1 _.2)
     (_.0 _.1 _.2 _.3)))

;;; Might give answers back in a different order.
(test-check "swappendw-2"
   (run 5 (q)
     (fresh (x y z)
       (swappendw x y z)
       (== `(,x ,y ,z) q)))
   '((() _.0 _.0)
     ((_.0) _.1 (_.0 . _.1))
     ((_.0 _.1) _.2 (_.0 _.1 . _.2))
     ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
     ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))))

