(set-logic QF_S)

(define-funs-rec ((extract1st ((x String) (y String)) Bool)
                   (extract1st_2 ((x String) (y String)) Bool)
                   (extract1st_3 ((x String) (y String)) Bool)) (
    ;
    ; extract1st
    (or (and (= x "") (= y ""))
        (and (not (= (seq-head x) (_ bv60 8)))  ; not '='
             (extract1st (seq-tail x) (seq-tail y)))
        (and (= (seq-head x) (_ bv60 8))        ; '='
             (extract1st_2 x (seq-tail y))))
    ;
    ; extract1st_2
    (or (and (= x "") (= y ""))
        (and (= (seq-head x) (seq-head y))
             (not (= (seq-head x) (_ bv61 8)))  ; not '='
             (extract1st_2 (seq-tail x) (seq-tail y)))
        (and (= (seq-head x) (_ bv61 8))        ; '='
             (extract1st_3 (seq-tail x) y)))
    ;
    ; extract1st_3
    (or (and (= x "") (= y ""))
        (extract1st_3 (seq-tail x) y))
    ;
  ))

(declare-fun x () String)
(declare-fun y () String)
(assert (= x "<abc>"))
(assert (extract1st x y))
(assert (= y "abc>"))

(check-sat)
