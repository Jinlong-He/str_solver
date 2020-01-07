(set-logic QF_S)
(define-funs-rec ((extract1st ((x String) (y String)) Bool)
                   (extract1st_2 ((x String) (y String)) Bool)) (
    ;
    ; extract1st
    (or (and (= x "") (= y ""))
        (and (= (seq-head x) (_ bv97 8))        ; '='
         (and (= (seq-head y) (_ bv98 8))     
         (extract1st_2 x (seq-tail y))))
        (and (not (= (seq-head x) (_ bv97 8)))  ; not '='
         (and (= (seq-head y) (seq-head x))
             (extract1st (seq-tail x) (seq-tail y)))))
    ;
    ; extract1st_2
    (or (and (= x "") (= y ""))
     (and (= (seq-head y) (_ bv99 8)) 
             (extract1st (seq-tail x) (seq-tail y))))))

(declare-fun x () String)
(declare-fun y () String)

(assert (= x "ab"))
(assert (extract1st x y))
(assert (= y "bcb"))

(check-sat)
