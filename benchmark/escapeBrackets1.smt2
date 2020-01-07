(set-logic QF_S)

(define-fun-rec escapeBrackets ((x String) (y String)) Bool
  (or (and (= x "") (= y ""))
      (and (= (seq-head x) (_ bv60 8))
           (and (= (seq-head y) (_ bv38 8))
                (escapeBrackets (seq-tail x) (seq-tail y))))
      (and (not (= (seq-head x) (_ bv60 8)))
           (escapeBrackets (seq-tail x) (seq-tail y)))
  )
)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x "<abc>"))
(assert (escapeBrackets x y))
(assert (= y "&abc>"))

(check-sat)
