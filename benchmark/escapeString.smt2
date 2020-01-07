(set-logic QF_S)

(define-fun-rec escapeBrackets ((x String) (y String)) Bool
  (or (and (= x "") (= y ""))
      (and (= (seq-head y)
              (ite (= (seq-head x) (_ bv60 8))
                   ("&lt;")
                   (ite (= (seq-head x) (_ bv62 8))
                        ("&gt;")
                        (seq-head x)))
           (toUpper (seq-tail x) (seq-tail y))))
  )

(declare-fun x () String)
(declare-fun y () String)

(assert (= x "<abc>"))
(assert (toUpper x y))
(assert (not (= y "&lt;abc&gt;")))

(check-sat)
