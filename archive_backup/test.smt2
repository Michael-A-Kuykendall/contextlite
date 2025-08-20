(set-logic QF_LIA)

; Document selection variables
(declare-fun x0 () Int)
(assert (or (= x0 0) (= x0 1)))
(declare-fun x1 () Int)
(assert (or (= x1 0) (= x1 1)))

; Co-selection variables for top-M pairs
(declare-fun y0_1 () Int)
(assert (or (= y0_1 0) (= y0_1 1)))

; Token budget budget
(assert (<= (+ (* 50 x0) (* 60 x1)) 200))

; Document count budget
(assert (<= (+ x0 x1) 2))

; Linking budgets
(assert (<= y0_1 x0))
(assert (<= y0_1 x1))
(assert (<= (+ x0 x1 (* -1 y0_1)) 1))

; Objective function
(declare-fun obj () Int)
(assert (= obj (+ (* 8000 x0) (* 7000 x1) (* 500 y0_1))))

(maximize obj)
(check-sat)
(get-objectives)
(get-model)
