(set-logic QF_LIA)

; Document selection variables
(declare-fun x0 () Int)
(assert (>= x0 0))
(assert (<= x0 1))
(declare-fun x1 () Int)
(assert (>= x1 0))
(assert (<= x1 1))

; Co-selection variables for top-M pairs
(declare-fun y0_1 () Int)
(assert (>= y0_1 0))
(assert (<= y0_1 1))

; Token budget budget
(assert (<= (+ (* 37 x0) (* 35 x1)) 800))

; Document count budget
(assert (<= (+ x0 x1) 4))

; Linking budgets: y_ij ↔ x_i ∧ x_j
(assert (<= y0_1 x0))
(assert (<= y0_1 x1))
(assert (<= (+ x0 x1 (* -1 y0_1)) 1))

; Objective function
(declare-fun obj () Int)
(assert (= obj (+ (* 2141 x0) (* 2068 x1) (* -1504 y0_1))))

(maximize obj)
(check-sat)
(get-objectives)
(get-model)
