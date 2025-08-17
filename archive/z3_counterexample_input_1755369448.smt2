(set-logic QF_LIA)

; Document selection variables
(declare-fun x0 () Int)
(assert (>= x0 0))
(assert (<= x0 1))
(declare-fun x1 () Int)
(assert (>= x1 0))
(assert (<= x1 1))
(declare-fun x2 () Int)
(assert (>= x2 0))
(assert (<= x2 1))

; Co-selection variables for top-M pairs
(declare-fun y0_1 () Int)
(assert (>= y0_1 0))
(assert (<= y0_1 1))
(declare-fun y1_2 () Int)
(assert (>= y1_2 0))
(assert (<= y1_2 1))
(declare-fun y0_2 () Int)
(assert (>= y0_2 0))
(assert (<= y0_2 1))

; Document count budget
(assert (<= (+ x0 x1 x2) 2))

; Linking budgets: y_ij ↔ x_i ∧ x_j
(assert (<= y0_1 x0))
(assert (<= y0_1 x1))
(assert (<= (+ x0 x1 (* -1 y0_1)) 1))
(assert (<= y1_2 x1))
(assert (<= y1_2 x2))
(assert (<= (+ x1 x2 (* -1 y1_2)) 1))
(assert (<= y0_2 x0))
(assert (<= y0_2 x2))
(assert (<= (+ x0 x2 (* -1 y0_2)) 1))

; Objective function
(declare-fun obj () Int)
(assert (= obj (+ (* 1896 x0) (* 2555 x1) (* 2403 x2) (* -691 y0_1) (* -403 y1_2) (* -1107 y0_2))))

(maximize obj)
(check-sat)
(get-objectives)
(get-model)
