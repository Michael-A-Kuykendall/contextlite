package main

import (
	"context"
	"fmt"
	"os/exec"
	"strings"
)

func main() {
	smtModel := `(set-logic QF_LIA)

; Document selection variables
(declare-fun x0 () Int)
(assert (or (= x0 0) (= x0 1)))
(declare-fun x1 () Int)
(assert (or (= x1 0) (= x1 1)))

; Co-selection variables for top-M pairs
(declare-fun y0_1 () Int)
(assert (or (= y0_1 0) (= y0_1 1)))

; Token budget constraint
(assert (<= (+ (* 50 x0) (* 60 x1)) 200))

; Document count constraint
(assert (<= (+ x0 x1) 2))

; Linking constraints
(assert (<= y0_1 x0))
(assert (<= y0_1 x1))
(assert (<= (+ x0 x1 (* -1 y0_1)) 1))

; Objective function
(declare-fun obj () Int)
(assert (= obj (+ (* 8000 x0) (* 7000 x1) (* 500 y0_1))))

(maximize obj)
(check-sat)
(get-objectives)
(get-model)`

	// Create Z3 command
	cmd := exec.CommandContext(context.Background(), "C:\\ProgramData\\chocolatey\\bin\\z3.exe", "-in")
	cmd.Stdin = strings.NewReader(smtModel)

	// Run Z3 and capture output
	output, err := cmd.Output()
	if err != nil {
		fmt.Printf("Error: %v\n", err)
		return
	}

	fmt.Printf("Raw Z3 Output:\n")
	fmt.Printf("==============\n")
	fmt.Printf("%s\n", string(output))
	fmt.Printf("==============\n")
	
	// Show line by line
	lines := strings.Split(string(output), "\n")
	fmt.Printf("Lines (%d total):\n", len(lines))
	for i, line := range lines {
		fmt.Printf("%2d: '%s'\n", i, line)
	}
}
