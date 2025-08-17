package main

import (
	"context"
	"fmt"
	"log"
	"strings"

	"contextlite/internal/solve"
	"contextlite/pkg/types"
)

func buildDebugSMTModel(docs []types.ScoredDocument, pairs []solve.DocumentPair, maxTokens int, maxDocs int) string {
	var sb strings.Builder
	integerScale := 10000

	// SMT-LIB2 header
	sb.WriteString("(set-logic QF_LIA)\n\n")

	// Decision variables: x_i for each document
	sb.WriteString("; Document selection variables\n")
	for i := range docs {
		sb.WriteString(fmt.Sprintf("(declare-fun x%d () Int)\n", i))
		sb.WriteString(fmt.Sprintf("(assert (or (= x%d 0) (= x%d 1)))\n", i, i))
	}
	sb.WriteString("\n")

	// Co-selection variables: y_ij for top-M pairs
	if len(pairs) > 0 {
		sb.WriteString("; Co-selection variables for top-M pairs\n")
		for _, pair := range pairs {
			varName := fmt.Sprintf("y%d_%d", pair.DocI, pair.DocJ)
			sb.WriteString(fmt.Sprintf("(declare-fun %s () Int)\n", varName))
			sb.WriteString(fmt.Sprintf("(assert (or (= %s 0) (= %s 1)))\n", varName, varName))
		}
		sb.WriteString("\n")
	}

	// Budget constraint: Σ t_i * x_i ≤ B
	if maxTokens > 0 {
		sb.WriteString("; Token budget constraint\n")
		sb.WriteString("(assert (<= (+")
		for i, doc := range docs {
			sb.WriteString(fmt.Sprintf(" (* %d x%d)", doc.Document.TokenCount, i))
		}
		sb.WriteString(fmt.Sprintf(") %d))\n\n", maxTokens))
	}

	// Cardinality constraint: Σ x_i ≤ D_max
	if maxDocs > 0 {
		sb.WriteString("; Document count constraint\n")
		sb.WriteString("(assert (<= (+")
		for i := range docs {
			sb.WriteString(fmt.Sprintf(" x%d", i))
		}
		sb.WriteString(fmt.Sprintf(") %d))\n\n", maxDocs))
	}

	// Linking constraints: y_ij ≤ x_i, y_ij ≤ x_j, x_i + x_j - y_ij ≤ 1
	if len(pairs) > 0 {
		sb.WriteString("; Linking constraints\n")
		for _, pair := range pairs {
			varName := fmt.Sprintf("y%d_%d", pair.DocI, pair.DocJ)
			sb.WriteString(fmt.Sprintf("(assert (<= %s x%d))\n", varName, pair.DocI))
			sb.WriteString(fmt.Sprintf("(assert (<= %s x%d))\n", varName, pair.DocJ))
			sb.WriteString(fmt.Sprintf("(assert (<= (+ x%d x%d (* -1 %s)) 1))\n", pair.DocI, pair.DocJ, varName))
		}
		sb.WriteString("\n")
	}

	// Objective function: Σ v_i * x_i - Σ r_ij * y_ij + Σ c_ij * y_ij
	sb.WriteString("; Objective function\n")
	sb.WriteString("(declare-fun obj () Int)\n")
	sb.WriteString("(assert (= obj (+")

	// Per-document utility terms
	for i, doc := range docs {
		// Scale utility score to integer (set-independent features only)
		scaledUtility := int(doc.UtilityScore * float64(integerScale))
		sb.WriteString(fmt.Sprintf(" (* %d x%d)", scaledUtility, i))
	}

	// Pairwise penalty/bonus terms
	for _, pair := range pairs {
		varName := fmt.Sprintf("y%d_%d", pair.DocI, pair.DocJ)
		// Net effect: coherence_bonus - redundancy_penalty
		netEffect := int((pair.CoherenceBonus - pair.RedundancyPenalty) * float64(integerScale))
		if netEffect != 0 {
			sb.WriteString(fmt.Sprintf(" (* %d %s)", netEffect, varName))
		}
	}

	sb.WriteString(")))\n\n")

	// Optimization directive
	sb.WriteString("(maximize obj)\n")
	sb.WriteString("(check-sat)\n")
	sb.WriteString("(get-objectives)\n")
	sb.WriteString("(get-model)\n")

	return sb.String()
}

func main() {
	// Simple test documents with higher utility scores
	docs := []types.ScoredDocument{
		{
			Document: types.Document{
				ID:         "doc1",
				Content:    "Test document one",
				TokenCount: 50,
			},
			UtilityScore: 0.8,
		},
		{
			Document: types.Document{
				ID:         "doc2",
				Content:    "Test document two",
				TokenCount: 60,
			},
			UtilityScore: 0.7,
		},
	}
	
	// Simple pair with small penalty
	pairs := []solve.DocumentPair{
		{
			DocI:             0,
			DocJ:             1,
			Similarity:       0.2,
			RedundancyPenalty: 0.05,  // Small penalty
			CoherenceBonus:   0.1,    // Positive bonus
		},
	}
	
	// Generate the SMT model
	smtModel := buildDebugSMTModel(docs, pairs, 200, 2)
	
	fmt.Println("Generated SMT-LIB2 Model:")
	fmt.Println("========================")
	fmt.Println(smtModel)
	
	// Now test with Z3
	z3 := solve.NewZ3Optimizer("C:\\ProgramData\\chocolatey\\bin\\z3.exe", 5000)
	result, err := z3.OptimizeDocumentSelection(
		context.Background(),
		docs,
		pairs,
		200, // should allow both docs (50+60 < 200)
		2,   // can select both docs
	)
	
	if err != nil {
		log.Fatalf("Z3 optimization failed: %v", err)
	}
	
	fmt.Printf("\nZ3 Result:\n")
	fmt.Printf("  Status: %s\n", result.Status)
	fmt.Printf("  Selected: %v\n", result.SelectedDocs)
	fmt.Printf("  Objective: %d\n", result.ObjectiveValue)
}
