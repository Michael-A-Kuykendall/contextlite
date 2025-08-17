package main

import (
	"context"
	"fmt"
	"log"

	"contextlite/internal/solve"
	"contextlite/pkg/types"
)

func main() {
	// Create Z3 optimizer
	z3 := solve.NewZ3Optimizer("C:\\ProgramData\\chocolatey\\bin\\z3.exe", 5000)
	
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
	
	fmt.Printf("Input Data:\n")
	for i, doc := range docs {
		fmt.Printf("  Doc %d: utility=%.3f, tokens=%d\n", i, doc.UtilityScore, doc.Document.TokenCount)
	}
	for _, pair := range pairs {
		fmt.Printf("  Pair %d-%d: redundancy=%.3f, coherence=%.3f, net=%.3f\n", 
			pair.DocI, pair.DocJ, pair.RedundancyPenalty, pair.CoherenceBonus,
			pair.CoherenceBonus - pair.RedundancyPenalty)
	}
	
	// Test with generous constraints
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
	fmt.Printf("  Objective: %d (scaled by 10000)\n", result.ObjectiveValue)
	fmt.Printf("  Objective (real): %.4f\n", float64(result.ObjectiveValue)/10000.0)
	fmt.Printf("  Variables: %d\n", result.VariableCount)
	fmt.Printf("  Constraints: %d\n", result.ConstraintCount)
	fmt.Printf("  Timeout: %v\n", result.TimedOut)
	
	// Calculate expected objective if both selected
	if len(result.SelectedDocs) >= 2 {
		expectedObj := docs[0].UtilityScore + docs[1].UtilityScore + (pairs[0].CoherenceBonus - pairs[0].RedundancyPenalty)
		fmt.Printf("  Expected both: %.4f\n", expectedObj)
	}
}
