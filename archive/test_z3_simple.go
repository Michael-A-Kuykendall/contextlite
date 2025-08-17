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
	
	// Simple test documents
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
	
	// Simple pair
	pairs := []solve.DocumentPair{
		{
			DocI:             0,
			DocJ:             1,
			Similarity:       0.2,
			RedundancyPenalty: 0.1,
			CoherenceBonus:   0.05,
		},
	}
	
	// Test with generous constraints
	result, err := z3.OptimizeDocumentSelection(
		context.Background(),
		docs,
		pairs,
		1000, // generous token limit
		2,    // can select both docs
	)
	
	if err != nil {
		log.Fatalf("Z3 optimization failed: %v", err)
	}
	
	fmt.Printf("Z3 Result:\n")
	fmt.Printf("  Status: %s\n", result.Status)
	fmt.Printf("  Selected: %v\n", result.SelectedDocs)
	fmt.Printf("  Objective: %d\n", result.ObjectiveValue)
	fmt.Printf("  Variables: %d\n", result.VariableCount)
	fmt.Printf("  Constraints: %d\n", result.ConstraintCount)
	fmt.Printf("  Timeout: %v\n", result.TimedOut)
}
