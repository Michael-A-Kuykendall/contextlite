package solve

import (
	"context"
	"testing"
	"time"

	"contextlite/pkg/types"
)

func TestZ3Optimizer_RealSMTSolving(t *testing.T) {
	// This test demonstrates real Z3 SMT solving (requires Z3 binary)
	// If Z3 is not available, it will gracefully skip
	
	z3Path := findZ3Binary()
	if z3Path == "" {
		t.Skip("Z3 binary not found, skipping real SMT test")
	}
	
	optimizer := NewZ3Optimizer(z3Path, 5000)
	
	// Create test documents with realistic features
	docs := []types.ScoredDocument{
		{
			Document: types.Document{
				ID:         "doc1",
				Content:    "Machine learning algorithms for data analysis",
				TokenCount: 149,
			},
			UtilityScore: 0.753,
		},
		{
			Document: types.Document{
				ID:         "doc2", 
				Content:    "Deep neural networks and artificial intelligence",
				TokenCount: 123,
			},
			UtilityScore: 0.652,
		},
		{
			Document: types.Document{
				ID:         "doc3",
				Content:    "Statistical methods in machine learning research", 
				TokenCount: 187,
			},
			UtilityScore: 0.598,
		},
	}
	
	// Create pairwise relationships
	pairs := []DocumentPair{
		{
			DocI:             0,
			DocJ:             1,
			Similarity:       0.45,
			RedundancyPenalty: 0.3 * 0.45, // weight * similarity
			CoherenceBonus:   0.2 * 0.45,
		},
		{
			DocI:             0,
			DocJ:             2,
			Similarity:       0.67,
			RedundancyPenalty: 0.3 * 0.67,
			CoherenceBonus:   0.2 * 0.67,
		},
		{
			DocI:             1,
			DocJ:             2,
			Similarity:       0.23,
			RedundancyPenalty: 0.3 * 0.23,
			CoherenceBonus:   0.2 * 0.23,
		},
	}
	
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	
	// Test Z3 optimization
	result, err := optimizer.OptimizeDocumentSelection(ctx, docs, pairs, 400, 2)
	if err != nil {
		t.Fatalf("Z3 optimization failed: %v", err)
	}
	
	// Verify results
	if result.Status != "sat" {
		t.Errorf("Expected sat result, got %s", result.Status)
	}
	
	if len(result.SelectedDocs) == 0 {
		t.Error("No documents selected")
	}
	
	if len(result.SelectedDocs) > 2 {
		t.Errorf("Too many documents selected: %d > 2", len(result.SelectedDocs))
	}
	
	// Verify token constraint
	totalTokens := 0
	for _, idx := range result.SelectedDocs {
		totalTokens += docs[idx].Document.TokenCount
	}
	if totalTokens > 400 {
		t.Errorf("Token constraint violated: %d > 400", totalTokens)
	}
	
	// Log the results for documentation
	t.Logf("Z3 SMT Optimization Results:")
	t.Logf("  Status: %s", result.Status)
	t.Logf("  Selected docs: %v", result.SelectedDocs)
	t.Logf("  Objective value: %d", result.ObjectiveValue)
	t.Logf("  Variable count: %d", result.VariableCount)
	t.Logf("  Constraint count: %d", result.ConstraintCount)
	t.Logf("  Total tokens: %d/400", totalTokens)
	t.Logf("  Timeout: %t", result.TimedOut)
	
	// Cross-verify objective computation
	expectedObjective := computeExpectedObjective(docs, pairs, result.SelectedDocs)
	scaledExpected := int(expectedObjective * 10000) // Match Z3 scaling
	
	// Allow small rounding differences
	diff := result.ObjectiveValue - scaledExpected
	if diff < 0 {
		diff = -diff
	}
	if diff > 10 { // Allow up to 10 units difference due to rounding
		t.Errorf("Objective mismatch: Z3=%d, computed=%d, diff=%d", 
			result.ObjectiveValue, scaledExpected, diff)
	}
}

// findZ3Binary attempts to locate Z3 binary in common locations
func findZ3Binary() string {
	candidates := []string{
		"z3",
		"/usr/bin/z3",
		"/usr/local/bin/z3",
		"C:\\Program Files\\Microsoft Research\\Z3-4.8.17\\bin\\z3.exe",
		"z3.exe",
	}
	
	for _, path := range candidates {
		if err := CheckZ3Available(path); err == nil {
			return path
		}
	}
	return ""
}

// computeExpectedObjective computes the expected objective value in Go
func computeExpectedObjective(docs []types.ScoredDocument, pairs []DocumentPair, selected []int) float64 {
	selectedSet := make(map[int]bool)
	for _, idx := range selected {
		selectedSet[idx] = true
	}
	
	objective := 0.0
	
	// Per-document utilities
	for _, idx := range selected {
		objective += docs[idx].UtilityScore
	}
	
	// Pairwise effects
	for _, pair := range pairs {
		if selectedSet[pair.DocI] && selectedSet[pair.DocJ] {
			objective += pair.CoherenceBonus - pair.RedundancyPenalty
		}
	}
	
	return objective
}

func TestZ3Optimizer_PairwisePenaltyEffects(t *testing.T) {
	// Test that high redundancy penalty prevents co-selection
	z3Path := findZ3Binary()
	if z3Path == "" {
		t.Skip("Z3 binary not found, skipping pairwise penalty test")
	}
	
	optimizer := NewZ3Optimizer(z3Path, 5000)
	
	// Two similar documents with high redundancy penalty
	docs := []types.ScoredDocument{
		{
			Document:     types.Document{ID: "doc1", TokenCount: 100},
			UtilityScore: 0.8,
		},
		{
			Document:     types.Document{ID: "doc2", TokenCount: 100},
			UtilityScore: 0.8,
		},
	}
	
	pairs := []DocumentPair{
		{
			DocI:             0,
			DocJ:             1,
			Similarity:       0.95,
			RedundancyPenalty: 1.5 * 0.95, // VERY high penalty (exceeds individual utility)
			CoherenceBonus:   0.1 * 0.95,  // Low bonus
		},
	}
	
	ctx := context.Background()
	
	// Should select only one document due to high redundancy penalty
	result, err := optimizer.OptimizeDocumentSelection(ctx, docs, pairs, 1000, 2)
	if err != nil {
		t.Fatalf("Z3 optimization failed: %v", err)
	}
	
	if len(result.SelectedDocs) != 1 {
		t.Errorf("Expected 1 document due to redundancy penalty, got %d", len(result.SelectedDocs))
	}
	
	t.Logf("Redundancy penalty test: selected %d documents (expected 1)", len(result.SelectedDocs))
}
