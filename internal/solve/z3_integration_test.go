package solve

import (
	"context"
	"fmt"
	"strings"
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

func TestZ3Optimizer_ErrorHandling(t *testing.T) {
	// Test with invalid Z3 path
	invalidOptimizer := NewZ3Optimizer("/nonexistent/z3/binary", 5000)
	
	docs := []types.ScoredDocument{
		{
			Document: types.Document{
				ID:         "1",
				Content:    "test content",
				TokenCount: 50,
			},
			UtilityScore: 0.8,
		},
	}
	
	ctx := context.Background()
	_, err := invalidOptimizer.OptimizeDocumentSelection(ctx, docs, nil, 100, 1)
	
	// Should handle the error gracefully (might return fallback or error)
	if err == nil {
		t.Log("Invalid Z3 path handled gracefully with fallback")
	} else {
		t.Logf("Invalid Z3 path properly returned error: %v", err)
	}
}

func TestZ3Optimizer_TimeoutHandling(t *testing.T) {
	err := CheckZ3Available("z3")
	if err != nil {
		t.Skip("Z3 not available for timeout testing")
	}
	
	optimizer := NewZ3Optimizer("z3", 1) // Very short timeout
	
	// Create a more complex problem that might timeout
	docs := make([]types.ScoredDocument, 10)
	for i := 0; i < 10; i++ {
		docs[i] = types.ScoredDocument{
			Document: types.Document{
				ID:         fmt.Sprintf("doc%d", i),
				Content:    fmt.Sprintf("Content %d with various words", i),
				TokenCount: 100 + i*10,
			},
			UtilityScore: 0.5 + float64(i)*0.05,
		}
	}
	
	pairs := make([]DocumentPair, 0)
	for i := 0; i < len(docs); i++ {
		for j := i + 1; j < len(docs); j++ {
			pairs = append(pairs, DocumentPair{
				DocI: i, DocJ: j, 
				Similarity: 0.5,
				RedundancyPenalty: 500,
				CoherenceBonus: 100,
			})
		}
	}
	
	// Use very short timeout
	ctx, cancel := context.WithTimeout(context.Background(), 1*time.Millisecond)
	defer cancel()
	
	result, err := optimizer.OptimizeDocumentSelection(ctx, docs, pairs, 500, 5)
	if err != nil {
		t.Logf("Timeout handling test returned error (expected): %v", err)
	} else if result.TimedOut {
		t.Log("Timeout properly detected and handled")
	} else {
		t.Log("Problem solved quickly despite short timeout")
	}
}

func TestCheckZ3Available_EdgeCases(t *testing.T) {
	// Test with empty path
	err := CheckZ3Available("")
	if err != nil {
		t.Logf("Empty Z3 path properly returns error: %v", err)
	}
	
	// Test with non-existent path
	err = CheckZ3Available("/nonexistent/binary")
	if err != nil {
		t.Logf("Non-existent Z3 path properly returns error: %v", err)
	}
	
	// Test with custom Z3 path
	customOptimizer := NewZ3Optimizer("/custom/z3/path", 5000)
	if customOptimizer.z3Path == "/custom/z3/path" {
		t.Log("Custom Z3 path properly set")
	}
}

func TestCheckZ3Available_Comprehensive(t *testing.T) {
	// Test case 1: Empty path
	t.Run("empty_path", func(t *testing.T) {
		err := CheckZ3Available("")
		if err == nil {
			t.Error("CheckZ3Available should return error for empty path")
		}
		t.Logf("Empty path error: %v", err)
	})
	
	// Test case 2: Non-existent binary
	t.Run("nonexistent_binary", func(t *testing.T) {
		err := CheckZ3Available("/definitely/does/not/exist/z3")
		if err == nil {
			t.Error("CheckZ3Available should return error for non-existent binary")
		}
		
		expectedSubstring := "Z3 not found"
		if !strings.Contains(err.Error(), expectedSubstring) {
			t.Errorf("Error should contain '%s', got: %v", expectedSubstring, err)
		}
		t.Logf("Non-existent binary error: %v", err)
	})
	
	// Test case 3: Invalid binary (not Z3)
	t.Run("invalid_binary", func(t *testing.T) {
		// Try with a known system binary that's not Z3 (like 'echo' on Unix or 'cmd' on Windows)
		invalidBinaries := []string{
			"/bin/echo",     // Unix
			"/usr/bin/echo", // Unix
			"echo",          // May work if in PATH
			"cmd",           // Windows
			"notepad",       // Windows
		}
		
		for _, binary := range invalidBinaries {
			err := CheckZ3Available(binary)
			if err != nil {
				// This is expected - the binary exists but doesn't output "Z3" on -version
				if strings.Contains(err.Error(), "invalid Z3 binary") {
					t.Logf("Correctly identified invalid Z3 binary %s: %v", binary, err)
					return // Found one that works for this test
				} else {
					t.Logf("Binary %s not found or other error: %v", binary, err)
				}
			}
		}
		t.Log("No suitable invalid binary found for testing")
	})
	
	// Test case 4: Try with actual Z3 if available
	t.Run("real_z3", func(t *testing.T) {
		z3Path := findZ3Binary()
		if z3Path == "" {
			t.Skip("Z3 binary not found, skipping real Z3 test")
		}
		
		err := CheckZ3Available(z3Path)
		if err != nil {
			t.Errorf("CheckZ3Available should succeed with real Z3 binary: %v", err)
		} else {
			t.Logf("Successfully verified Z3 at: %s", z3Path)
		}
	})
	
	// Test case 5: Path with spaces and special characters
	t.Run("special_path", func(t *testing.T) {
		specialPaths := []string{
			"/path with spaces/z3",
			"/path-with-dashes/z3",
			"/path_with_underscores/z3",
			"./relative/path/z3",
		}
		
		for _, path := range specialPaths {
			err := CheckZ3Available(path)
			if err != nil {
				t.Logf("Special path %s properly returns error: %v", path, err)
			}
		}
	})
}
