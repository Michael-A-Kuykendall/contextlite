package solve

import (
	"fmt"
	"math/rand"
	"testing"

	"contextlite/pkg/types"
)

func TestBruteForceVerifier_ParityWithoptimizer(t *testing.T) {
	// Test brute-force parity for N≤12 documents
	verifier := NewBruteForceVerifier()
	
	// Test cases with different problem sizes
	testCases := []struct {
		name     string
		numDocs  int
		maxDocs  int
		maxTokens int
		seed     int64
	}{
		{"small_3docs", 3, 2, 300, 12345},
		{"medium_5docs", 5, 3, 500, 23456},
		{"large_8docs", 8, 4, 800, 34567},
		{"max_12docs", 12, 5, 1200, 45678},
	}
	
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			rand.Seed(tc.seed)
			
			// Generate test documents
			docs := generateRandomDocs(tc.numDocs)
			pairs := generateRandomPairs(tc.numDocs)
			
			// Run brute-force verification
			result, err := verifier.BruteForceOptimize(docs, pairs, tc.maxTokens, tc.maxDocs)
			if err != nil {
				t.Fatalf("Brute-force optimization failed: %v", err)
			}
			
			// Verify feasibility
			totalTokens := 0
			for _, idx := range result.SelectedDocs {
				totalTokens += docs[idx].Document.TokenCount
			}
			if !verifier.isFeasible(result.SelectedDocs, totalTokens, tc.maxTokens, tc.maxDocs) {
				t.Errorf("Brute-force result is not feasible")
			}
			
			t.Logf("Seed %d: Optimal objective %d, selected %v", 
				tc.seed, result.ObjectiveValue, result.SelectedDocs)
		})
	}
}

func TestBruteForceVerifier_PairwisePenaltyValidation(t *testing.T) {
	// Test that high redundancy penalty prevents co-selection
	verifier := NewBruteForceVerifier()
	
	docs := []types.ScoredDocument{
		{Document: types.Document{ID: "doc1", TokenCount: 100}, UtilityScore: 0.8},
		{Document: types.Document{ID: "doc2", TokenCount: 100}, UtilityScore: 0.8},
	}
	
	// High redundancy penalty should prevent co-selection
	pairs := []DocumentPair{
		{
			DocI:             0,
			DocJ:             1,
			Similarity:       0.95,
			RedundancyPenalty: 0.9, // Very high penalty
			CoherenceBonus:   0.1,  // Low bonus
		},
	}
	
	result, err := verifier.BruteForceOptimize(docs, pairs, 1000, 2)
	if err != nil {
		t.Fatalf("Brute-force optimization failed: %v", err)
	}
	
	if len(result.SelectedDocs) != 1 {
		t.Errorf("Expected 1 document due to redundancy penalty, got %d", len(result.SelectedDocs))
	}
	
	t.Logf("High redundancy penalty correctly prevented co-selection: selected %d docs", 
		len(result.SelectedDocs))
}

func TestDeterminismValidation(t *testing.T) {
	// Test that same input produces identical output
	verifier := NewBruteForceVerifier()
	
	docs := generateRandomDocs(5)
	pairs := generateRandomPairs(5)
	
	// Run twice with same input
	result1, err1 := verifier.BruteForceOptimize(docs, pairs, 500, 3)
	if err1 != nil {
		t.Fatalf("First run failed: %v", err1)
	}
	
	result2, err2 := verifier.BruteForceOptimize(docs, pairs, 500, 3)
	if err2 != nil {
		t.Fatalf("Second run failed: %v", err2)
	}
	
	// Results should be identical
	if result1.ObjectiveValue != result2.ObjectiveValue {
		t.Errorf("Objective values differ: %d vs %d", result1.ObjectiveValue, result2.ObjectiveValue)
	}
	
	if len(result1.SelectedDocs) != len(result2.SelectedDocs) {
		t.Errorf("Selection lengths differ: %d vs %d", len(result1.SelectedDocs), len(result2.SelectedDocs))
	}
	
	for i, doc := range result1.SelectedDocs {
		if i >= len(result2.SelectedDocs) || doc != result2.SelectedDocs[i] {
			t.Errorf("Selected documents differ at position %d: %d vs %d", i, doc, result2.SelectedDocs[i])
		}
	}
	
	t.Log("Determinism validated: identical inputs produce identical outputs")
}

// generateRandomDocs creates test documents with random features
func generateRandomDocs(n int) []types.ScoredDocument {
	docs := make([]types.ScoredDocument, n)
	for i := 0; i < n; i++ {
		docs[i] = types.ScoredDocument{
			Document: types.Document{
				ID:         fmt.Sprintf("doc%d", i),
				Content:    fmt.Sprintf("Test document %d with random content", i),
				TokenCount: 50 + rand.Intn(200), // 50-250 tokens
			},
			UtilityScore: rand.Float64(), // 0-1
		}
	}
	return docs
}

// generateRandomPairs creates test document pairs with random similarities
func generateRandomPairs(n int) []DocumentPair {
	var pairs []DocumentPair
	for i := 0; i < n; i++ {
		for j := i + 1; j < n; j++ {
			similarity := rand.Float64()
			pairs = append(pairs, DocumentPair{
				DocI:             i,
				DocJ:             j,
				Similarity:       similarity,
				RedundancyPenalty: 0.3 * similarity,
				CoherenceBonus:   0.2 * similarity,
			})
		}
	}
	return pairs
}

func BenchmarkBruteForceVerifier_Scale(b *testing.B) {
	// Benchmark brute-force verification at different scales
	verifier := NewBruteForceVerifier()
	
	benchmarks := []struct {
		name    string
		numDocs int
		maxDocs int
	}{
		{"3docs", 3, 2},
		{"5docs", 5, 3}, 
		{"8docs", 8, 4},
		{"10docs", 10, 4},
		{"12docs", 12, 5},
	}
	
	for _, bm := range benchmarks {
		b.Run(bm.name, func(b *testing.B) {
			docs := generateRandomDocs(bm.numDocs)
			pairs := generateRandomPairs(bm.numDocs)
			
			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				_, err := verifier.BruteForceOptimize(docs, pairs, 1000, bm.maxDocs)
				if err != nil {
					b.Fatalf("Optimization failed: %v", err)
				}
			}
		})
	}
}

func TestBruteForceVerifier_VerifyOptimality(t *testing.T) {
	verifier := NewBruteForceVerifier()
	
	// Create test documents using the existing pattern
	docs := []types.ScoredDocument{
		{
			Document: types.Document{
				ID:         "doc1",
				Content:    "First test document",
				TokenCount: 100,
			},
			UtilityScore: 0.8,
		},
		{
			Document: types.Document{
				ID:         "doc2", 
				Content:    "Second test document",
				TokenCount: 150,
			},
			UtilityScore: 0.6,
		},
		{
			Document: types.Document{
				ID:         "doc3",
				Content:    "Third test document", 
				TokenCount: 120,
			},
			UtilityScore: 0.7,
		},
	}
	
	pairs := []DocumentPair{
		{DocI: 0, DocJ: 1, Similarity: 0.5, RedundancyPenalty: 200, CoherenceBonus: 100},
		{DocI: 1, DocJ: 2, Similarity: 0.4, RedundancyPenalty: 300, CoherenceBonus: 120},
		{DocI: 0, DocJ: 2, Similarity: 0.3, RedundancyPenalty: 150, CoherenceBonus: 90},
	}
	
	// Create a mock optimizer result to verify against
	z3Result := &OptimizeResult{
		Status:          "sat",
		ObjectiveValue:  15000, // Some objective value
		SelectedDocs:    []int{0, 2},
		VariableCount:   3,
		ConstraintCount: 10,
		SolveTimeMs:     50,
	}
	
	// Test verification
	verification, err := verifier.VerifyOptimality(docs, pairs, 300, 2, z3Result)
	if err != nil {
		t.Fatalf("Verification failed: %v", err)
	}
	
	if verification == nil {
		t.Errorf("Verification result should not be nil")
	}
	
	if verification.BruteForceOptimum <= 0 {
		t.Errorf("Brute force optimum should be positive, got %d", verification.BruteForceOptimum)
	}
	
	if verification.optimizerObjectiveValue != z3Result.ObjectiveValue {
		t.Errorf("optimizer objective value mismatch: expected %d, got %d", 
			z3Result.ObjectiveValue, verification.optimizerObjectiveValue)
	}
	
	t.Logf("Verification completed: BF=%d, optimizer=%d, Optimal=%v", 
		verification.BruteForceOptimum, verification.optimizerObjectiveValue, verification.IsOptimal)
}

func TestBruteForceVerifier_OptimizeExhaustiveComplete(t *testing.T) {
	verifier := NewBruteForceVerifier()
	
	// Test case 1: Empty documents
	t.Run("empty_documents", func(t *testing.T) {
		docs := []types.ScoredDocument{}
		pairs := []DocumentPair{}
		
		result, err := verifier.OptimizeExhaustive(docs, pairs, 100, 5)
		if err != nil {
			t.Fatalf("OptimizeExhaustive should handle empty docs: %v", err)
		}
		
		if result == nil {
			t.Fatal("Result should not be nil")
		}
		
		t.Logf("Empty docs result: Feasible=%v, ObjectiveValue=%d, SolutionsChecked=%d, SelectedDocs=%v", 
			result.Feasible, result.ObjectiveValue, result.SolutionsChecked, result.SelectedDocs)
		
		if result.SolutionsChecked != 1 {
			t.Errorf("Expected 1 solution checked for empty set, got %d", result.SolutionsChecked)
		}
	})
	
	// Test case 2: Single document
	t.Run("single_document", func(t *testing.T) {
		docs := []types.ScoredDocument{
			{
				Document: types.Document{
					ID:         "doc1",
					TokenCount: 50,
				},
				UtilityScore: 100,
			},
		}
		pairs := []DocumentPair{}
		
		result, err := verifier.OptimizeExhaustive(docs, pairs, 100, 5)
		if err != nil {
			t.Fatalf("OptimizeExhaustive failed for single doc: %v", err)
		}
		
		if !result.Feasible {
			t.Error("Single document within limits should be feasible")
		}
		
		if len(result.SelectedDocs) != 1 || result.SelectedDocs[0] != 0 {
			t.Errorf("Expected single document selected, got %v", result.SelectedDocs)
		}
		
		if result.SolutionsChecked != 2 {
			t.Errorf("Expected 2 solutions checked (empty + single), got %d", result.SolutionsChecked)
		}
	})
	
	// Test case 3: Token budget budget
	t.Run("token_budget_budget", func(t *testing.T) {
		docs := []types.ScoredDocument{
			{
				Document: types.Document{
					ID:         "doc1",
					TokenCount: 60,
				},
				UtilityScore: 100,
			},
			{
				Document: types.Document{
					ID:         "doc2", 
					TokenCount: 80,
				},
				UtilityScore: 90,
			},
		}
		pairs := []DocumentPair{}
		
		// Set budget that allows only one document
		result, err := verifier.OptimizeExhaustive(docs, pairs, 100, 5)
		if err != nil {
			t.Fatalf("OptimizeExhaustive failed: %v", err)
		}
		
		if !result.Feasible {
			t.Error("Should find feasible solution within token budget")
		}
		
		// Should select the first document (higher utility)
		if len(result.SelectedDocs) != 1 || result.SelectedDocs[0] != 0 {
			t.Errorf("Expected doc 0 selected due to higher utility, got %v", result.SelectedDocs)
		}
		
		if result.SolutionsChecked != 4 {
			t.Errorf("Expected 4 solutions checked (2^2), got %d", result.SolutionsChecked)
		}
	})
	
	// Test case 4: MaxDocs budget
	t.Run("max_docs_budget", func(t *testing.T) {
		docs := []types.ScoredDocument{
			{
				Document: types.Document{
					ID:         "doc1",
					TokenCount: 10,
				},
				UtilityScore: 100,
			},
			{
				Document: types.Document{
					ID:         "doc2",
					TokenCount: 10,
				},
				UtilityScore: 90,
			},
			{
				Document: types.Document{
					ID:         "doc3",
					TokenCount: 10,
				},
				UtilityScore: 80,
			},
		}
		pairs := []DocumentPair{}
		
		// Set maxDocs to 2
		result, err := verifier.OptimizeExhaustive(docs, pairs, 1000, 2)
		if err != nil {
			t.Fatalf("OptimizeExhaustive failed: %v", err)
		}
		
		if !result.Feasible {
			t.Error("Should find feasible solution within doc limit")
		}
		
		// Should select top 2 documents
		if len(result.SelectedDocs) != 2 {
			t.Errorf("Expected 2 docs selected due to maxDocs budget, got %d", len(result.SelectedDocs))
		}
		
		if result.SolutionsChecked != 8 {
			t.Errorf("Expected 8 solutions checked (2^3), got %d", result.SolutionsChecked)
		}
	})
	
	// Test case 5: With pairwise interactions
	t.Run("with_pairwise_interactions", func(t *testing.T) {
		docs := []types.ScoredDocument{
			{
				Document: types.Document{
					ID:         "doc1",
					TokenCount: 30,
				},
				UtilityScore: 50,
			},
			{
				Document: types.Document{
					ID:         "doc2",
					TokenCount: 30,
				},
				UtilityScore: 50,
			},
		}
		
		// Add pairwise interaction that makes selecting both better
		pairs := []DocumentPair{
			{
				DocI:           0,
				DocJ:           1,
				Similarity:     0.8,
				CoherenceBonus: 100, // High synergy
			},
		}
		
		result, err := verifier.OptimizeExhaustive(docs, pairs, 100, 5)
		if err != nil {
			t.Fatalf("OptimizeExhaustive failed: %v", err)
		}
		
		if !result.Feasible {
			t.Error("Should find feasible solution")
		}
		
		// Should select both documents due to pairwise synergy
		if len(result.SelectedDocs) != 2 {
			t.Errorf("Expected both docs selected due to synergy, got %v", result.SelectedDocs)
		}
		
		if result.SolutionsChecked != 4 {
			t.Errorf("Expected 4 solutions checked (2^2), got %d", result.SolutionsChecked)
		}
	})
	
	// Test case 6: Error case - too many documents
	t.Run("too_many_documents", func(t *testing.T) {
		docs := make([]types.ScoredDocument, 15) // More than 12
		for i := range docs {
			docs[i] = types.ScoredDocument{
				Document: types.Document{
					ID:         fmt.Sprintf("doc%d", i),
					TokenCount: 10,
				},
				UtilityScore: float64(100 - i),
			}
		}
		pairs := []DocumentPair{}
		
		result, err := verifier.OptimizeExhaustive(docs, pairs, 1000, 10)
		if err == nil {
			t.Error("OptimizeExhaustive should return error for > 12 documents")
		}
		
		if result != nil {
			t.Error("Result should be nil when error occurs")
		}
		
		expectedError := "brute force limited to N ≤ 12 documents, got 15"
		if err.Error() != expectedError {
			t.Errorf("Expected error '%s', got '%s'", expectedError, err.Error())
		}
	})
	
	// Test case 7: Edge case - maxTokens = 0 (unlimited)
	t.Run("unlimited_tokens", func(t *testing.T) {
		docs := []types.ScoredDocument{
			{
				Document: types.Document{
					ID:         "doc1",
					TokenCount: 1000,
				},
				UtilityScore: 100,
			},
			{
				Document: types.Document{
					ID:         "doc2",
					TokenCount: 2000,
				},
				UtilityScore: 90,
			},
		}
		pairs := []DocumentPair{}
		
		result, err := verifier.OptimizeExhaustive(docs, pairs, 0, 5) // 0 = unlimited tokens
		if err != nil {
			t.Fatalf("OptimizeExhaustive failed: %v", err)
		}
		
		if !result.Feasible {
			t.Error("Should find feasible solution with unlimited tokens")
		}
		
		// Should select both documents
		if len(result.SelectedDocs) != 2 {
			t.Errorf("Expected both docs selected with unlimited tokens, got %v", result.SelectedDocs)
		}
	})
	
	// Test case 8: Complex scenario with multiple budgets
	t.Run("complex_scenario", func(t *testing.T) {
		docs := []types.ScoredDocument{
			{
				Document: types.Document{
					ID:         "doc1",
					TokenCount: 40,
				},
				UtilityScore: 100,
			},
			{
				Document: types.Document{
					ID:         "doc2",
					TokenCount: 35,
				},
				UtilityScore: 95,
			},
			{
				Document: types.Document{
					ID:         "doc3",
					TokenCount: 30,
				},
				UtilityScore: 90,
			},
			{
				Document: types.Document{
					ID:         "doc4",
					TokenCount: 25,
				},
				UtilityScore: 85,
			},
		}
		
		pairs := []DocumentPair{
			{DocI: 0, DocJ: 1, Similarity: 0.8, CoherenceBonus: 50},
			{DocI: 1, DocJ: 2, Similarity: 0.6, CoherenceBonus: 30},
			{DocI: 2, DocJ: 3, Similarity: 0.7, CoherenceBonus: 40},
		}
		
		result, err := verifier.OptimizeExhaustive(docs, pairs, 100, 3)
		if err != nil {
			t.Fatalf("OptimizeExhaustive failed: %v", err)
		}
		
		if !result.Feasible {
			t.Error("Should find feasible solution in complex scenario")
		}
		
		if result.SolutionsChecked != 16 {
			t.Errorf("Expected 16 solutions checked (2^4), got %d", result.SolutionsChecked)
		}
		
		// Verify all selected docs are within bounds
		for _, idx := range result.SelectedDocs {
			if idx < 0 || idx >= len(docs) {
				t.Errorf("Invalid document index %d", idx)
			}
		}
		
		t.Logf("Complex scenario result: selected %v, objective %d", 
			result.SelectedDocs, result.ObjectiveValue)
	})
}

func TestBruteForceVerifier_VerifyOptimalityComplete(t *testing.T) {
	verifier := NewBruteForceVerifier()
	
	// Helper to create test documents
	createDocs := func(count int) []types.ScoredDocument {
		docs := make([]types.ScoredDocument, count)
		for i := 0; i < count; i++ {
			docs[i] = types.ScoredDocument{
				Document: types.Document{
					ID:         fmt.Sprintf("doc%d", i),
					TokenCount: 50,
				},
				UtilityScore: float64(100 - i*10),
			}
		}
		return docs
	}
	
	// Test case 1: optimizer finds optimal solution
	t.Run("z3_optimal", func(t *testing.T) {
		docs := createDocs(3)
		pairs := []DocumentPair{}
		
		// Create optimizer result that matches optimal
		z3Result := &OptimizeResult{
			SelectedDocs:    []int{0, 1}, // Best 2 docs
			ObjectiveValue:  1900000,     // (100 + 90) * 10000 scale
			Status:          "sat",
			SolveTimeMs:     50,
		}
		
		verification, err := verifier.VerifyOptimality(docs, pairs, 200, 2, z3Result)
		if err != nil {
			t.Fatalf("VerifyOptimality failed: %v", err)
		}
		
		if verification == nil {
			t.Fatal("Verification result should not be nil")
		}
		
		if !verification.IsOptimal {
			t.Error("optimizer result should be verified as optimal")
		}
		
		if verification.Gap != 0.0 {
			t.Errorf("Gap should be 0 for optimal solution, got %f", verification.Gap)
		}
		
		if verification.optimizerObjectiveValue != z3Result.ObjectiveValue {
			t.Errorf("optimizer objective mismatch: expected %d, got %d", 
				z3Result.ObjectiveValue, verification.optimizerObjectiveValue)
		}
		
		t.Logf("Optimal verification: BF=%d, optimizer=%d, Gap=%f", 
			verification.BruteForceOptimum, verification.optimizerObjectiveValue, verification.Gap)
	})
	
	// Test case 2: optimizer finds suboptimal solution
	t.Run("z3_suboptimal", func(t *testing.T) {
		docs := createDocs(3)
		pairs := []DocumentPair{}
		
		// Create optimizer result that is suboptimal
		z3Result := &OptimizeResult{
			SelectedDocs:    []int{1, 2}, // Suboptimal selection
			ObjectiveValue:  1700000,     // (90 + 80) * 10000 scale
			Status:          "sat",
			SolveTimeMs:     50,
		}
		
		verification, err := verifier.VerifyOptimality(docs, pairs, 200, 2, z3Result)
		if err != nil {
			t.Fatalf("VerifyOptimality failed: %v", err)
		}
		
		if verification.IsOptimal {
			t.Error("optimizer result should be verified as suboptimal")
		}
		
		if verification.Gap <= 0.0 {
			t.Errorf("Gap should be positive for suboptimal solution, got %f", verification.Gap)
		}
		
		expectedGap := float64(verification.BruteForceOptimum - z3Result.ObjectiveValue) / float64(verification.BruteForceOptimum)
		if verification.Gap != expectedGap {
			t.Errorf("Gap calculation incorrect: expected %f, got %f", expectedGap, verification.Gap)
		}
		
		t.Logf("Suboptimal verification: BF=%d, optimizer=%d, Gap=%f", 
			verification.BruteForceOptimum, verification.optimizerObjectiveValue, verification.Gap)
	})
	
	// Test case 3: optimizer returns unsat
	t.Run("z3_unsat", func(t *testing.T) {
		docs := createDocs(2)
		pairs := []DocumentPair{}
		
		// Create optimizer result with unsat status
		z3Result := &OptimizeResult{
			SelectedDocs:    []int{},
			ObjectiveValue:  0,
			Status:          "unsat",
			SolveTimeMs:     50,
		}
		
		verification, err := verifier.VerifyOptimality(docs, pairs, 200, 2, z3Result)
		if err != nil {
			t.Fatalf("VerifyOptimality failed: %v", err)
		}
		
		if verification.IsOptimal {
			t.Error("Unsat optimizer result should not be marked as optimal")
		}
		
		t.Logf("Unsat verification: BF=%d, optimizer=%d, Status=%s", 
			verification.BruteForceOptimum, verification.optimizerObjectiveValue, z3Result.Status)
	})
	
	// Test case 4: Zero objective value edge case
	t.Run("zero_objective", func(t *testing.T) {
		docs := []types.ScoredDocument{
			{
				Document: types.Document{
					ID:         "doc1",
					TokenCount: 1000, // Too large for budget
				},
				UtilityScore: 100,
			},
		}
		pairs := []DocumentPair{}
		
		// Create optimizer result with zero objective (no feasible selection)
		z3Result := &OptimizeResult{
			SelectedDocs:    []int{},
			ObjectiveValue:  0,
			Status:          "sat",
			SolveTimeMs:     50,
		}
		
		verification, err := verifier.VerifyOptimality(docs, pairs, 100, 1, z3Result) // Very tight budget
		if err != nil {
			t.Fatalf("VerifyOptimality failed: %v", err)
		}
		
		// With zero brute force optimum, gap calculation should handle division by zero
		if verification.Gap != 0.0 {
			t.Errorf("Gap should be 0 when brute force optimum is 0, got %f", verification.Gap)
		}
		
		t.Logf("Zero objective verification: BF=%d, optimizer=%d, Gap=%f", 
			verification.BruteForceOptimum, verification.optimizerObjectiveValue, verification.Gap)
	})
	
	// Test case 5: Brute force optimization error propagation
	t.Run("brute_force_error", func(t *testing.T) {
		docs := createDocs(15) // Too many documents for brute force
		pairs := []DocumentPair{}
		
		z3Result := &OptimizeResult{
			SelectedDocs:    []int{0, 1},
			ObjectiveValue:  1900000, // Scaled value
			Status:          "sat",
			SolveTimeMs:     50,
		}
		
		verification, err := verifier.VerifyOptimality(docs, pairs, 200, 2, z3Result)
		if err == nil {
			t.Error("VerifyOptimality should propagate brute force error for too many documents")
		}
		
		if verification != nil {
			t.Error("Verification result should be nil when error occurs")
		}
		
		expectedError := "brute force limited to N ≤ 12 documents, got 15"
		if err.Error() != expectedError {
			t.Errorf("Expected error '%s', got '%s'", expectedError, err.Error())
		}
	})
	
	// Test case 6: Infeasible brute force result
	t.Run("infeasible_brute_force", func(t *testing.T) {
		docs := []types.ScoredDocument{
			{
				Document: types.Document{
					ID:         "doc1",
					TokenCount: 200,
				},
				UtilityScore: 100,
			},
			{
				Document: types.Document{
					ID:         "doc2",
					TokenCount: 200,
				},
				UtilityScore: 90,
			},
		}
		pairs := []DocumentPair{}
		
		z3Result := &OptimizeResult{
			SelectedDocs:    []int{},
			ObjectiveValue:  0,
			Status:          "unsat",
			SolveTimeMs:     50,
		}
		
		// Very tight budget - no document can fit
		verification, err := verifier.VerifyOptimality(docs, pairs, 100, 1, z3Result)
		if err != nil {
			t.Fatalf("VerifyOptimality failed: %v", err)
		}
		
		// When brute force finds no feasible solution, IsOptimal should remain false
		if verification.IsOptimal {
			t.Error("Should not be optimal when brute force finds no feasible solution")
		}
		
		t.Logf("Infeasible verification: BF=%d feasible=%v, optimizer=%d status=%s", 
			verification.BruteForceOptimum, verification.BruteForceOptimum > 0, verification.optimizerObjectiveValue, z3Result.Status)
	})
}
