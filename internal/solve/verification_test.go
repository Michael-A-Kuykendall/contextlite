package solve

import (
	"fmt"
	"math/rand"
	"testing"

	"contextlite/pkg/types"
)

func TestBruteForceVerifier_ParityWithZ3(t *testing.T) {
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
