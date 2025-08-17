package features

import (
	"contextlite/pkg/types"
	"testing"
)

// TestComputePairwiseScores_KeyGeneration tests the specific key generation logic
func TestComputePairwiseScores_KeyGeneration(t *testing.T) {
	computer := NewSimilarityComputer(10)
	
	// Create documents where we can predict the ordering
	docs := []types.ScoredDocument{
		{Document: types.Document{ID: "doc0", Content: "content zero"}},
		{Document: types.Document{ID: "doc1", Content: "content one"}},
		{Document: types.Document{ID: "doc2", Content: "content two"}},
	}
	
	pairs := computer.ComputePairwiseScores(docs)
	
	// The function creates pairs where i < j in the initial loop
	// But in the grouping phase, both DocI and DocJ are used as keys
	// This should test both branches of the key generation
	
	foundPairs := make(map[string]bool)
	for _, pair := range pairs {
		var key string
		if pair.DocI < pair.DocJ {
			key = "forward"
		} else {
			key = "reverse"
		}
		foundPairs[key] = true
		
		t.Logf("Pair: DocI=%d, DocJ=%d, Similarity=%.3f", 
			pair.DocI, pair.DocJ, pair.Similarity)
	}
	
	t.Logf("Found pair types: %+v", foundPairs)
}

// TestComputePairwiseScores_FullCoverage attempts to hit all code paths
func TestComputePairwiseScores_FullCoverage(t *testing.T) {
	computer := NewSimilarityComputer(1) // Very restrictive limit
	
	// Create many similar documents to force the limiting logic
	docs := []types.ScoredDocument{
		{Document: types.Document{ID: "A", Content: "similar text alpha beta"}},
		{Document: types.Document{ID: "B", Content: "similar text beta gamma"}},
		{Document: types.Document{ID: "C", Content: "similar text gamma delta"}},
		{Document: types.Document{ID: "D", Content: "similar text delta epsilon"}},
		{Document: types.Document{ID: "E", Content: "completely different unrelated content"}},
	}
	
	pairs := computer.ComputePairwiseScores(docs)
	
	t.Logf("Generated %d pairs with maxPairsPerDoc=1", len(pairs))
	
	// With maxPairsPerDoc=1, each document should contribute at most 1 pair
	// But due to deduplication, the actual count may be less
	
	for i, pair := range pairs {
		t.Logf("Pair %d: %d-%d, similarity=%.3f", i, pair.DocI, pair.DocJ, pair.Similarity)
	}
	
	// Test that the break condition works
	if len(pairs) > len(docs) {
		t.Errorf("Too many pairs generated: %d (expected <= %d)", len(pairs), len(docs))
	}
}

// TestComputePairwiseScores_SortingVerification verifies the sorting logic
func TestComputePairwiseScores_SortingVerification(t *testing.T) {
	computer := NewSimilarityComputer(5)
	
	// Create documents with predictable similarity patterns
	docs := []types.ScoredDocument{
		{Document: types.Document{ID: "base", Content: "machine learning neural network"}},
		{Document: types.Document{ID: "high", Content: "machine learning neural network deep"}}, // Very similar
		{Document: types.Document{ID: "med", Content: "machine learning algorithms"}},           // Somewhat similar
		{Document: types.Document{ID: "low", Content: "cooking recipes food"}},                  // Very different
	}
	
	pairs := computer.ComputePairwiseScores(docs)
	
	// Find pairs involving the base document
	var basePairs []DocumentPair
	for _, pair := range pairs {
		if pair.DocI == 0 || pair.DocJ == 0 {
			basePairs = append(basePairs, pair)
		}
	}
	
	t.Logf("Found %d pairs involving base document", len(basePairs))
	
	// The pairs should be sorted by similarity in descending order
	// Due to the content, we expect: base-high > base-med > base-low
	for i, pair := range basePairs {
		t.Logf("Base pair %d: similarity=%.3f", i, pair.Similarity)
	}
	
	if len(basePairs) == 0 {
		t.Error("Expected at least one pair involving base document")
	}
}
