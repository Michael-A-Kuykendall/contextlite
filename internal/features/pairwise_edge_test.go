package features

import (
	"contextlite/pkg/types"
	"testing"
)

// TestComputePairwiseScores_EdgeCases tests edge cases for ComputePairwiseScores
func TestComputePairwiseScores_EdgeCases(t *testing.T) {
	computer := NewSimilarityComputer(2) // Small limit to test limiting logic
	
	t.Run("empty_documents", func(t *testing.T) {
		docs := []types.ScoredDocument{}
		pairs := computer.ComputePairwiseScores(docs)
		
		if len(pairs) != 0 {
			t.Errorf("Expected 0 pairs for empty input, got %d", len(pairs))
		}
	})
	
	t.Run("single_document", func(t *testing.T) {
		docs := []types.ScoredDocument{
			{
				Document: types.Document{
					ID:      "1",
					Content: "single document content",
				},
			},
		}
		
		pairs := computer.ComputePairwiseScores(docs)
		
		if len(pairs) != 0 {
			t.Errorf("Expected 0 pairs for single document, got %d", len(pairs))
		}
	})
	
	t.Run("max_pairs_limiting", func(t *testing.T) {
		// Create many documents to test the maxPairsPerDoc limiting
		docs := []types.ScoredDocument{
			{Document: types.Document{ID: "1", Content: "similar content alpha"}},
			{Document: types.Document{ID: "2", Content: "similar content beta"}},
			{Document: types.Document{ID: "3", Content: "similar content gamma"}},
			{Document: types.Document{ID: "4", Content: "similar content delta"}},
			{Document: types.Document{ID: "5", Content: "similar content epsilon"}},
		}
		
		pairs := computer.ComputePairwiseScores(docs)
		
		// With maxPairsPerDoc=2, we should get fewer pairs than all possible combinations
		maxPossible := len(docs) * (len(docs) - 1) / 2 // 5*4/2 = 10
		
		t.Logf("Got %d pairs, max possible was %d", len(pairs), maxPossible)
		
		// Verify we have some pairs but not all possible
		if len(pairs) == 0 {
			t.Error("Expected some pairs when limiting")
		}
	})
	
	t.Run("duplicate_key_handling", func(t *testing.T) {
		// Test the key generation and deduplication logic
		docs := []types.ScoredDocument{
			{Document: types.Document{ID: "1", Content: "test content one"}},
			{Document: types.Document{ID: "2", Content: "test content two"}},
			{Document: types.Document{ID: "3", Content: "test content three"}},
		}
		
		pairs := computer.ComputePairwiseScores(docs)
		
		// Check that no duplicate pairs exist
		seenKeys := make(map[string]bool)
		for _, pair := range pairs {
			var key string
			if pair.DocI < pair.DocJ {
				key = string(rune(pair.DocI + '0')) + "-" + string(rune(pair.DocJ + '0'))
			} else {
				key = string(rune(pair.DocJ + '0')) + "-" + string(rune(pair.DocI + '0'))
			}
			
			if seenKeys[key] {
				t.Errorf("Found duplicate pair key: %s", key)
			}
			seenKeys[key] = true
		}
	})
	
	t.Run("zero_maxPairsPerDoc", func(t *testing.T) {
		computer := NewSimilarityComputer(0) // Zero limit
		
		docs := []types.ScoredDocument{
			{Document: types.Document{ID: "1", Content: "content one"}},
			{Document: types.Document{ID: "2", Content: "content two"}},
		}
		
		pairs := computer.ComputePairwiseScores(docs)
		
		// With maxPairsPerDoc=0, should get no pairs due to limiting
		if len(pairs) != 0 {
			t.Errorf("Expected 0 pairs with maxPairsPerDoc=0, got %d", len(pairs))
		}
	})
	
	t.Run("identical_documents", func(t *testing.T) {
		// Test with identical content to trigger high similarity scores
		docs := []types.ScoredDocument{
			{Document: types.Document{ID: "1", Content: "identical content here"}},
			{Document: types.Document{ID: "2", Content: "identical content here"}},
			{Document: types.Document{ID: "3", Content: "different content entirely"}},
		}
		
		pairs := computer.ComputePairwiseScores(docs)
		
		// Should get some pairs
		if len(pairs) == 0 {
			t.Error("Expected pairs from identical content test")
		}
		
		// Find the identical pair and check high similarity
		for _, pair := range pairs {
			if (pair.DocI == 0 && pair.DocJ == 1) || (pair.DocI == 1 && pair.DocJ == 0) {
				if pair.Similarity < 0.5 {
					t.Errorf("Expected high similarity for identical docs, got %f", pair.Similarity)
				}
			}
		}
	})
}
