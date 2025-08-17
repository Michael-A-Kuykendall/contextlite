package features

import (
	"testing"

	"contextlite/pkg/types"
)

func TestNewSimilarityComputer(t *testing.T) {
	computer := NewSimilarityComputer(100)
	if computer == nil {
		t.Fatal("NewSimilarityComputer returned nil")
	}
	
	if computer.maxPairsPerDoc != 100 {
		t.Errorf("Expected maxPairsPerDoc 100, got %d", computer.maxPairsPerDoc)
	}
}

func TestSimilarityComputer_ComputePairwiseScores(t *testing.T) {
	computer := NewSimilarityComputer(100)
	
	docs := []types.ScoredDocument{
		{
			Document: types.Document{
				ID:      "1",
				Content: "machine learning algorithms",
			},
		},
		{
			Document: types.Document{
				ID:      "2", 
				Content: "artificial intelligence neural networks",
			},
		},
		{
			Document: types.Document{
				ID:      "3",
				Content: "completely different content about cooking",
			},
		},
	}
	
	pairs := computer.ComputePairwiseScores(docs)
	
	if len(pairs) == 0 {
		t.Error("Expected some pairwise scores, got none")
	}
	
	// Check that pairs have valid scores
	for _, pair := range pairs {
		if pair.Similarity < 0 || pair.Similarity > 1 {
			t.Errorf("Similarity score out of range [0,1]: %f", pair.Similarity)
		}
		
		if pair.Coherence < 0 || pair.Coherence > 1 {
			t.Errorf("Coherence score out of range [0,1]: %f", pair.Coherence)
		}
		
		if pair.Redundancy < 0 || pair.Redundancy > 1 {
			t.Errorf("Redundancy score out of range [0,1]: %f", pair.Redundancy)
		}
	}
}

func TestComputeDocumentSimilarity(t *testing.T) {
	computer := NewSimilarityComputer(100)
	
	doc1 := types.Document{
		ID:      "1",
		Content: "machine learning algorithms",
		Path:    "/path/to/file1.txt",
	}
	
	doc2 := types.Document{
		ID:      "2",
		Content: "machine learning techniques",
		Path:    "/path/to/file2.txt",
	}
	
	similarity := computer.computeDocumentSimilarity(doc1, doc2)
	
	if similarity < 0 || similarity > 1 {
		t.Errorf("Similarity should be in [0,1], got %f", similarity)
	}
	
	// Similar content should have high similarity
	if similarity < 0.5 {
		t.Errorf("Expected high similarity for similar content, got %f", similarity)
	}
}

func TestComputeCoherence(t *testing.T) {
	computer := NewSimilarityComputer(100)
	
	doc1 := types.Document{
		ID:      "1",
		Content: "machine learning algorithms",
		Path:    "/ml/algorithms.txt",
	}
	
	doc2 := types.Document{
		ID:      "2",
		Content: "machine learning techniques",
		Path:    "/ml/techniques.txt",
	}
	
	// Test with similar paths and content
	coherence := computer.computeCoherence(doc1, doc2)
	
	if coherence < 0 || coherence > 1 {
		t.Errorf("Coherence should be in [0,1], got %f", coherence)
	}
	
	// Test with different paths
	doc3 := types.Document{
		ID:      "3",
		Content: "machine learning techniques",
		Path:    "/completely/different/path.txt",
	}
	
	coherence2 := computer.computeCoherence(doc1, doc3)
	
	if coherence2 < 0 || coherence2 > 1 {
		t.Errorf("Coherence should be in [0,1], got %f", coherence2)
	}
}

func TestPathSimilarity(t *testing.T) {
	computer := NewSimilarityComputer(100)
	
	// Test identical paths
	sim := computer.pathSimilarity("/path/to/file.txt", "/path/to/file.txt")
	if sim != 1.0 {
		t.Errorf("Expected 1.0 for identical paths, got %f", sim)
	}
	
	// Test similar paths
	sim = computer.pathSimilarity("/path/to/file1.txt", "/path/to/file2.txt")
	if sim <= 0.5 {
		t.Errorf("Expected high similarity for similar paths, got %f", sim)
	}
	
	// Test completely different paths
	sim = computer.pathSimilarity("/path/to/file.txt", "/completely/different/path.txt")
	if sim >= 0.5 {
		t.Errorf("Expected low similarity for different paths, got %f", sim)
	}
	
	// Test empty paths
	sim = computer.pathSimilarity("", "")
	if sim != 0.0 {
		t.Errorf("Expected 0.0 for empty paths, got %f", sim)
	}
	
	// Test one empty path
	sim = computer.pathSimilarity("/path/to/file.txt", "")
	if sim != 0.0 {
		t.Errorf("Expected 0.0 for one empty path, got %f", sim)
	}
}

func TestCosineSimilarity(t *testing.T) {
	// Test identical vectors
	vec1 := []float64{1, 2, 3}
	vec2 := []float64{1, 2, 3}
	
	sim := cosineSimilarity(vec1, vec2)
	if sim != 1.0 {
		t.Errorf("Expected 1.0 for identical vectors, got %f", sim)
	}
	
	// Test orthogonal vectors
	vec3 := []float64{1, 0}
	vec4 := []float64{0, 1}
	
	sim = cosineSimilarity(vec3, vec4)
	if sim != 0.0 {
		t.Errorf("Expected 0.0 for orthogonal vectors, got %f", sim)
	}
	
	// Test empty vectors
	vec5 := []float64{}
	vec6 := []float64{}
	
	sim = cosineSimilarity(vec5, vec6)
	if sim != 0.0 {
		t.Errorf("Expected 0.0 for empty vectors, got %f", sim)
	}
	
	// Test different length vectors
	vec7 := []float64{1, 2}
	vec8 := []float64{1, 2, 3}
	
	sim = cosineSimilarity(vec7, vec8)
	if sim != 0.0 {
		t.Errorf("Expected 0.0 for different length vectors, got %f", sim)
	}
}

func TestFilterEmpty(t *testing.T) {
	// Test with empty strings
	input := []string{"hello", "", "world", "", "test"}
	result := filterEmpty(input)
	
	expected := []string{"hello", "world", "test"}
	
	if len(result) != len(expected) {
		t.Errorf("Expected %d items, got %d", len(expected), len(result))
	}
	
	for i, expected := range expected {
		if i >= len(result) || result[i] != expected {
			t.Errorf("Expected item %d to be '%s', got '%s'", i, expected, result[i])
		}
	}
	
	// Test with all empty strings
	input = []string{"", "", ""}
	result = filterEmpty(input)
	
	if len(result) != 0 {
		t.Errorf("Expected empty result for all empty strings, got %v", result)
	}
	
	// Test with no empty strings
	input = []string{"hello", "world", "test"}
	result = filterEmpty(input)
	
	if len(result) != len(input) {
		t.Errorf("Expected %d items when no empty strings, got %d", len(input), len(result))
	}
}

func TestExtractSignificantTermsEdgeCases(t *testing.T) {
	// Test with empty content
	terms := extractSignificantTerms("", 0.2)
	if len(terms) != 0 {
		t.Errorf("Expected no terms for empty content, got %d", len(terms))
	}
	
	// Test with punctuation only
	terms = extractSignificantTerms("!@#$%^&*()", 0.2)
	if len(terms) == 0 {
		t.Log("No terms extracted from punctuation (expected)")
	}
	
	// Test with mixed content
	terms = extractSignificantTerms("The quick brown fox jumps over the lazy dog.", 0.2)
	if len(terms) == 0 {
		t.Error("Expected some terms for normal text")
	}
}

func TestComputeDocumentSimilarityEdgeCases(t *testing.T) {
	computer := NewSimilarityComputer(100)
	
	// Test with empty documents
	emptyDoc1 := types.Document{ID: "1", Content: ""}
	emptyDoc2 := types.Document{ID: "2", Content: ""}
	
	sim := computer.computeDocumentSimilarity(emptyDoc1, emptyDoc2)
	if sim != 0.0 {
		t.Errorf("Expected 0 similarity for empty documents, got %f", sim)
	}
	
	// Test with one empty document
	normalDoc := types.Document{ID: "3", Content: "normal content"}
	sim = computer.computeDocumentSimilarity(emptyDoc1, normalDoc)
	if sim != 0.0 {
		t.Errorf("Expected 0 similarity for one empty document, got %f", sim)
	}
}