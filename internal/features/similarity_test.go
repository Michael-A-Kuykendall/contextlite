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

func TestComputeCoherenceLanguageBoost(t *testing.T) {
	computer := NewSimilarityComputer(100)
	
	// Test language boost code path: same non-empty language
	doc1 := types.Document{
		ID:       "1",
		Content:  "function main() { print hello world }",
		Path:     "/project/main.go",
		Language: "go",
	}
	
	doc2SameLang := types.Document{
		ID:       "2", 
		Content:  "function test() { print hello universe }",
		Path:     "/different/test.go",
		Language: "go", // Same language - should trigger boost code path
	}
	
	doc2DiffLang := types.Document{
		ID:       "3",
		Content:  "function test() { print hello universe }",
		Path:     "/different/test.py",
		Language: "python", // Different language - should not trigger boost
	}
	
	coherenceSameLang := computer.computeCoherence(doc1, doc2SameLang)
	coherenceDiffLang := computer.computeCoherence(doc1, doc2DiffLang)
	
	// Just verify valid range - the goal is to exercise the code paths
	if coherenceSameLang < 0 || coherenceSameLang > 1 {
		t.Errorf("Coherence with same language should be in [0,1], got %f", coherenceSameLang)
	}
	if coherenceDiffLang < 0 || coherenceDiffLang > 1 {
		t.Errorf("Coherence with different language should be in [0,1], got %f", coherenceDiffLang)
	}
	
	// Test empty language - should not trigger boost
	doc2EmptyLang := types.Document{
		ID:       "4",
		Content:  "function test() { print hello universe }",
		Path:     "/different/test.go",
		Language: "", // Empty language
	}
	
	coherenceEmptyLang := computer.computeCoherence(doc1, doc2EmptyLang)
	
	// Result should be valid
	if coherenceEmptyLang < 0 || coherenceEmptyLang > 1 {
		t.Errorf("Coherence with empty language should be in [0,1], got %f", coherenceEmptyLang)
	}
}

func TestComputeCoherencePathBoost(t *testing.T) {
	computer := NewSimilarityComputer(100)
	
	// Test path boost code path: similar paths (should trigger path similarity > 0.5)
	doc1 := types.Document{
		ID:      "1",
		Content: "function main() { print hello world }",
		Path:    "/project/src/main.go",
	}
	
	doc2SimilarPath := types.Document{
		ID:      "2",
		Content: "function test() { print hello universe }",
		Path:    "/project/src/test.go", // Same directory - should have high path similarity
	}
	
	doc2DifferentPath := types.Document{
		ID:      "3",
		Content: "function test() { print hello universe }",
		Path:    "/completely/different/location/test.go", // Different path
	}
	
	coherenceSimilarPath := computer.computeCoherence(doc1, doc2SimilarPath)
	coherenceDifferentPath := computer.computeCoherence(doc1, doc2DifferentPath)
	
	// Just verify valid range - the goal is to exercise the code paths
	if coherenceSimilarPath < 0 || coherenceSimilarPath > 1 {
		t.Errorf("Coherence with similar path should be in [0,1], got %f", coherenceSimilarPath)
	}
	if coherenceDifferentPath < 0 || coherenceDifferentPath > 1 {
		t.Errorf("Coherence with different path should be in [0,1], got %f", coherenceDifferentPath)
	}
}

func TestComputeCoherenceCombinedBoosts(t *testing.T) {
	computer := NewSimilarityComputer(100)
	
	// Create baseline content for comparison
	baseContent := "function test() { print hello world algorithm }"
	
	// Test both language and path boosts together
	doc1 := types.Document{
		ID:       "1",
		Content:  baseContent,
		Path:     "/project/src/main.go",
		Language: "go",
	}
	
	doc2BothBoosts := types.Document{
		ID:       "2",
		Content:  baseContent,
		Path:     "/project/src/test.go", // Same directory (path boost)
		Language: "go",                   // Same language (language boost)
	}
	
	doc2NoBoosts := types.Document{
		ID:       "3",
		Content:  baseContent,
		Path:     "/completely/different/location/test.py", // Different path (no path boost)
		Language: "python",                                 // Different language (no language boost)
	}
	
	coherenceBothBoosts := computer.computeCoherence(doc1, doc2BothBoosts)
	coherenceNoBoosts := computer.computeCoherence(doc1, doc2NoBoosts)
	
	// Both boosts should increase coherence (or at least not decrease it)
	if coherenceBothBoosts < coherenceNoBoosts {
		t.Errorf("Expected both boosts to increase coherence: with=%f, without=%f",
			coherenceBothBoosts, coherenceNoBoosts)
	}
	
	// Verify both values are in valid range
	if coherenceBothBoosts < 0 || coherenceBothBoosts > 1 {
		t.Errorf("Coherence with boosts should be in [0,1], got %f", coherenceBothBoosts)
	}
	if coherenceNoBoosts < 0 || coherenceNoBoosts > 1 {
		t.Errorf("Coherence without boosts should be in [0,1], got %f", coherenceNoBoosts)
	}
}

func TestComputeCoherenceCapAtOne(t *testing.T) {
	computer := NewSimilarityComputer(100)
	
	// Create documents with high similarity content but test the Math.Min capping
	// Use content that should give high Jaccard + boosts to test the cap
	doc1 := types.Document{
		ID:       "1",
		Content:  "algorithm algorithm algorithm machine machine learning", // Repeated terms for higher frequency
		Path:     "/project/src/main.go",
		Language: "go",
	}
	
	doc2 := types.Document{
		ID:       "2", 
		Content:  "algorithm algorithm machine machine learning learning", // Similar high-frequency terms
		Path:     "/project/src/test.go", // Similar path for boost
		Language: "go",                   // Same language for boost
	}
	
	coherence := computer.computeCoherence(doc1, doc2)
	
	// Should be capped at 1.0 even with boosts
	if coherence > 1.0 {
		t.Errorf("Coherence should be capped at 1.0, got %f", coherence)
	}
	
	// Test that Math.Min is actually working by creating a scenario that should cap
	// Create documents that would exceed 1.0 without Math.Min
	doc3 := types.Document{
		ID:       "3",
		Content:  "same same same same same same", // Identical frequent terms
		Path:     "/project/src/file1.go",
		Language: "go",
	}
	
	doc4 := types.Document{
		ID:       "4",
		Content:  "same same same same same same", // Identical frequent terms  
		Path:     "/project/src/file2.go", // Similar path
		Language: "go",                     // Same language
	}
	
	coherence2 := computer.computeCoherence(doc3, doc4)
	
	// Should be capped at 1.0
	if coherence2 > 1.0 {
		t.Errorf("Coherence should be capped at 1.0, got %f", coherence2)
	}
	
	// Verify that without any boosts, we get a lower value
	doc5 := types.Document{
		ID:       "5",
		Content:  "same same same same same same",
		Path:     "/completely/different/path.py",
		Language: "python",
	}
	
	coherenceNoBoosts := computer.computeCoherence(doc3, doc5)
	
	// The capped value should be higher than no-boosts (unless no-boosts is already 1.0)
	if coherence2 < coherenceNoBoosts && coherenceNoBoosts < 1.0 {
		t.Errorf("Expected boosts to increase coherence: with=%f, without=%f", coherence2, coherenceNoBoosts)
	}
}

func TestComputeCoherenceEdgeCases(t *testing.T) {
	computer := NewSimilarityComputer(100)
	
	// Test with documents that produce no significant terms
	doc1 := types.Document{
		ID:      "1",
		Content: "", // Empty content
		Path:    "/test/file1.txt",
	}
	
	doc2 := types.Document{
		ID:      "2",
		Content: "content with words",
		Path:    "/test/file2.txt",
	}
	
	coherence := computer.computeCoherence(doc1, doc2)
	if coherence != 0.0 {
		t.Errorf("Expected 0.0 coherence for empty content, got %f", coherence)
	}
	
	// Test with both documents having no significant terms
	doc3 := types.Document{
		ID:      "3",
		Content: "",
		Path:    "/test/file3.txt",
	}
	
	coherence2 := computer.computeCoherence(doc1, doc3)
	if coherence2 != 0.0 {
		t.Errorf("Expected 0.0 coherence for both empty content, got %f", coherence2)
	}
	
	// Test with punctuation-only content (should produce no significant terms)
	doc4 := types.Document{
		ID:      "4",
		Content: "!@#$%^&*()",
		Path:    "/test/file4.txt",
	}
	
	doc5 := types.Document{
		ID:      "5",
		Content: "normal content with words",
		Path:    "/test/file5.txt",
	}
	
	coherence3 := computer.computeCoherence(doc4, doc5)
	// This might be 0.0 if punctuation produces no significant terms
	if coherence3 < 0 || coherence3 > 1 {
		t.Errorf("Coherence should be in [0,1] even for punctuation, got %f", coherence3)
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

func TestPathSimilarityEdgeCases(t *testing.T) {
	computer := NewSimilarityComputer(100)
	
	// Test paths that become empty after filterEmpty (only slashes)
	sim := computer.pathSimilarity("///", "//")
	if sim != 0.0 {
		t.Errorf("Expected 0.0 for paths with only slashes, got %f", sim)
	}
	
	// Test one path becomes empty after filtering
	sim = computer.pathSimilarity("/path/to/file", "///")
	if sim != 0.0 {
		t.Errorf("Expected 0.0 when one path becomes empty after filtering, got %f", sim)
	}
	
	// Test case sensitivity (function converts to lower)
	sim = computer.pathSimilarity("/Path/To/File", "/path/to/file")
	if sim != 1.0 {
		t.Errorf("Expected 1.0 for case-insensitive identical paths, got %f", sim)
	}
	
	// Test paths with different lengths (maxLen calculation)
	simShortLong := computer.pathSimilarity("/a/b", "/a/b/c/d/e")
	// Common prefix: 2, maxLen: 5, similarity: 2/5 = 0.4
	expectedShortLong := 2.0 / 5.0
	if absFloat(simShortLong-expectedShortLong) > 0.01 {
		t.Errorf("Expected %f for short/long paths, got %f", expectedShortLong, simShortLong)
	}
	
	// Test reverse (long/short) - should be same result
	simLongShort := computer.pathSimilarity("/a/b/c/d/e", "/a/b")
	if absFloat(simLongShort-expectedShortLong) > 0.01 {
		t.Errorf("Expected %f for long/short paths, got %f", expectedShortLong, simLongShort)
	}
	
	// Test no common prefix
	sim = computer.pathSimilarity("/a/b/c", "/x/y/z")
	if sim != 0.0 {
		t.Errorf("Expected 0.0 for no common prefix, got %f", sim)
	}
	
	// Test partial common prefix
	sim = computer.pathSimilarity("/a/b/c/d", "/a/b/x/y")
	// Common prefix: 2, maxLen: 4, similarity: 2/4 = 0.5
	expectedPartial := 2.0 / 4.0
	if absFloat(sim-expectedPartial) > 0.01 {
		t.Errorf("Expected %f for partial common prefix, got %f", expectedPartial, sim)
	}
	
	// Test paths with multiple consecutive slashes
	sim = computer.pathSimilarity("/a//b///c", "/a/b/c")
	if sim != 1.0 {
		t.Errorf("Expected 1.0 for paths with multiple slashes, got %f", sim)
	}
	
	// Test single component paths
	sim = computer.pathSimilarity("/file1", "/file2")
	if sim != 0.0 {
		t.Errorf("Expected 0.0 for different single component paths, got %f", sim)
	}
	
	sim = computer.pathSimilarity("/file", "/file")
	if sim != 1.0 {
		t.Errorf("Expected 1.0 for identical single component paths, got %f", sim)
	}
	
	// Test paths where one has common prefix but different total length
	sim = computer.pathSimilarity("/a/b", "/a")
	// Common prefix: 1, maxLen: 2, similarity: 1/2 = 0.5
	expectedOne := 1.0 / 2.0
	if absFloat(sim-expectedOne) > 0.01 {
		t.Errorf("Expected %f for one component common prefix, got %f", expectedOne, sim)
	}
}

// Helper function for floating point comparison
func absFloat(x float64) float64 {
	if x < 0 {
		return -x
	}
	return x
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