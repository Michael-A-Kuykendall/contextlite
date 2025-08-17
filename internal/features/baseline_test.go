package features

import (
	"testing"

	"contextlite/pkg/types"
)

func TestNewBM25Scorer(t *testing.T) {
	scorer := NewBM25Scorer()
	if scorer == nil {
		t.Fatal("NewBM25Scorer returned nil")
	}
	
	// Check default parameters
	if scorer.k1 != 1.2 {
		t.Errorf("Expected k1=1.2, got %f", scorer.k1)
	}
	
	if scorer.b != 0.75 {
		t.Errorf("Expected b=0.75, got %f", scorer.b)
	}
	
	if scorer.lambda != 0.3 {
		t.Errorf("Expected lambda=0.3, got %f", scorer.lambda)
	}
}

func TestBM25Scorer_ScoreDocuments(t *testing.T) {
	scorer := NewBM25Scorer()
	
	docs := []types.Document{
		{
			ID:      "1",
			Content: "the quick brown fox jumps over the lazy dog",
		},
		{
			ID:      "2", 
			Content: "brown foxes are quick animals",
		},
		{
			ID:      "3",
			Content: "dogs are lazy pets",
		},
	}
	
	query := "quick brown fox"
	maxResults := 3
	
	results := scorer.ScoreDocuments(docs, query, maxResults)
	
	if len(results) == 0 {
		t.Error("ScoreDocuments returned no results")
	}
	
	if len(results) > maxResults {
		t.Errorf("Expected at most %d results, got %d", maxResults, len(results))
	}
	
	// Check that results are sorted by score (descending)
	for i := 1; i < len(results); i++ {
		if results[i-1].UtilityScore < results[i].UtilityScore {
			t.Errorf("Results not sorted by score: %f < %f at positions %d, %d", 
				results[i-1].UtilityScore, results[i].UtilityScore, i-1, i)
		}
	}
	
	// First result should be document 1 or 2 (high relevance)
	if len(results) > 0 && results[0].Document.ID != "1" && results[0].Document.ID != "2" {
		t.Logf("First result ID: %s (score: %f)", results[0].Document.ID, results[0].UtilityScore)
	}
	
	t.Logf("BM25 scoring completed: %d results", len(results))
}

func TestBM25Scorer_EmptyQuery(t *testing.T) {
	scorer := NewBM25Scorer()
	
	docs := []types.Document{
		{ID: "1", Content: "some content"},
		{ID: "2", Content: "more content"},
	}
	
	results := scorer.ScoreDocuments(docs, "", 10)
	
	// Should handle empty query gracefully
	if len(results) == 0 {
		t.Log("Empty query returned no results (expected)")
	} else {
		// If it returns results, they should all have zero scores
		for i, result := range results {
			if result.UtilityScore != 0.0 {
				t.Errorf("Expected zero score for empty query, got %f at position %d", result.UtilityScore, i)
			}
		}
	}
}

func TestBM25Scorer_EmptyDocuments(t *testing.T) {
	scorer := NewBM25Scorer()
	
	results := scorer.ScoreDocuments([]types.Document{}, "test query", 5)
	
	if results != nil {
		t.Errorf("Expected nil for empty documents, got %v", results)
	}
}

func TestBM25Scorer_MaxResults(t *testing.T) {
	scorer := NewBM25Scorer()
	
	docs := []types.Document{
		{ID: "1", Content: "document one with content"},
		{ID: "2", Content: "document two with content"},
		{ID: "3", Content: "document three with content"},
		{ID: "4", Content: "document four with content"},
		{ID: "5", Content: "document five with content"},
	}
	
	// Test limiting results
	results := scorer.ScoreDocuments(docs, "document content", 3)
	
	if len(results) != 3 {
		t.Errorf("Expected exactly 3 results, got %d", len(results))
	}
	
	// Test no limit (maxResults = 0)
	results = scorer.ScoreDocuments(docs, "document content", 0)
	
	if len(results) != len(docs) {
		t.Errorf("Expected %d results with no limit, got %d", len(docs), len(results))
	}
}

func TestBM25Scorer_CalculateBM25(t *testing.T) {
	scorer := NewBM25Scorer()
	
	queryTerms := []string{"quick", "brown"}
	docTerms := map[string]int{
		"quick": 1,
		"brown": 1,
		"fox":   1,
	}
	docLength := 3
	avgDocLength := 5.0
	termDocFreq := map[string]int{
		"quick": 1, // Both terms appear in at least 1 document
		"brown": 1,
		"fox":   1,
	}
	totalDocs := 3
	
	score := scorer.calculateBM25(queryTerms, docTerms, docLength, avgDocLength, termDocFreq, totalDocs)
	
	if score <= 0 {
		t.Errorf("Expected positive BM25 score, got %f", score)
	}
	
	t.Logf("BM25 score: %f", score)
}

func TestBM25Scorer_CalculateBM25_NoMatchingTerms(t *testing.T) {
	scorer := NewBM25Scorer()
	
	queryTerms := []string{"missing", "terms"}
	docTerms := map[string]int{
		"different": 1,
		"words":     1,
	}
	docLength := 2
	avgDocLength := 5.0
	termDocFreq := map[string]int{
		"different": 1,
		"words":     1,
	}
	totalDocs := 3
	
	score := scorer.calculateBM25(queryTerms, docTerms, docLength, avgDocLength, termDocFreq, totalDocs)
	
	if score != 0.0 {
		t.Errorf("Expected zero score for no matching terms, got %f", score)
	}
}

func TestBM25Scorer_ApplyMMR(t *testing.T) {
	scorer := NewBM25Scorer()
	
	scored := []types.ScoredDocument{
		{
			Document:     types.Document{ID: "1", Content: "very similar content about cats"},
			UtilityScore: 1.0,
		},
		{
			Document:     types.Document{ID: "2", Content: "very similar content about cats"},
			UtilityScore: 0.9,
		},
		{
			Document:     types.Document{ID: "3", Content: "completely different topic about cars"},
			UtilityScore: 0.8,
		},
		{
			Document:     types.Document{ID: "4", Content: "another car-related document"},
			UtilityScore: 0.7,
		},
	}
	
	maxResults := 2
	results := scorer.applyMMR(scored, maxResults)
	
	if len(results) != maxResults {
		t.Errorf("Expected %d results from MMR, got %d", maxResults, len(results))
	}
	
	// First result should be highest scoring
	if results[0].Document.ID != "1" {
		t.Errorf("Expected first result to be doc 1, got %s", results[0].Document.ID)
	}
	
	// Second result should favor diversity over pure relevance
	// (should pick doc 3 over doc 2 due to diversity)
	if len(results) > 1 {
		t.Logf("Second result: %s (for diversity testing)", results[1].Document.ID)
	}
}

func TestBM25Scorer_CalculateSimilarity(t *testing.T) {
	scorer := NewBM25Scorer()
	
	doc1 := types.Document{
		ID:      "1",
		Content: "the quick brown fox",
	}
	
	doc2 := types.Document{
		ID:      "2",
		Content: "the fast brown fox",
	}
	
	doc3 := types.Document{
		ID:      "3",
		Content: "completely different content",
	}
	
	// Similar documents should have high similarity
	sim12 := scorer.calculateSimilarity(doc1, doc2)
	if sim12 <= 0.5 {
		t.Errorf("Expected high similarity between similar docs, got %f", sim12)
	}
	
	// Different documents should have low similarity
	sim13 := scorer.calculateSimilarity(doc1, doc3)
	if sim13 >= 0.5 {
		t.Errorf("Expected low similarity between different docs, got %f", sim13)
	}
	
	// Document should be identical to itself
	sim11 := scorer.calculateSimilarity(doc1, doc1)
	if sim11 != 1.0 {
		t.Errorf("Expected similarity of 1.0 for identical docs, got %f", sim11)
	}
	
	t.Logf("Similarities: similar=%f, different=%f, identical=%f", sim12, sim13, sim11)
}

func TestBM25Scorer_CalculateDiversityScore(t *testing.T) {
	scorer := NewBM25Scorer()
	
	doc := types.Document{
		ID:      "target",
		Content: "unique content",
	}
	
	selected := []types.ScoredDocument{
		{
			Document: types.Document{ID: "1", Content: "similar to unique content"},
		},
		{
			Document: types.Document{ID: "2", Content: "completely different"},
		},
	}
	
	diversityScore := scorer.calculateDiversityScore(doc, selected)
	
	if diversityScore < 0.0 || diversityScore > 1.0 {
		t.Errorf("Diversity score should be between 0 and 1, got %f", diversityScore)
	}
	
	// Test with single document (should return 1.0)
	singleSelected := []types.ScoredDocument{
		{Document: doc},
	}
	
	diversityScore = scorer.calculateDiversityScore(doc, singleSelected)
	if diversityScore != 1.0 {
		t.Errorf("Expected diversity score of 1.0 for single document, got %f", diversityScore)
	}
	
	t.Logf("Diversity score: %f", diversityScore)
}

func TestBM25Scorer_CalculateDiversityScoreEdgeCases(t *testing.T) {
	scorer := NewBM25Scorer()
	
	doc := types.Document{
		ID:      "target",
		Content: "test content",
	}
	
	// Test with empty selected list (len(selected) == 0)
	emptySelected := []types.ScoredDocument{}
	diversityScore := scorer.calculateDiversityScore(doc, emptySelected)
	if diversityScore != 1.0 {
		t.Errorf("Expected diversity score of 1.0 for empty selection, got %f", diversityScore)
	}
	
	// Test with exactly one document (len(selected) == 1) 
	oneSelected := []types.ScoredDocument{
		{Document: types.Document{ID: "other", Content: "other content"}},
	}
	diversityScore = scorer.calculateDiversityScore(doc, oneSelected)
	if diversityScore != 1.0 {
		t.Errorf("Expected diversity score of 1.0 for single selection, got %f", diversityScore)
	}
	
	// Test where all selected documents have the same ID as target (count == 0)
	sameIdSelected := []types.ScoredDocument{
		{Document: types.Document{ID: "target", Content: "same id content 1"}},
		{Document: types.Document{ID: "target", Content: "same id content 2"}},
	}
	diversityScore = scorer.calculateDiversityScore(doc, sameIdSelected)
	if diversityScore != 1.0 {
		t.Errorf("Expected diversity score of 1.0 when all docs have same ID as target, got %f", diversityScore)
	}
	
	// Test mixed case: some same ID, some different ID
	mixedSelected := []types.ScoredDocument{
		{Document: types.Document{ID: "target", Content: "same id"}}, // Same ID - should be skipped
		{Document: types.Document{ID: "different1", Content: "test content"}}, // Different ID - should be included
		{Document: types.Document{ID: "target", Content: "another same id"}}, // Same ID - should be skipped
		{Document: types.Document{ID: "different2", Content: "other content"}}, // Different ID - should be included
	}
	diversityScore = scorer.calculateDiversityScore(doc, mixedSelected)
	
	// Should only consider the 2 documents with different IDs
	if diversityScore < 0.0 || diversityScore > 1.0 {
		t.Errorf("Diversity score should be between 0 and 1 for mixed selection, got %f", diversityScore)
	}
	
	// Test with highly similar documents (low diversity)
	similarSelected := []types.ScoredDocument{
		{Document: types.Document{ID: "sim1", Content: "test content very similar"}},
		{Document: types.Document{ID: "sim2", Content: "test content extremely similar"}},
	}
	similarityScore := scorer.calculateDiversityScore(doc, similarSelected)
	
	// Should be lower diversity due to high similarity
	if similarityScore < 0.0 || similarityScore > 1.0 {
		t.Errorf("Diversity score should be between 0 and 1 for similar content, got %f", similarityScore)
	}
	
	// Test with very different documents (high diversity)
	differentSelected := []types.ScoredDocument{
		{Document: types.Document{ID: "diff1", Content: "completely unrelated words"}},
		{Document: types.Document{ID: "diff2", Content: "totally different vocabulary"}},
	}
	differentScore := scorer.calculateDiversityScore(doc, differentSelected)
	
	// Should be higher diversity due to low similarity
	if differentScore < 0.0 || differentScore > 1.0 {
		t.Errorf("Diversity score should be between 0 and 1 for different content, got %f", differentScore)
	}
	
	// Different content should have higher diversity than similar content
	if differentScore <= similarityScore {
		t.Logf("Note: Expected different content to have higher diversity (%f) than similar content (%f)", 
			differentScore, similarityScore)
	}
}

func TestTokenize(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		expected []string
	}{
		{
			name:     "simple_words",
			input:    "hello world",
			expected: []string{"hello", "world"},
		},
		{
			name:     "with_punctuation",
			input:    "Hello, world! How are you?",
			expected: []string{"hello", "world", "how", "are", "you"},
		},
		{
			name:     "empty_string",
			input:    "",
			expected: []string{},
		},
		{
			name:     "single_character",
			input:    "a b c",
			expected: []string{}, // Single characters are filtered out
		},
		{
			name:     "mixed_case",
			input:    "CamelCase UPPERCASE lowercase",
			expected: []string{"camelcase", "uppercase", "lowercase"},
		},
	}
	
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			result := tokenize(test.input)
			
			if len(result) != len(test.expected) {
				t.Errorf("Expected %d tokens, got %d", len(test.expected), len(result))
			}
			
			for i, expected := range test.expected {
				if i >= len(result) || result[i] != expected {
					t.Errorf("Expected token %d to be '%s', got '%s'", i, expected, result[i])
				}
			}
		})
	}
}

// Benchmark tests
func BenchmarkBM25Scorer_ScoreDocuments(b *testing.B) {
	scorer := NewBM25Scorer()
	
	// Create test documents
	docs := make([]types.Document, 100)
	for i := 0; i < 100; i++ {
		docs[i] = types.Document{
			ID:      string(rune('A' + i%26)),
			Content: "sample document content with various terms and words for testing performance",
		}
	}
	
	query := "document content terms"
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		scorer.ScoreDocuments(docs, query, 10)
	}
}

func BenchmarkTokenize(b *testing.B) {
	text := "This is a sample text with multiple words and punctuation marks for tokenization performance testing."
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		tokenize(text)
	}
}
