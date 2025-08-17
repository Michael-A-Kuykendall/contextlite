package features

import (
	"testing"
	"math"
	"time"

	"contextlite/pkg/types"
)

// TestRelevanceFormula tests BM25 relevance calculation
func TestRelevanceFormula(t *testing.T) {
	fe := &FeatureExtractor{}
	
	// Test case: query="security auth" matching document
	query := "security auth"
	queryTerms := map[string]int{"security": 1, "auth": 1}
	docTerms := map[string]int{"security": 2, "auth": 1, "system": 1}
	docFreq := map[string]int{"security": 10, "auth": 5, "system": 20}
	totalDocs := 100
	
	relevance := fe.computeRelevance(query, queryTerms, docTerms, docFreq, totalDocs)
	
	// Expected: positive relevance score for matching terms
	if relevance <= 0 {
		t.Errorf("Expected positive relevance, got %f", relevance)
	}
	
	// Test non-matching document
	docTermsEmpty := map[string]int{"unrelated": 1, "terms": 1}
	relevanceEmpty := fe.computeRelevance(query, queryTerms, docTermsEmpty, docFreq, totalDocs)
	
	if relevanceEmpty != 0 {
		t.Errorf("Expected zero relevance for non-matching doc, got %f", relevanceEmpty)
	}
}

// TestRecencyFormula tests exponential decay calculation
func TestRecencyFormula(t *testing.T) {
	fe := &FeatureExtractor{}
	
	now := time.Now().Unix()
	
	// Test current document (modified now)
	recencyNow := fe.computeRecency(now)
	if math.Abs(recencyNow - 1.0) > 0.01 {
		t.Errorf("Expected recency ~1.0 for current doc, got %f", recencyNow)
	}
	
	// Test 7-day old document (should be ~0.5 due to half-life)
	sevenDaysAgo := now - 7*24*3600
	recencyWeek := fe.computeRecency(sevenDaysAgo)
	expected := 0.5
	if math.Abs(recencyWeek - expected) > 0.05 {
		t.Errorf("Expected recency ~0.5 for 7-day old doc, got %f", recencyWeek)
	}
	
	// Test 14-day old document (should be ~0.25)
	fourteenDaysAgo := now - 14*24*3600
	recencyTwoWeeks := fe.computeRecency(fourteenDaysAgo)
	expected = 0.25
	if math.Abs(recencyTwoWeeks - expected) > 0.05 {
		t.Errorf("Expected recency ~0.25 for 14-day old doc, got %f", recencyTwoWeeks)
	}
}

// TestEntanglementFormula tests PMI-based concept density
func TestEntanglementFormula(t *testing.T) {
	fe := &FeatureExtractor{}
	
	// Test document with multiple related terms (should have positive PMI)
	docTerms := map[string]int{
		"security": 5,
		"authentication": 3,
		"authorization": 2,
		"access": 4,
		"control": 3,
		"system": 2,
		"user": 2,
		"policy": 1,
		"permission": 1,
		"admin": 1,
	}
	docFreq := map[string]int{
		"security": 10, "authentication": 8, "authorization": 6,
		"access": 12, "control": 9, "system": 15, "user": 20,
		"policy": 5, "permission": 7, "admin": 3,
	}
	
	entanglement := fe.computeEntanglement(docTerms, docFreq, 100)
	
	// Entanglement should be non-negative for documents with multiple terms
	if entanglement < 0 {
		t.Errorf("Expected non-negative entanglement, got %f", entanglement)
	}
	
	// Test single-term document (should be 0)
	singleTermDoc := map[string]int{"isolated": 1}
	entanglementSingle := fe.computeEntanglement(singleTermDoc, docFreq, 100)
	if entanglementSingle != 0 {
		t.Errorf("Expected zero entanglement for single-term doc, got %f", entanglementSingle)
	}
}

// TestAuthorityFormula tests document importance calculation
func TestAuthorityFormula(t *testing.T) {
	fe := &FeatureExtractor{}
	
	// Test large document (should have higher authority)
	largeDoc := types.Document{
		TokenCount: 5000,
		Content:    generateLargeContent(10000), // 10KB content
	}
	
	authorityLarge := fe.computeAuthority(largeDoc)
	
	// Test small document
	smallDoc := types.Document{
		TokenCount: 100,
		Content:    "Small content",
	}
	
	authoritySmall := fe.computeAuthority(smallDoc)
	
	// Large document should have higher authority
	if authorityLarge <= authoritySmall {
		t.Errorf("Expected larger doc to have higher authority: large=%f, small=%f", 
			authorityLarge, authoritySmall)
	}
	
	// Authority should be in [0,1] range
	if authorityLarge < 0 || authorityLarge > 1 {
		t.Errorf("Authority should be in [0,1], got %f", authorityLarge)
	}
}

// TestSpecificityFormula tests query-document topic alignment
func TestSpecificityFormula(t *testing.T) {
	fe := &FeatureExtractor{}
	
	query := "machine learning algorithms"
	queryTerms := map[string]int{"machine": 1, "learning": 1, "algorithms": 1}
	
	// Test highly specific document (contains all query terms)
	specificDocTerms := map[string]int{
		"machine": 2, "learning": 3, "algorithms": 2,
	}
	
	specificityHigh := fe.computeSpecificity(query, queryTerms, specificDocTerms)
	
	// Test less specific document (contains some query terms + others)
	generalDocTerms := map[string]int{
		"machine": 1, "learning": 1,
		"other": 5, "terms": 3, "unrelated": 4,
	}
	
	specificityLow := fe.computeSpecificity(query, queryTerms, generalDocTerms)
	
	// Specific document should score higher
	if specificityHigh <= specificityLow {
		t.Errorf("Expected specific doc to score higher: specific=%f, general=%f",
			specificityHigh, specificityLow)
	}
	
	// Specificity should be in [0,1] range
	if specificityHigh < 0 || specificityHigh > 1 {
		t.Errorf("Specificity should be in [0,1], got %f", specificityHigh)
	}
}

// TestUncertaintyFormula tests score variance calculation
func TestUncertaintyFormula(t *testing.T) {
	fe := &FeatureExtractor{}
	
	query := "test query"
	docTerms := map[string]int{"test": 2, "query": 1, "content": 3}
	docFreq := map[string]int{"test": 10, "query": 8, "content": 15}
	totalDocs := 100
	
	uncertainty := fe.computeUncertainty(query, docTerms, docFreq, totalDocs)
	
	// Uncertainty should be non-negative
	if uncertainty < 0 {
		t.Errorf("Uncertainty should be non-negative, got %f", uncertainty)
	}
	
	// Should be finite
	if math.IsInf(uncertainty, 0) || math.IsNaN(uncertainty) {
		t.Errorf("Uncertainty should be finite, got %f", uncertainty)
	}
}

// TestPriorFormula tests historical selection likelihood
func TestPriorFormula(t *testing.T) {
	fe := &FeatureExtractor{}
	
	// Test documents with different characteristics
	popularDoc := types.Document{
		Path: "frequently/accessed/document.md",
		Language: "markdown",
	}
	
	rareDoc := types.Document{
		Path: "rarely/accessed/document.txt", 
		Language: "text",
	}
	
	priorPopular := fe.computePrior(popularDoc)
	priorRare := fe.computePrior(rareDoc)
	
	// Both should be non-negative
	if priorPopular < 0 || priorRare < 0 {
		t.Errorf("Prior scores should be non-negative: popular=%f, rare=%f",
			priorPopular, priorRare)
	}
}

// TestFeatureSetIndependence verifies features are set-independent
func TestFeatureSetIndependence(t *testing.T) {
	fe := &FeatureExtractor{}
	
	// Create test document and query
	doc := types.Document{
		Content: "security authentication systems",
		ModifiedTime: time.Now().Unix() - 3600, // 1 hour ago
		TokenCount: 100,
		Path: "test/security.md",
		Language: "markdown",
	}
	
	query := "security systems"
	docTerms := map[string]int{"security": 1, "authentication": 1, "systems": 1}
	queryTerms := map[string]int{"security": 1, "systems": 1}
	docFreq := map[string]int{"security": 10, "authentication": 5, "systems": 15}
	
	// Extract features
	features := fe.extractRawFeatures(doc, query, queryTerms, docTerms, docFreq, 100)
	
	// Verify all features are computable and finite
	featureValues := []float64{
		features.Relevance,
		features.Recency,
		features.Entanglement,
		features.Prior,
		features.Uncertainty,
		features.Authority,
		features.Specificity,
	}
	
	for i, value := range featureValues {
		if math.IsNaN(value) || math.IsInf(value, 0) {
			t.Errorf("Feature %d should be finite, got %f", i, value)
		}
	}
	
	// Verify features depend only on (query, document) pair
	// Re-computing with same inputs should give identical results
	features2 := fe.extractRawFeatures(doc, query, queryTerms, docTerms, docFreq, 100)
	
	tolerance := 1e-10
	if math.Abs(features.Relevance-features2.Relevance) > tolerance ||
		math.Abs(features.Recency-features2.Recency) > tolerance ||
		math.Abs(features.Entanglement-features2.Entanglement) > tolerance ||
		math.Abs(features.Prior-features2.Prior) > tolerance ||
		math.Abs(features.Uncertainty-features2.Uncertainty) > tolerance ||
		math.Abs(features.Authority-features2.Authority) > tolerance ||
		math.Abs(features.Specificity-features2.Specificity) > tolerance {
		t.Errorf("Features should be deterministic for same inputs")
		t.Errorf("First:  %+v", features)
		t.Errorf("Second: %+v", features2)
	}
}

// Helper function to generate large content for testing
func generateLargeContent(size int) string {
	content := ""
	text := "This is sample content for testing document authority calculations. "
	for len(content) < size {
		content += text
	}
	return content[:size]
}

// TestFeatureNormalization tests the normalization process
func TestFeatureNormalization(t *testing.T) {
	// Create mock normalization stats
	normStats := &types.NormalizationStats{
		Mean: map[string]float64{
			"relevance": 2.0, "recency": 0.5, "entanglement": 0.1, "prior": 1.0,
			"uncertainty": 0.3, "authority": 0.4, "specificity": 0.6,
		},
		StdDev: map[string]float64{
			"relevance": 1.0, "recency": 0.2, "entanglement": 0.05, "prior": 0.5,
			"uncertainty": 0.1, "authority": 0.1, "specificity": 0.2,
		},
		Count: 100,
	}
	
	fe := &FeatureExtractor{normStats: normStats}
	
	// Test raw features
	rawFeatures := types.FeatureVector{
		Relevance: 3.0,    // (3.0 - 2.0) / 1.0 = 1.0
		Recency: 0.7,      // (0.7 - 0.5) / 0.2 = 1.0  
		Entanglement: 0.15, // (0.15 - 0.1) / 0.05 = 1.0
		Prior: 1.5,        // (1.5 - 1.0) / 0.5 = 1.0
		Uncertainty: 0.4,  // (0.4 - 0.3) / 0.1 = 1.0
		Authority: 0.5,    // (0.5 - 0.4) / 0.1 = 1.0
		Specificity: 0.8,  // (0.8 - 0.6) / 0.2 = 1.0
	}
	
	normalized := fe.normalizeFeatures(rawFeatures)
	
	// With sigmoid normalization, all values should be in [0,1] range
	actualValues := []float64{
		normalized.Relevance, normalized.Recency, normalized.Entanglement,
		normalized.Prior, normalized.Uncertainty, normalized.Authority, normalized.Specificity,
	}
	
	for i, value := range actualValues {
		if value < 0 || value > 1 {
			t.Errorf("Normalized feature %d should be in [0,1], got %f", i, value)
		}
	}
	
	// Values should be approximately 0.5 + sigmoid transform
	// For z-score = 1.0, sigmoid(1.0) ≈ 0.73
	expected := 1.0 / (1.0 + math.Exp(-1.0)) // ≈ 0.73
	for i, value := range actualValues {
		if math.Abs(value - expected) > 0.05 {
			t.Errorf("Normalized feature %d: expected ~%f, got %f", i, expected, value)
		}
	}
}
