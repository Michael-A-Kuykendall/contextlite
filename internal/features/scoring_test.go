package features

import (
	"context"
	"math"
	"strings"
	"testing"
	"time"

	"contextlite/pkg/types"
)

func TestNewFeatureExtractor(t *testing.T) {
	normStats := &types.NormalizationStats{
		Mean: map[string]float64{
			"relevance":    0.5,
			"recency":      0.5,
			"entanglement": 0.5,
			"prior":        0.5,
			"uncertainty":  0.5,
			"authority":    0.5,
			"specificity":  0.5,
		},
		StdDev: map[string]float64{
			"relevance":    0.2,
			"recency":      0.2,
			"entanglement": 0.2,
			"prior":        0.2,
			"uncertainty":  0.2,
			"authority":    0.2,
			"specificity":  0.2,
		},
		Count: 100,
	}
	
	extractor := NewFeatureExtractor("/test/workspace", normStats)
	if extractor == nil {
		t.Fatal("NewFeatureExtractor returned nil")
	}
	
	if extractor.workspacePath != "/test/workspace" {
		t.Errorf("Expected workspace path '/test/workspace', got '%s'", extractor.workspacePath)
	}
}

func TestFeatureExtractor_ExtractFeatures(t *testing.T) {
	normStats := &types.NormalizationStats{
		Mean: map[string]float64{
			"relevance":    0.5,
			"recency":      0.5,
			"entanglement": 0.5,
			"prior":        0.5,
			"uncertainty":  0.5,
			"authority":    0.5,
			"specificity":  0.5,
		},
		StdDev: map[string]float64{
			"relevance":    0.2,
			"recency":      0.2,
			"entanglement": 0.2,
			"prior":        0.2,
			"uncertainty":  0.2,
			"authority":    0.2,
			"specificity":  0.2,
		},
		Count: 100,
	}
	
	extractor := NewFeatureExtractor("/test/workspace", normStats)
	
	docs := []types.Document{
		{
			ID:           "1",
			Content:      "machine learning algorithms and data science",
			Path:         "/test/ml.txt",
			ModifiedTime: time.Now().Unix(),
		},
		{
			ID:           "2", 
			Content:      "artificial intelligence and neural networks",
			Path:         "/test/ai.txt",
			ModifiedTime: time.Now().Unix() - 86400, // 1 day ago
		},
	}
	
	ctx := context.Background()
	results, err := extractor.ExtractFeatures(ctx, docs, "machine learning")
	
	if err != nil {
		t.Fatalf("ExtractFeatures failed: %v", err)
	}
	
	if len(results) != len(docs) {
		t.Errorf("Expected %d results, got %d", len(docs), len(results))
	}
	
	for i, result := range results {
		if result.Document.ID != docs[i].ID {
			t.Errorf("Result %d: expected ID %s, got %s", i, docs[i].ID, result.Document.ID)
		}
		
		// Check that features are within expected ranges [0, 1]
		features := result.Features
		
		if features.Relevance < 0 || features.Relevance > 1 {
			t.Errorf("Relevance score out of range [0,1]: %f", features.Relevance)
		}
		
		if features.Recency < 0 || features.Recency > 1 {
			t.Errorf("Recency score out of range [0,1]: %f", features.Recency)
		}
		
		// Check utility score is computed
		if result.UtilityScore <= 0 {
			t.Errorf("Expected positive utility score, got %f", result.UtilityScore)
		}
	}
}

func TestComputeRelevance(t *testing.T) {
	normStats := &types.NormalizationStats{
		Mean:   map[string]float64{},
		StdDev: map[string]float64{},
		Count:  100,
	}
	
	extractor := NewFeatureExtractor("/test/workspace", normStats)
	
	queryTerms := map[string]int{
		"machine":  1,
		"learning": 1,
	}
	
	docTerms := map[string]int{
		"machine":    1,
		"learning":   1,
		"algorithms": 1,
	}
	
	docFreq := map[string]int{
		"machine":    1,
		"learning":   1,
		"algorithms": 1,
	}
	
	totalDocs := 5
	
	relevance := extractor.computeRelevance("machine learning", queryTerms, docTerms, docFreq, totalDocs)
	
	if relevance <= 0 {
		t.Errorf("Expected positive relevance score, got %f", relevance)
	}
	
	// Test with no matching terms
	docTermsNoMatch := map[string]int{
		"different": 1,
		"words":     1,
	}
	
	relevance = extractor.computeRelevance("machine learning", queryTerms, docTermsNoMatch, docFreq, totalDocs)
	
	if relevance != 0 {
		t.Errorf("Expected zero relevance for no matching terms, got %f", relevance)
	}
}

func TestComputeRelevanceEdgeCases(t *testing.T) {
	normStats := &types.NormalizationStats{
		Mean:   map[string]float64{},
		StdDev: map[string]float64{},
		Count:  100,
	}
	
	extractor := NewFeatureExtractor("/test/workspace", normStats)
	
	// Test with zero document frequency (df == 0) - should skip term
	queryTerms := map[string]int{
		"term1": 1,
		"term2": 1,
	}
	
	docTerms := map[string]int{
		"term1": 1,
		"term2": 1,
	}
	
	docFreqZero := map[string]int{
		"term1": 0, // Zero frequency - should be skipped
		"term2": 1, // Normal frequency
	}
	
	relevance := extractor.computeRelevance("term1 term2", queryTerms, docTerms, docFreqZero, 5)
	
	// Should only get contribution from term2, not term1 due to df == 0
	if relevance <= 0 {
		t.Errorf("Expected positive relevance from term2 despite term1 having df=0, got %f", relevance)
	}
	
	// Test with missing docFreq entries (should continue loop)
	incompleteDocFreq := map[string]int{
		"term2": 1,
		// "term1" missing - should be treated as 0 and skipped
	}
	
	relevance2 := extractor.computeRelevance("term1 term2", queryTerms, docTerms, incompleteDocFreq, 5)
	
	// Should only get contribution from term2
	if relevance2 <= 0 {
		t.Errorf("Expected positive relevance from term2 despite term1 missing from docFreq, got %f", relevance2)
	}
	
	// Test with totalDocs > 1 to trigger avgDocLen calculation path
	relevanceMultiDoc := extractor.computeRelevance("term2", map[string]int{"term2": 1}, docTerms, docFreqZero, 10)
	
	// Should be valid (though may be 0 due to df=0 for term2 in this setup)
	if relevanceMultiDoc < 0 {
		t.Errorf("Expected non-negative relevance for multiple docs, got %f", relevanceMultiDoc)
	}
	
	// Test with very high document frequency that could cause denominator edge case
	docFreqHigh := map[string]int{
		"common_term": 100, // Very high frequency
	}
	
	queryCommon := map[string]int{
		"common_term": 1,
	}
	
	docCommon := map[string]int{
		"common_term": 5,
	}
	
	// Test with totalDocs equal to df (edge case for IDF calculation)
	relevanceEdge := extractor.computeRelevance("common_term", queryCommon, docCommon, docFreqHigh, 100)
	
	// BM25 can produce negative values when IDF is negative (common terms)
	// Just verify the calculation doesn't crash and produces a finite value
	if !isFinite(relevanceEdge) {
		t.Errorf("Expected finite relevance for edge case IDF, got %f", relevanceEdge)
	}
	
	// Test with totalDocs == 1 (single document case)
	relevanceSingle := extractor.computeRelevance("term2", map[string]int{"term2": 1}, 
		map[string]int{"term2": 3}, map[string]int{"term2": 1}, 1)
	
	// Should use document's own length as avgDocLen
	// BM25 can be negative, just verify it's finite
	if !isFinite(relevanceSingle) {
		t.Errorf("Expected finite relevance for single document, got %f", relevanceSingle)
	}
}

// Helper function to check if a float is finite
func isFinite(f float64) bool {
	return !math.IsNaN(f) && !math.IsInf(f, 0)
}

func TestNormalizeFeatures(t *testing.T) {
	normStats := &types.NormalizationStats{
		Mean: map[string]float64{
			"relevance":    0.5,
			"recency":      0.5,
			"entanglement": 0.5,
			"prior":        0.5,
			"uncertainty":  0.5,
			"authority":    0.5,
			"specificity":  0.5,
		},
		StdDev: map[string]float64{
			"relevance":    0.2,
			"recency":      0.2,
			"entanglement": 0.2,
			"prior":        0.2,
			"uncertainty":  0.2,
			"authority":    0.2,
			"specificity":  0.2,
		},
		Count: 100,
	}
	
	extractor := NewFeatureExtractor("/test/workspace", normStats)
	
	// Test normal case
	raw := types.FeatureVector{
		Relevance:    0.7,  // Above mean
		Recency:      0.3,  // Below mean
		Entanglement: 0.5,  // At mean
		Prior:        0.9,  // Well above mean
		Uncertainty:  0.1,  // Well below mean
		Authority:    0.5,  // At mean
		Specificity:  0.8,  // Above mean
	}
	
	normalized := extractor.normalizeFeatures(raw)
	
	// Check that values are reasonable (within several standard deviations)
	if normalized.Relevance < -5 || normalized.Relevance > 5 {
		t.Errorf("Normalized relevance seems out of range: %f", normalized.Relevance)
	}
	
	// Test with zero standard deviation
	zeroStdStats := &types.NormalizationStats{
		Mean: map[string]float64{
			"relevance": 0.5,
		},
		StdDev: map[string]float64{
			"relevance": 0.0,  // Zero std dev
		},
		Count: 100,
	}
	
	extractorZero := NewFeatureExtractor("/test/workspace", zeroStdStats)
	normalizedZero := extractorZero.normalizeFeatures(raw)
	
	// Should return 0.5 for zero std dev (constant values)
	if normalizedZero.Relevance != 0.5 {
		t.Errorf("Zero std dev should return 0.5 for constant values: expected 0.5, got %f", normalizedZero.Relevance)
	}
	
	// Test with missing normalization stats
	partialStats := &types.NormalizationStats{
		Mean: map[string]float64{
			"relevance": 0.5,
		},
		StdDev: map[string]float64{
			"relevance": 0.2,
		},
		Count: 100,
	}
	
	extractorPartial := NewFeatureExtractor("/test/workspace", partialStats)
	rawPartial := types.FeatureVector{
		Relevance: 0.7,
		Recency:   0.3, // No normalization stats for this
	}
	
	normalizedPartial := extractorPartial.normalizeFeatures(rawPartial)
	
	// Should use fallback for missing stats (0.5 for missing mean/stddev)
	if normalizedPartial.Recency != 0.5 {
		t.Errorf("Expected 0.5 for missing normalization stats, got %f", normalizedPartial.Recency)
	}
}

func TestNormalizeFeaturesNilStats(t *testing.T) {
	// Test with nil normalization stats
	extractorNil := NewFeatureExtractor("/test/workspace", nil)
	
	raw := types.FeatureVector{
		Relevance:    1.5,  // Above 1
		Recency:      -0.3, // Below 0
		Entanglement: 0.5,  // Normal
		Prior:        2.0,  // Well above 1
		Uncertainty:  -1.0, // Well below 0
		Authority:    0.5,  // Normal
		Specificity:  0.8,  // Normal
	}
	
	normalized := extractorNil.normalizeFeatures(raw)
	
	// Should clamp values to [0,1] range
	if normalized.Relevance != 1.0 {
		t.Errorf("Expected relevance clamped to 1.0, got %f", normalized.Relevance)
	}
	if normalized.Recency != 0.0 {
		t.Errorf("Expected recency clamped to 0.0, got %f", normalized.Recency)
	}
	if normalized.Prior != 1.0 {
		t.Errorf("Expected prior clamped to 1.0, got %f", normalized.Prior)
	}
	if normalized.Uncertainty != 0.0 {
		t.Errorf("Expected uncertainty clamped to 0.0, got %f", normalized.Uncertainty)
	}
}

func TestNormalizeFeaturesZeroCount(t *testing.T) {
	// Test with zero count (should also use clamping path)
	zeroCountStats := &types.NormalizationStats{
		Mean:   map[string]float64{"relevance": 0.5},
		StdDev: map[string]float64{"relevance": 0.2},
		Count:  0, // Zero count should trigger clamping path
	}
	
	extractorZeroCount := NewFeatureExtractor("/test/workspace", zeroCountStats)
	
	raw := types.FeatureVector{
		Relevance:    1.2,  // Above 1
		Recency:      -0.1, // Below 0
		Entanglement: 0.7,  // Normal
	}
	
	normalized := extractorZeroCount.normalizeFeatures(raw)
	
	// Should clamp values to [0,1] range
	if normalized.Relevance != 1.0 {
		t.Errorf("Expected relevance clamped to 1.0 with zero count, got %f", normalized.Relevance)
	}
	if normalized.Recency != 0.0 {
		t.Errorf("Expected recency clamped to 0.0 with zero count, got %f", normalized.Recency)
	}
}

func TestNormalizeFeaturesMissingMapKeys(t *testing.T) {
	// Test with missing keys in mean/stddev maps (should default to 0.5)
	incompleteStats := &types.NormalizationStats{
		Mean: map[string]float64{
			"relevance": 0.5,
			// Missing other keys
		},
		StdDev: map[string]float64{
			"relevance": 0.2,
			// Missing other keys
		},
		Count: 100,
	}
	
	extractor := NewFeatureExtractor("/test/workspace", incompleteStats)
	
	raw := types.FeatureVector{
		Relevance:    0.7,
		Recency:      0.3, // No stats for this
		Entanglement: 0.5, // No stats for this
	}
	
	normalized := extractor.normalizeFeatures(raw)
	
	// Relevance should be normalized
	if normalized.Relevance == raw.Relevance {
		t.Error("Expected relevance to be normalized, but it remained unchanged")
	}
	
	// Other fields with missing stats should use stdDev=0 path -> return 0.5
	if normalized.Recency != 0.5 {
		t.Errorf("Expected recency to default to 0.5 for missing stats, got %f", normalized.Recency)
	}
	if normalized.Entanglement != 0.5 {
		t.Errorf("Expected entanglement to default to 0.5 for missing stats, got %f", normalized.Entanglement)
	}
}

// Helper function
func abs(x float64) float64 {
	if x < 0 {
		return -x
	}
	return x
}

func TestComputeRecencyEdgeCases(t *testing.T) {
	normStats := &types.NormalizationStats{
		Mean:   map[string]float64{},
		StdDev: map[string]float64{},
		Count:  100,
	}
	
	extractor := NewFeatureExtractor("/test/workspace", normStats)
	
	// Test old timestamp
	oldTime := time.Now().Add(-30 * 24 * time.Hour).Unix() // 30 days ago
	recencyOld := extractor.computeRecency(oldTime)
	if recencyOld >= 0.5 {
		t.Errorf("Expected old timestamp to have low recency, got %f", recencyOld)
	}
	
	// Test zero timestamp
	recencyZero := extractor.computeRecency(0)
	if recencyZero < 0 {
		t.Errorf("Expected zero timestamp to have valid recency, got %f", recencyZero)
	}
	
	// Test current timestamp
	currentTime := time.Now().Unix()
	recencyCurrent := extractor.computeRecency(currentTime)
	if recencyCurrent <= 0.8 {
		t.Errorf("Expected current timestamp to have high recency, got %f", recencyCurrent)
	}
}

func TestComputePriorEdgeCases(t *testing.T) {
	normStats := &types.NormalizationStats{
		Mean:   map[string]float64{},
		StdDev: map[string]float64{},
		Count:  100,
	}
	
	extractor := NewFeatureExtractor("/test/workspace", normStats)
	
	// Test very long document
	longDoc := types.Document{
		ID:      "long",
		Content: strings.Repeat("word ", 1000), // Very long document
	}
	priorLong := extractor.computePrior(longDoc)
	if priorLong <= 0 {
		t.Errorf("Expected long document to have positive prior, got %f", priorLong)
	}
	
	// Test empty document
	emptyDoc := types.Document{
		ID:      "empty",
		Content: "",
	}
	priorEmpty := extractor.computePrior(emptyDoc)
	if priorEmpty < 0 {
		t.Errorf("Expected empty document to have valid prior, got %f", priorEmpty)
	}
	
	// Test document with special characters
	specialDoc := types.Document{
		ID:      "special",
		Content: "!@#$%^&*()_+-=[]{}|;:,.<>?",
	}
	priorSpecial := extractor.computePrior(specialDoc)
	if priorSpecial < 0 {
		t.Errorf("Expected special character document to have valid prior, got %f", priorSpecial)
	}
	
	// Test document with Go language
	goDoc := types.Document{
		ID:       "go",
		Content:  "package main",
		Language: "go",
		Path:     "/src/main.go",
		ModifiedTime: time.Now().Unix() - 86400, // 1 day ago
	}
	priorGo := extractor.computePrior(goDoc)
	if priorGo <= 0.5 {
		t.Errorf("Expected Go document to have boosted prior, got %f", priorGo)
	}
	
	// Test document with main in path
	mainDoc := types.Document{
		ID:       "main",
		Content:  "main content",
		Path:     "/path/to/main.js",
		Language: "javascript",
	}
	priorMain := extractor.computePrior(mainDoc)
	if priorMain <= 0.5 {
		t.Errorf("Expected main path document to have boosted prior, got %f", priorMain)
	}
}

func TestComputeSpecificityEdgeCases(t *testing.T) {
	normStats := &types.NormalizationStats{
		Mean:   map[string]float64{},
		StdDev: map[string]float64{},
		Count:  100,
	}
	
	extractor := NewFeatureExtractor("/test/workspace", normStats)
	
	// Test with very common terms
	queryTerms := map[string]int{
		"the": 1,
		"and": 1,
		"a":   1,
	}
	docTerms := map[string]int{
		"the": 100,
		"and": 80,
		"a":   90,
	}
	specificity := extractor.computeSpecificity("the and a", queryTerms, docTerms)
	if specificity < 0 || specificity > 1 {
		t.Errorf("Specificity should be in [0,1], got %f", specificity)
	}
	
	// Test with rare terms
	rareQueryTerms := map[string]int{
		"specialized": 1,
		"unique":      1,
		"rare":        1,
	}
	rareDocTerms := map[string]int{
		"specialized": 5,
		"unique":      3,
		"rare":        2,
	}
	specificityRare := extractor.computeSpecificity("specialized unique rare", rareQueryTerms, rareDocTerms)
	if specificityRare < 0 || specificityRare > 1 {
		t.Errorf("Specificity should be in [0,1], got %f", specificityRare)
	}
	
	// Test with empty terms
	emptyQueryTerms := map[string]int{}
	emptyDocTerms := map[string]int{}
	specificityEmpty := extractor.computeSpecificity("", emptyQueryTerms, emptyDocTerms)
	if specificityEmpty != 0 {
		t.Errorf("Expected zero specificity for empty terms, got %f", specificityEmpty)
	}
}

func TestComputeAuthorityEdgeCases(t *testing.T) {
	normStats := &types.NormalizationStats{
		Mean:   map[string]float64{},
		StdDev: map[string]float64{},
		Count:  100,
	}
	
	extractor := NewFeatureExtractor("/test/workspace", normStats)
	
	// Test config files
	configDoc := types.Document{
		ID:      "config",
		Path:    "/project/config.yaml",
		Content: "configuration settings",
	}
	authorityConfig := extractor.computeAuthority(configDoc)
	if authorityConfig < 0 || authorityConfig > 1 {
		t.Errorf("Expected authority in [0,1] for config file, got %f", authorityConfig)
	}
	
	// Test README files
	readmeDoc := types.Document{
		ID:      "readme",
		Path:    "/project/README.md",
		Content: "project documentation",
	}
	authorityReadme := extractor.computeAuthority(readmeDoc)
	if authorityReadme < 0 || authorityReadme > 1 {
		t.Errorf("Expected authority in [0,1] for README file, got %f", authorityReadme)
	}
	
	// Test regular files
	regularDoc := types.Document{
		ID:      "regular",
		Path:    "/project/src/helper.js",
		Content: "helper functions",
	}
	authorityRegular := extractor.computeAuthority(regularDoc)
	if authorityRegular < 0 || authorityRegular > 1 {
		t.Errorf("Expected authority in [0,1] for regular file, got %f", authorityRegular)
	}
}