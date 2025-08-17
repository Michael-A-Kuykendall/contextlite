package features

import (
	"context"
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