package features

import (
	"context"
	"math"
	"sort"
	"strings"
	"time"

	"contextlite/pkg/types"
)

// FeatureExtractor extracts 7D features from documents
type FeatureExtractor struct {
	workspacePath string
	normStats     *types.NormalizationStats
}

// NewFeatureExtractor creates a new feature extractor
func NewFeatureExtractor(workspacePath string, normStats *types.NormalizationStats) *FeatureExtractor {
	return &FeatureExtractor{
		workspacePath: workspacePath,
		normStats:     normStats,
	}
}

// ExtractFeatures extracts normalized 7D features for all documents
func (fe *FeatureExtractor) ExtractFeatures(ctx context.Context, docs []types.Document, query string) ([]types.ScoredDocument, error) {
	var scored []types.ScoredDocument

	// Build term frequency maps for all documents
	docTerms := make([]map[string]int, len(docs))
	allTerms := make(map[string]int)
	
	for i, doc := range docs {
		terms := extractTerms(doc.Content)
		docTerms[i] = terms
		for term, count := range terms {
			allTerms[term] += count
		}
	}

	queryTerms := extractTerms(query)
	
	for i, doc := range docs {
		features := fe.extractRawFeatures(doc, query, queryTerms, docTerms[i], allTerms, len(docs))
		normalizedFeatures := fe.normalizeFeatures(features)
		
		scored = append(scored, types.ScoredDocument{
			Document: doc,
			Features: normalizedFeatures,
			UtilityScore: fe.computeUtilityScore(normalizedFeatures),
		})
	}

	return scored, nil
}

// extractRawFeatures extracts raw feature values (before normalization)
func (fe *FeatureExtractor) extractRawFeatures(doc types.Document, query string, queryTerms, docTerms, allTerms map[string]int, totalDocs int) types.FeatureVector {
	return types.FeatureVector{
		Relevance:    fe.computeRelevance(query, queryTerms, docTerms, allTerms, totalDocs),
		Recency:      fe.computeRecency(doc.ModifiedTime),
		Entanglement: fe.computeEntanglement(docTerms, allTerms, totalDocs),
		Prior:        fe.computePrior(doc),
		Uncertainty:  fe.computeUncertainty(query, docTerms, allTerms, totalDocs),
		Authority:    fe.computeAuthority(doc),
		Specificity:  fe.computeSpecificity(query, queryTerms, docTerms),
	}
}

// computeRelevance computes BM25 relevance score
func (fe *FeatureExtractor) computeRelevance(query string, queryTerms, docTerms, allTerms map[string]int, totalDocs int) float64 {
	// BM25 parameters
	k1 := 1.5
	b := 0.75
	
	// Document length
	docLen := 0
	for _, count := range docTerms {
		docLen += count
	}
	
	// Average document length (approximation)
	avgDocLen := float64(len(allTerms)) / float64(totalDocs)
	
	score := 0.0
	for term := range queryTerms {
		if tf, exists := docTerms[term]; exists {
			df := 0
			for _, doc := range allTerms {
				if doc > 0 {
					df++
				}
			}
			
			// IDF component
			idf := math.Log((float64(totalDocs) - float64(df) + 0.5) / (float64(df) + 0.5))
			
			// TF component with normalization
			tfNorm := float64(tf) * (k1 + 1) / (float64(tf) + k1*(1-b+b*float64(docLen)/avgDocLen))
			
			score += idf * tfNorm
		}
	}
	
	return score
}

// computeRecency computes exponential decay based on modified time
func (fe *FeatureExtractor) computeRecency(mtime int64) float64 {
	if mtime == 0 {
		return 0.5 // Default for unknown time
	}
	
	now := time.Now().Unix()
	daysSince := float64(now-mtime) / (24 * 3600)
	
	// 7-day half-life exponential decay
	halfLife := 7.0
	return math.Exp(-math.Ln2 * daysSince / halfLife)
}

// computeEntanglement computes PMI-based concept density
func (fe *FeatureExtractor) computeEntanglement(docTerms, allTerms map[string]int, totalDocs int) float64 {
	if len(docTerms) < 2 {
		return 0.0
	}
	
	// Extract significant terms (top 20% by frequency)
	type termFreq struct {
		term string
		freq int
	}
	
	var terms []termFreq
	for term, freq := range docTerms {
		terms = append(terms, termFreq{term, freq})
	}
	
	sort.Slice(terms, func(i, j int) bool {
		return terms[i].freq > terms[j].freq
	})
	
	// Take top 20% of terms
	topN := int(math.Max(2, float64(len(terms))*0.2))
	if topN > len(terms) {
		topN = len(terms)
	}
	
	entanglement := 0.0
	pairs := 0
	
	// Compute PMI between significant terms
	for i := 0; i < topN; i++ {
		for j := i + 1; j < topN; j++ {
			term1, term2 := terms[i].term, terms[j].term
			
			// Simple co-occurrence approximation (both terms in same doc)
			coOccur := 1.0 // Both are in this document
			prob1 := float64(allTerms[term1]) / float64(totalDocs)
			prob2 := float64(allTerms[term2]) / float64(totalDocs)
			jointProb := coOccur / float64(totalDocs)
			
			if prob1 > 0 && prob2 > 0 && jointProb > 0 {
				pmi := math.Log(jointProb / (prob1 * prob2))
				entanglement += math.Max(0, pmi) // Only positive PMI
				pairs++
			}
		}
	}
	
	if pairs > 0 {
		return entanglement / float64(pairs)
	}
	return 0.0
}

// computePrior computes historical selection likelihood
func (fe *FeatureExtractor) computePrior(doc types.Document) float64 {
	// Simple heuristics based on path and usage patterns
	score := 0.5 // Base score
	
	// Boost for commonly used file types
	if strings.Contains(doc.Language, "go") ||
	   strings.Contains(doc.Language, "python") ||
	   strings.Contains(doc.Language, "javascript") {
		score += 0.2
	}
	
	// Boost for main/entry files
	if strings.Contains(strings.ToLower(doc.Path), "main") ||
	   strings.Contains(strings.ToLower(doc.Path), "index") ||
	   strings.Contains(strings.ToLower(doc.Path), "app") {
		score += 0.3
	}
	
	// Boost for recent files (based on modified time)
	if doc.ModifiedTime > 0 {
		daysSince := float64(time.Now().Unix()-doc.ModifiedTime) / (24 * 3600)
		if daysSince < 7 {
			score += 0.2 * (7 - daysSince) / 7
		}
	}
	
	return math.Min(1.0, score)
}

// computeUncertainty computes score variance across estimators
func (fe *FeatureExtractor) computeUncertainty(query string, docTerms, allTerms map[string]int, totalDocs int) float64 {
	// Compute different scoring methods
	queryTerms := extractTerms(query)
	
	// BM25 score
	bm25 := fe.computeRelevance(query, queryTerms, docTerms, allTerms, totalDocs)
	
	// TF-IDF score (simplified)
	tfidf := 0.0
	docLen := 0
	for _, count := range docTerms {
		docLen += count
	}
	
	for term := range queryTerms {
		if tf, exists := docTerms[term]; exists {
			df := float64(allTerms[term])
			idf := math.Log(float64(totalDocs) / (df + 1))
			tfidf += (float64(tf) / float64(docLen)) * idf
		}
	}
	
	// Simple overlap score
	overlap := 0.0
	for term := range queryTerms {
		if _, exists := docTerms[term]; exists {
			overlap += 1.0
		}
	}
	overlap /= float64(len(queryTerms))
	
	// Compute variance
	scores := []float64{bm25, tfidf, overlap}
	mean := (bm25 + tfidf + overlap) / 3.0
	
	variance := 0.0
	for _, score := range scores {
		variance += (score - mean) * (score - mean)
	}
	variance /= float64(len(scores))
	
	// Return normalized uncertainty (higher = more uncertain)
	return math.Min(1.0, math.Sqrt(variance))
}

// computeAuthority computes document importance
func (fe *FeatureExtractor) computeAuthority(doc types.Document) float64 {
	score := 0.0
	
	// File size (longer docs often more important)
	contentLen := float64(len(doc.Content))
	if contentLen > 0 {
		// Normalize by log to prevent very long docs from dominating
		score += math.Min(0.5, math.Log(contentLen)/math.Log(10000))
	}
	
	// Token count (if available)
	if doc.TokenCount > 0 {
		score += math.Min(0.3, float64(doc.TokenCount)/5000)
	}
	
	// Path-based importance
	if strings.Contains(strings.ToLower(doc.Path), "readme") ||
	   strings.Contains(strings.ToLower(doc.Path), "doc") {
		score += 0.3
	}
	
	// Language-specific boosts
	if doc.Language != "" {
		score += 0.2
	}
	
	return math.Min(1.0, score)
}

// computeSpecificity computes query-document topic alignment
func (fe *FeatureExtractor) computeSpecificity(query string, queryTerms, docTerms map[string]int) float64 {
	if len(queryTerms) == 0 || len(docTerms) == 0 {
		return 0.0
	}
	
	// Jaccard similarity of terms
	intersection := 0
	union := len(queryTerms)
	
	for term := range queryTerms {
		if _, exists := docTerms[term]; exists {
			intersection++
		}
	}
	
	// Add doc terms not in query
	for term := range docTerms {
		if _, exists := queryTerms[term]; !exists {
			union++
		}
	}
	
	if union == 0 {
		return 0.0
	}
	
	jaccard := float64(intersection) / float64(union)
	
	// Boost for exact phrase matches
	queryLower := strings.ToLower(query)
	contentLower := strings.ToLower(extractContent(docTerms))
	
	if strings.Contains(contentLower, queryLower) {
		jaccard += 0.3
	}
	
	return math.Min(1.0, jaccard)
}

// normalizeFeatures applies z-score normalization using workspace stats
func (fe *FeatureExtractor) normalizeFeatures(features types.FeatureVector) types.FeatureVector {
	if fe.normStats == nil || fe.normStats.Count == 0 {
		// No normalization stats available, return as-is (clamped to [0,1])
		return types.FeatureVector{
			Relevance:    math.Max(0, math.Min(1, features.Relevance)),
			Recency:      math.Max(0, math.Min(1, features.Recency)),
			Entanglement: math.Max(0, math.Min(1, features.Entanglement)),
			Prior:        math.Max(0, math.Min(1, features.Prior)),
			Uncertainty:  math.Max(0, math.Min(1, features.Uncertainty)),
			Authority:    math.Max(0, math.Min(1, features.Authority)),
			Specificity:  math.Max(0, math.Min(1, features.Specificity)),
		}
	}
	
	// Apply z-score normalization and clamp to [0,1]
	normalize := func(value, mean, stdDev float64) float64 {
		if stdDev == 0 {
			return 0.5 // Default for constant values
		}
		zscore := (value - mean) / stdDev
		// Convert z-score to [0,1] using sigmoid
		return 1.0 / (1.0 + math.Exp(-zscore))
	}
	
	return types.FeatureVector{
		Relevance:    normalize(features.Relevance, fe.normStats.Mean["relevance"], fe.normStats.StdDev["relevance"]),
		Recency:      normalize(features.Recency, fe.normStats.Mean["recency"], fe.normStats.StdDev["recency"]),
		Entanglement: normalize(features.Entanglement, fe.normStats.Mean["entanglement"], fe.normStats.StdDev["entanglement"]),
		Prior:        normalize(features.Prior, fe.normStats.Mean["prior"], fe.normStats.StdDev["prior"]),
		Uncertainty:  normalize(features.Uncertainty, fe.normStats.Mean["uncertainty"], fe.normStats.StdDev["uncertainty"]),
		Authority:    normalize(features.Authority, fe.normStats.Mean["authority"], fe.normStats.StdDev["authority"]),
		Specificity:  normalize(features.Specificity, fe.normStats.Mean["specificity"], fe.normStats.StdDev["specificity"]),
	}
}

// computeUtilityScore computes per-document utility for optimization optimization
func (fe *FeatureExtractor) computeUtilityScore(features types.FeatureVector) float64 {
	// Default weights (will be overridden by workspace-specific weights)
	weights := map[string]float64{
		"relevance":    0.30,
		"recency":      0.20,
		"entanglement": 0.15,
		"prior":        0.15,
		"authority":    0.10,
		"specificity":  0.05,
		"uncertainty":  0.05,
	}
	
	return weights["relevance"]*features.Relevance +
		   weights["recency"]*features.Recency +
		   weights["entanglement"]*features.Entanglement +
		   weights["prior"]*features.Prior +
		   weights["authority"]*features.Authority +
		   weights["specificity"]*features.Specificity -
		   weights["uncertainty"]*features.Uncertainty // Subtract uncertainty
}

// extractTerms extracts and normalizes terms from text
func extractTerms(text string) map[string]int {
	terms := make(map[string]int)
	
	// Simple tokenization (split on non-alphanumeric)
	words := strings.FieldsFunc(strings.ToLower(text), func(r rune) bool {
		return !((r >= 'a' && r <= 'z') || (r >= '0' && r <= '9'))
	})
	
	for _, word := range words {
		if len(word) > 2 { // Filter out very short words
			terms[word]++
		}
	}
	
	return terms
}

// extractContent reconstructs content from term map (for phrase matching)
func extractContent(terms map[string]int) string {
	var words []string
	for term, count := range terms {
		for i := 0; i < count; i++ {
			words = append(words, term)
		}
	}
	return strings.Join(words, " ")
}
