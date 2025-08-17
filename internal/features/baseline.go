package features

import (
	"math"
	"sort"
	"strings"

	"contextlite/pkg/types"
)

// BM25Scorer implements a simple BM25 + MMR baseline for comparison
type BM25Scorer struct {
	k1       float64 // Term frequency saturation parameter
	b        float64 // Length normalization parameter
	lambda   float64 // MMR diversity parameter (0 = pure relevance, 1 = pure diversity)
}

// NewBM25Scorer creates a new BM25 scorer with standard parameters
func NewBM25Scorer() *BM25Scorer {
	return &BM25Scorer{
		k1:     1.2,  // Standard BM25 k1
		b:      0.75, // Standard BM25 b
		lambda: 0.3,  // 30% diversity, 70% relevance for MMR
	}
}

// ScoreDocuments scores documents using BM25 + MMR baseline
func (bm25 *BM25Scorer) ScoreDocuments(docs []types.Document, query string, maxResults int) []types.ScoredDocument {
	if len(docs) == 0 {
		return nil
	}

	// Tokenize query and documents
	queryTerms := tokenize(query)
	docTerms := make([]map[string]int, len(docs))
	docLengths := make([]int, len(docs))
	avgDocLength := 0.0
	
	// Calculate term frequencies and document frequencies
	termDocFreq := make(map[string]int)
	
	for i, doc := range docs {
		terms := tokenize(doc.Content)
		docTerms[i] = make(map[string]int)
		for _, term := range terms {
			docTerms[i][term]++
		}
		docLengths[i] = len(terms)
		avgDocLength += float64(len(terms))
		
		// Track which documents contain each term
		seenTerms := make(map[string]bool)
		for term := range docTerms[i] {
			if !seenTerms[term] {
				termDocFreq[term]++
				seenTerms[term] = true
			}
		}
	}
	avgDocLength /= float64(len(docs))

	// Calculate BM25 scores
	scored := make([]types.ScoredDocument, len(docs))
	for i, doc := range docs {
		score := bm25.calculateBM25(queryTerms, docTerms[i], docLengths[i], avgDocLength, termDocFreq, len(docs))
		
		scored[i] = types.ScoredDocument{
			Document:     doc,
			UtilityScore: score,
			Features: types.FeatureVector{
				Relevance:   score, // For baseline, relevance = BM25 score
				Recency:     0.0,   // Not used in baseline
				Entanglement: 0.0,  // Not used in baseline
				Prior:       0.0,   // Not used in baseline
				Uncertainty: 0.0,   // Not used in baseline
				Authority:   0.0,   // Not used in baseline
				Specificity: 0.0,   // Not used in baseline
			},
			PairwiseScores: nil, // Will be calculated in MMR
		}
	}

	// Sort by BM25 score (descending)
	sort.Slice(scored, func(i, j int) bool {
		return scored[i].UtilityScore > scored[j].UtilityScore
	})

	// Apply MMR (Maximal Marginal Relevance) for diversity
	if maxResults > 0 && maxResults < len(scored) {
		return bm25.applyMMR(scored, maxResults)
	}

	return scored
}

// calculateBM25 computes BM25 score for a document given a query
func (bm25 *BM25Scorer) calculateBM25(queryTerms []string, docTerms map[string]int, docLength int, avgDocLength float64, termDocFreq map[string]int, totalDocs int) float64 {
	score := 0.0
	
	for _, term := range queryTerms {
		tf := float64(docTerms[term]) // Term frequency in document
		df := float64(termDocFreq[term]) // Document frequency
		
		if df == 0 {
			continue // Term not in any document
		}
		
		// IDF component: log((N - df + 0.5) / (df + 0.5))
		idf := math.Log((float64(totalDocs) - df + 0.5) / (df + 0.5))
		
		// TF component with length normalization
		normalizedTF := (tf * (bm25.k1 + 1)) / (tf + bm25.k1*(1-bm25.b+bm25.b*(float64(docLength)/avgDocLength)))
		
		score += idf * normalizedTF
	}
	
	return score
}

// applyMMR applies Maximal Marginal Relevance for diversity
func (bm25 *BM25Scorer) applyMMR(scored []types.ScoredDocument, maxResults int) []types.ScoredDocument {
	if len(scored) <= maxResults {
		return scored
	}

	selected := make([]types.ScoredDocument, 0, maxResults)
	remaining := make([]types.ScoredDocument, len(scored))
	copy(remaining, scored)

	// Select first document (highest BM25 score)
	selected = append(selected, remaining[0])
	remaining = remaining[1:]

	// Iteratively select documents balancing relevance and diversity
	for len(selected) < maxResults && len(remaining) > 0 {
		bestIdx := -1
		bestScore := -1.0

		for i, candidate := range remaining {
			// Relevance component
			relevance := candidate.UtilityScore
			if len(scored) > 0 {
				relevance /= scored[0].UtilityScore // Normalize by top score
			}

			// Diversity component (minimum similarity to selected docs)
			minSimilarity := 1.0
			for _, selectedDoc := range selected {
				similarity := bm25.calculateSimilarity(candidate.Document, selectedDoc.Document)
				if similarity < minSimilarity {
					minSimilarity = similarity
				}
			}
			diversity := 1.0 - minSimilarity

			// MMR score: λ * relevance + (1-λ) * diversity
			mmrScore := bm25.lambda*relevance + (1-bm25.lambda)*diversity

			if mmrScore > bestScore {
				bestScore = mmrScore
				bestIdx = i
			}
		}

		if bestIdx >= 0 {
			// Add selected document and remove from remaining
			selected = append(selected, remaining[bestIdx])
			remaining = append(remaining[:bestIdx], remaining[bestIdx+1:]...)
		} else {
			break
		}
	}

	// Update diversity scores in features
	for i := range selected {
		diversityScore := bm25.calculateDiversityScore(selected[i].Document, selected)
		selected[i].Features.Specificity = diversityScore // Use Specificity field for diversity in baseline
	}

	return selected
}

// calculateSimilarity computes cosine similarity between two documents
func (bm25 *BM25Scorer) calculateSimilarity(doc1, doc2 types.Document) float64 {
	terms1 := tokenize(doc1.Content)
	terms2 := tokenize(doc2.Content)

	// Create term frequency maps
	tf1 := make(map[string]int)
	tf2 := make(map[string]int)
	
	for _, term := range terms1 {
		tf1[term]++
	}
	for _, term := range terms2 {
		tf2[term]++
	}

	// Calculate cosine similarity
	dotProduct := 0.0
	norm1 := 0.0
	norm2 := 0.0

	allTerms := make(map[string]bool)
	for term := range tf1 {
		allTerms[term] = true
	}
	for term := range tf2 {
		allTerms[term] = true
	}

	for term := range allTerms {
		v1 := float64(tf1[term])
		v2 := float64(tf2[term])
		dotProduct += v1 * v2
		norm1 += v1 * v1
		norm2 += v2 * v2
	}

	if norm1 == 0 || norm2 == 0 {
		return 0.0
	}

	return dotProduct / (math.Sqrt(norm1) * math.Sqrt(norm2))
}

// calculateDiversityScore calculates diversity score for a document within a set
func (bm25 *BM25Scorer) calculateDiversityScore(doc types.Document, selected []types.ScoredDocument) float64 {
	if len(selected) <= 1 {
		return 1.0
	}

	totalSimilarity := 0.0
	count := 0

	for _, other := range selected {
		if other.Document.ID != doc.ID {
			similarity := bm25.calculateSimilarity(doc, other.Document)
			totalSimilarity += similarity
			count++
		}
	}

	if count == 0 {
		return 1.0
	}

	avgSimilarity := totalSimilarity / float64(count)
	return 1.0 - avgSimilarity // Higher diversity = lower average similarity
}

// tokenize splits text into terms (simple whitespace tokenization)
func tokenize(text string) []string {
	// Simple tokenization - split on whitespace and convert to lowercase
	text = strings.ToLower(text)
	fields := strings.Fields(text)
	
	// Remove punctuation and short terms
	var terms []string
	for _, field := range fields {
		cleaned := strings.Trim(field, ".,!?;:\"'()[]{}=+-*/\\|<>@#$%^&")
		if len(cleaned) >= 2 { // Only keep terms with 2+ characters
			terms = append(terms, cleaned)
		}
	}
	
	return terms
}
