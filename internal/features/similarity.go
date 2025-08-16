package features

import (
	"fmt"
	"math"
	"sort"
	"strings"

	"contextlite/pkg/types"
)

// SimilarityComputer computes pairwise similarities between documents
type SimilarityComputer struct {
	maxPairsPerDoc int
}

// NewSimilarityComputer creates a new similarity computer
func NewSimilarityComputer(maxPairsPerDoc int) *SimilarityComputer {
	return &SimilarityComputer{
		maxPairsPerDoc: maxPairsPerDoc,
	}
}

// DocumentPair represents a pair of documents with similarity scores
type DocumentPair struct {
	DocI          int     `json:"doc_i"`
	DocJ          int     `json:"doc_j"`
	Similarity    float64 `json:"similarity"`
	Coherence     float64 `json:"coherence"`
	Redundancy    float64 `json:"redundancy"`
}

// ComputePairwiseScores computes similarity scores for document pairs
func (sc *SimilarityComputer) ComputePairwiseScores(docs []types.ScoredDocument) []DocumentPair {
	var pairs []DocumentPair
	
	// Compute all pairwise similarities
	allPairs := make([]DocumentPair, 0, len(docs)*(len(docs)-1)/2)
	
	for i := 0; i < len(docs); i++ {
		for j := i + 1; j < len(docs); j++ {
			similarity := sc.computeDocumentSimilarity(docs[i].Document, docs[j].Document)
			coherence := sc.computeCoherence(docs[i].Document, docs[j].Document)
			redundancy := similarity // For now, redundancy is just similarity
			
			allPairs = append(allPairs, DocumentPair{
				DocI:       i,
				DocJ:       j,
				Similarity: similarity,
				Coherence:  coherence,
				Redundancy: redundancy,
			})
		}
	}
	
	// For each document, keep only top-M most similar pairs
	docPairs := make(map[int][]DocumentPair)
	
	// Group pairs by document
	for _, pair := range allPairs {
		docPairs[pair.DocI] = append(docPairs[pair.DocI], pair)
		docPairs[pair.DocJ] = append(docPairs[pair.DocJ], pair)
	}
	
	// Sort and limit pairs per document
	usedPairs := make(map[string]bool)
	
	for _, docPairList := range docPairs {
		// Sort by similarity (descending)
		sort.Slice(docPairList, func(i, j int) bool {
			return docPairList[i].Similarity > docPairList[j].Similarity
		})
		
		// Take top M pairs for this document
		count := 0
		for _, pair := range docPairList {
			if count >= sc.maxPairsPerDoc {
				break
			}
			
			// Create unique key for this pair
			var key string
			if pair.DocI < pair.DocJ {
				key = fmt.Sprintf("%d-%d", pair.DocI, pair.DocJ)
			} else {
				key = fmt.Sprintf("%d-%d", pair.DocJ, pair.DocI)
			}
			
			if !usedPairs[key] {
				pairs = append(pairs, pair)
				usedPairs[key] = true
				count++
			}
		}
	}
	
	return pairs
}

// computeDocumentSimilarity computes TF-IDF cosine similarity between documents
func (sc *SimilarityComputer) computeDocumentSimilarity(doc1, doc2 types.Document) float64 {
	// Extract terms from both documents
	terms1 := extractTerms(doc1.Content)
	terms2 := extractTerms(doc2.Content)
	
	// Build union of all terms
	allTerms := make(map[string]bool)
	for term := range terms1 {
		allTerms[term] = true
	}
	for term := range terms2 {
		allTerms[term] = true
	}
	
	if len(allTerms) == 0 {
		return 0.0
	}
	
	// Compute TF-IDF vectors (simplified - using just TF for now)
	var vec1, vec2 []float64
	
	// Get document lengths for normalization
	len1 := 0
	for _, count := range terms1 {
		len1 += count
	}
	len2 := 0
	for _, count := range terms2 {
		len2 += count
	}
	
	if len1 == 0 || len2 == 0 {
		return 0.0
	}
	
	// Build normalized term frequency vectors
	for term := range allTerms {
		tf1 := float64(terms1[term]) / float64(len1)
		tf2 := float64(terms2[term]) / float64(len2)
		vec1 = append(vec1, tf1)
		vec2 = append(vec2, tf2)
	}
	
	// Compute cosine similarity
	return cosineSimilarity(vec1, vec2)
}

// computeCoherence computes concept overlap between documents
func (sc *SimilarityComputer) computeCoherence(doc1, doc2 types.Document) float64 {
	// Extract significant terms (top 20% by frequency)
	terms1 := extractSignificantTerms(doc1.Content, 0.2)
	terms2 := extractSignificantTerms(doc2.Content, 0.2)
	
	if len(terms1) == 0 || len(terms2) == 0 {
		return 0.0
	}
	
	// Compute Jaccard similarity of significant terms
	intersection := 0
	union := make(map[string]bool)
	
	for term := range terms1 {
		union[term] = true
	}
	for term := range terms2 {
		union[term] = true
		if terms1[term] > 0 {
			intersection++
		}
	}
	
	if len(union) == 0 {
		return 0.0
	}
	
	jaccard := float64(intersection) / float64(len(union))
	
	// Boost for similar languages/file types
	if doc1.Language == doc2.Language && doc1.Language != "" {
		jaccard += 0.1
	}
	
	// Boost for similar paths (same directory, etc.)
	if sc.pathSimilarity(doc1.Path, doc2.Path) > 0.5 {
		jaccard += 0.1
	}
	
	return math.Min(1.0, jaccard)
}

// extractSignificantTerms extracts the top percentage of terms by frequency
func extractSignificantTerms(content string, topPercent float64) map[string]int {
	allTerms := extractTerms(content)
	
	if len(allTerms) == 0 {
		return allTerms
	}
	
	// Sort terms by frequency
	type termFreq struct {
		term string
		freq int
	}
	
	var terms []termFreq
	for term, freq := range allTerms {
		terms = append(terms, termFreq{term, freq})
	}
	
	sort.Slice(terms, func(i, j int) bool {
		return terms[i].freq > terms[j].freq
	})
	
	// Take top percentage
	topN := int(math.Max(1, float64(len(terms))*topPercent))
	if topN > len(terms) {
		topN = len(terms)
	}
	
	significant := make(map[string]int)
	for i := 0; i < topN; i++ {
		significant[terms[i].term] = terms[i].freq
	}
	
	return significant
}

// pathSimilarity computes similarity between file paths
func (sc *SimilarityComputer) pathSimilarity(path1, path2 string) float64 {
	if path1 == "" || path2 == "" {
		return 0.0
	}
	
	// Split paths into components
	parts1 := strings.Split(strings.ToLower(path1), "/")
	parts2 := strings.Split(strings.ToLower(path2), "/")
	
	// Remove empty parts
	parts1 = filterEmpty(parts1)
	parts2 = filterEmpty(parts2)
	
	if len(parts1) == 0 || len(parts2) == 0 {
		return 0.0
	}
	
	// Compute longest common prefix
	commonPrefix := 0
	minLen := len(parts1)
	if len(parts2) < minLen {
		minLen = len(parts2)
	}
	
	for i := 0; i < minLen; i++ {
		if parts1[i] == parts2[i] {
			commonPrefix++
		} else {
			break
		}
	}
	
	// Similarity based on common prefix ratio
	maxLen := len(parts1)
	if len(parts2) > maxLen {
		maxLen = len(parts2)
	}
	
	return float64(commonPrefix) / float64(maxLen)
}

// cosineSimilarity computes cosine similarity between two vectors
func cosineSimilarity(vec1, vec2 []float64) float64 {
	if len(vec1) != len(vec2) {
		return 0.0
	}
	
	var dotProduct, norm1, norm2 float64
	
	for i := 0; i < len(vec1); i++ {
		dotProduct += vec1[i] * vec2[i]
		norm1 += vec1[i] * vec1[i]
		norm2 += vec2[i] * vec2[i]
	}
	
	if norm1 == 0 || norm2 == 0 {
		return 0.0
	}
	
	return dotProduct / (math.Sqrt(norm1) * math.Sqrt(norm2))
}

// filterEmpty removes empty strings from slice
func filterEmpty(strs []string) []string {
	var result []string
	for _, s := range strs {
		if s != "" {
			result = append(result, s)
		}
	}
	return result
}
