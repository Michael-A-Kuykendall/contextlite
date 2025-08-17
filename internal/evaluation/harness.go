// Package evaluation provides comprehensive evaluation metrics for ContextLite optimization system
// against SOTA RAG approaches including classical BM25, embedding-based, and LLM-based systems.
package evaluation

import (
	"fmt"
	"math"
	"sort"

	"contextlite/pkg/types"
)

// EvaluationResult contains comprehensive metrics for SOTA comparison
type EvaluationResult struct {
	// Core Information Retrieval Metrics
	RecallAt1  float64 `json:"recall_at_1"`
	RecallAt3  float64 `json:"recall_at_3"`
	RecallAt5  float64 `json:"recall_at_5"`
	RecallAt10 float64 `json:"recall_at_10"`
	
	// Normalized Discounted Cumulative Gain
	NDCG1  float64 `json:"ndcg_at_1"`
	NDCG3  float64 `json:"ndcg_at_3"`
	NDCG5  float64 `json:"ndcg_at_5"`
	NDCG10 float64 `json:"ndcg_at_10"`
	
	// Mean Average Precision
	MAP float64 `json:"mean_average_precision"`
	
	// Mean Reciprocal Rank
	MRR float64 `json:"mean_reciprocal_rank"`
	
	// Additional Context Quality Metrics
	Precision     float64 `json:"precision"`
	F1Score       float64 `json:"f1_score"`
	ContextLength int     `json:"context_length_tokens"`
	
	// Performance Metrics
	LatencyMs    int64 `json:"latency_ms"`
	MemoryUsageMB float64 `json:"memory_usage_mb"`
	
	// System Information
	SystemType    string `json:"system_type"`    // "contextlite_optimization", "bm25", "embedding", "llm"
	QueryType     string `json:"query_type"`     // "factual", "analytical", "creative"
	DocumentCount int    `json:"document_count"`
}

// GroundTruth represents human-annotated relevance judgments
type GroundTruth struct {
	Query       string             `json:"query"`
	QueryType   string             `json:"query_type"`
	Relevance   map[string]float64 `json:"relevance"`   // doc_id -> relevance score [0-3]
	Description string             `json:"description"`
}

// EvaluationConfig controls evaluation parameters
type EvaluationConfig struct {
	MaxK            int     `json:"max_k"`              // Maximum k for Recall@k, nDCG@k
	RelevanceThresh float64 `json:"relevance_thresh"`   // Minimum score to consider relevant
	UseIdealDCG     bool    `json:"use_ideal_dcg"`      // Whether to normalize DCG
}

// DefaultEvaluationConfig returns standard evaluation parameters
func DefaultEvaluationConfig() *EvaluationConfig {
	return &EvaluationConfig{
		MaxK:            10,
		RelevanceThresh: 1.0, // Documents with relevance >= 1.0 considered relevant
		UseIdealDCG:     true,
	}
}

// EvaluationHarness provides comprehensive evaluation capabilities
type EvaluationHarness struct {
	config     *EvaluationConfig
	groundTruth []GroundTruth
}

// NewEvaluationHarness creates a new evaluation harness
func NewEvaluationHarness(config *EvaluationConfig) *EvaluationHarness {
	if config == nil {
		config = DefaultEvaluationConfig()
	}
	
	return &EvaluationHarness{
		config:      config,
		groundTruth: make([]GroundTruth, 0),
	}
}

// LoadGroundTruth adds ground truth data for evaluation
func (h *EvaluationHarness) LoadGroundTruth(gt []GroundTruth) {
	h.groundTruth = append(h.groundTruth, gt...)
}

// EvaluateQuery computes comprehensive metrics for a single query result
func (h *EvaluationHarness) EvaluateQuery(
	query string,
	results []types.DocumentReference,
	systemType string,
	latencyMs int64,
	memoryMB float64,
) (*EvaluationResult, error) {
	
	// Find ground truth for this query
	var gt *GroundTruth
	for i := range h.groundTruth {
		if h.groundTruth[i].Query == query {
			gt = &h.groundTruth[i]
			break
		}
	}
	
	if gt == nil {
		return nil, fmt.Errorf("no ground truth found for query: %s", query)
	}
	
	// Calculate core metrics
	result := &EvaluationResult{
		SystemType:    systemType,
		QueryType:     gt.QueryType,
		DocumentCount: len(results),
		LatencyMs:     latencyMs,
		MemoryUsageMB: memoryMB,
	}
	
	// Calculate token count for context length (estimate from content length)
	totalTokens := 0
	for _, doc := range results {
		// Estimate tokens as ~4 characters per token
		totalTokens += len(doc.Content) / 4
	}
	result.ContextLength = totalTokens
	
	// Compute Recall@k for different k values
	result.RecallAt1 = h.calculateRecallAtK(results, gt, 1)
	result.RecallAt3 = h.calculateRecallAtK(results, gt, 3)
	result.RecallAt5 = h.calculateRecallAtK(results, gt, 5)
	result.RecallAt10 = h.calculateRecallAtK(results, gt, 10)
	
	// Compute nDCG@k for different k values
	result.NDCG1 = h.calculateNDCGAtK(results, gt, 1)
	result.NDCG3 = h.calculateNDCGAtK(results, gt, 3)
	result.NDCG5 = h.calculateNDCGAtK(results, gt, 5)
	result.NDCG10 = h.calculateNDCGAtK(results, gt, 10)
	
	// Compute MAP and MRR
	result.MAP = h.calculateMAP(results, gt)
	result.MRR = h.calculateMRR(results, gt)
	
	// Compute Precision and F1
	precision, recall := h.calculatePrecisionRecall(results, gt)
	result.Precision = precision
	if precision+recall > 0 {
		result.F1Score = 2 * (precision * recall) / (precision + recall)
	}
	
	return result, nil
}

// calculateRecallAtK computes Recall@k: percentage of relevant docs in top-k
func (h *EvaluationHarness) calculateRecallAtK(
	results []types.DocumentReference,
	gt *GroundTruth,
	k int,
) float64 {
	if k > len(results) {
		k = len(results)
	}
	
	// Count total relevant documents
	totalRelevant := 0
	for _, relevance := range gt.Relevance {
		if relevance >= h.config.RelevanceThresh {
			totalRelevant++
		}
	}
	
	if totalRelevant == 0 {
		return 0.0
	}
	
	// Count relevant documents in top-k
	relevantInTopK := 0
	for i := 0; i < k; i++ {
		docID := results[i].ID
		if relevance, exists := gt.Relevance[docID]; exists {
			if relevance >= h.config.RelevanceThresh {
				relevantInTopK++
			}
		}
	}
	
	return float64(relevantInTopK) / float64(totalRelevant)
}

// calculateNDCGAtK computes Normalized Discounted Cumulative Gain@k
func (h *EvaluationHarness) calculateNDCGAtK(
	results []types.DocumentReference,
	gt *GroundTruth,
	k int,
) float64 {
	if k > len(results) {
		k = len(results)
	}
	
	// Calculate DCG@k
	dcg := 0.0
	for i := 0; i < k; i++ {
		docID := results[i].ID
		relevance := 0.0
		if rel, exists := gt.Relevance[docID]; exists {
			relevance = rel
		}
		
		// DCG formula: rel / log2(position + 1)
		if i == 0 {
			dcg += relevance
		} else {
			dcg += relevance / math.Log2(float64(i+2))
		}
	}
	
	if !h.config.UseIdealDCG {
		return dcg
	}
	
	// Calculate Ideal DCG@k (IDCG)
	idealRelevances := make([]float64, 0, len(gt.Relevance))
	for _, relevance := range gt.Relevance {
		idealRelevances = append(idealRelevances, relevance)
	}
	
	// Sort relevances in descending order
	sort.Float64s(idealRelevances)
	for i := 0; i < len(idealRelevances)/2; i++ {
		j := len(idealRelevances) - 1 - i
		idealRelevances[i], idealRelevances[j] = idealRelevances[j], idealRelevances[i]
	}
	
	idcg := 0.0
	for i := 0; i < k && i < len(idealRelevances); i++ {
		relevance := idealRelevances[i]
		if i == 0 {
			idcg += relevance
		} else {
			idcg += relevance / math.Log2(float64(i+2))
		}
	}
	
	if idcg == 0 {
		return 0.0
	}
	
	return dcg / idcg
}

// calculateMAP computes Mean Average Precision
func (h *EvaluationHarness) calculateMAP(
	results []types.DocumentReference,
	gt *GroundTruth,
) float64 {
	relevantFound := 0
	sumPrecision := 0.0
	
	for i, doc := range results {
		if relevance, exists := gt.Relevance[doc.ID]; exists {
			if relevance >= h.config.RelevanceThresh {
				relevantFound++
				precision := float64(relevantFound) / float64(i+1)
				sumPrecision += precision
			}
		}
	}
	
	// Count total relevant documents
	totalRelevant := 0
	for _, relevance := range gt.Relevance {
		if relevance >= h.config.RelevanceThresh {
			totalRelevant++
		}
	}
	
	if totalRelevant == 0 {
		return 0.0
	}
	
	return sumPrecision / float64(totalRelevant)
}

// calculateMRR computes Mean Reciprocal Rank
func (h *EvaluationHarness) calculateMRR(
	results []types.DocumentReference,
	gt *GroundTruth,
) float64 {
	for i, doc := range results {
		if relevance, exists := gt.Relevance[doc.ID]; exists {
			if relevance >= h.config.RelevanceThresh {
				return 1.0 / float64(i+1)
			}
		}
	}
	return 0.0
}

// calculatePrecisionRecall computes overall precision and recall
func (h *EvaluationHarness) calculatePrecisionRecall(
	results []types.DocumentReference,
	gt *GroundTruth,
) (precision, recall float64) {
	relevantRetrieved := 0
	totalRetrieved := len(results)
	
	// Count relevant documents in results
	for _, doc := range results {
		if relevance, exists := gt.Relevance[doc.ID]; exists {
			if relevance >= h.config.RelevanceThresh {
				relevantRetrieved++
			}
		}
	}
	
	// Count total relevant documents
	totalRelevant := 0
	for _, relevance := range gt.Relevance {
		if relevance >= h.config.RelevanceThresh {
			totalRelevant++
		}
	}
	
	precision = 0.0
	if totalRetrieved > 0 {
		precision = float64(relevantRetrieved) / float64(totalRetrieved)
	}
	
	recall = 0.0
	if totalRelevant > 0 {
		recall = float64(relevantRetrieved) / float64(totalRelevant)
	}
	
	return precision, recall
}

// BatchEvaluate runs evaluation across multiple queries and returns aggregate metrics
func (h *EvaluationHarness) BatchEvaluate(
	queryResults map[string]QueryResult,
	systemType string,
) (*AggregateResults, error) {
	
	if len(queryResults) == 0 {
		return nil, fmt.Errorf("no query results provided")
	}
	
	results := make([]*EvaluationResult, 0, len(queryResults))
	
	for query, qr := range queryResults {
		result, err := h.EvaluateQuery(
			query,
			qr.Documents,
			systemType,
			qr.LatencyMs,
			qr.MemoryMB,
		)
		if err != nil {
			continue // Skip queries without ground truth
		}
		results = append(results, result)
	}
	
	if len(results) == 0 {
		return nil, fmt.Errorf("no valid evaluation results")
	}
	
	return h.aggregateResults(results, systemType), nil
}

// QueryResult represents the output from a retrieval system
type QueryResult struct {
	Documents []types.DocumentReference `json:"documents"`
	LatencyMs int64                     `json:"latency_ms"`
	MemoryMB  float64                   `json:"memory_mb"`
}

// AggregateResults contains mean metrics across all queries
type AggregateResults struct {
	SystemType string `json:"system_type"`
	QueryCount int    `json:"query_count"`
	
	// Mean metrics
	MeanRecallAt1  float64 `json:"mean_recall_at_1"`
	MeanRecallAt3  float64 `json:"mean_recall_at_3"`
	MeanRecallAt5  float64 `json:"mean_recall_at_5"`
	MeanRecallAt10 float64 `json:"mean_recall_at_10"`
	
	MeanNDCG1  float64 `json:"mean_ndcg_at_1"`
	MeanNDCG3  float64 `json:"mean_ndcg_at_3"`
	MeanNDCG5  float64 `json:"mean_ndcg_at_5"`
	MeanNDCG10 float64 `json:"mean_ndcg_at_10"`
	
	MeanMAP       float64 `json:"mean_map"`
	MeanMRR       float64 `json:"mean_mrr"`
	MeanPrecision float64 `json:"mean_precision"`
	MeanF1Score   float64 `json:"mean_f1_score"`
	
	// Performance metrics
	MeanLatencyMs    float64 `json:"mean_latency_ms"`
	MeanMemoryMB     float64 `json:"mean_memory_mb"`
	MeanContextLen   float64 `json:"mean_context_length"`
	
	// Standard deviations for significance testing
	StdRecallAt5  float64 `json:"std_recall_at_5"`
	StdNDCG5      float64 `json:"std_ndcg_at_5"`
	StdLatencyMs  float64 `json:"std_latency_ms"`
}

// aggregateResults computes mean and standard deviation across evaluation results
func (h *EvaluationHarness) aggregateResults(
	results []*EvaluationResult,
	systemType string,
) *AggregateResults {
	
	n := float64(len(results))
	agg := &AggregateResults{
		SystemType: systemType,
		QueryCount: len(results),
	}
	
	// Calculate means
	for _, r := range results {
		agg.MeanRecallAt1 += r.RecallAt1
		agg.MeanRecallAt3 += r.RecallAt3
		agg.MeanRecallAt5 += r.RecallAt5
		agg.MeanRecallAt10 += r.RecallAt10
		
		agg.MeanNDCG1 += r.NDCG1
		agg.MeanNDCG3 += r.NDCG3
		agg.MeanNDCG5 += r.NDCG5
		agg.MeanNDCG10 += r.NDCG10
		
		agg.MeanMAP += r.MAP
		agg.MeanMRR += r.MRR
		agg.MeanPrecision += r.Precision
		agg.MeanF1Score += r.F1Score
		
		agg.MeanLatencyMs += float64(r.LatencyMs)
		agg.MeanMemoryMB += r.MemoryUsageMB
		agg.MeanContextLen += float64(r.ContextLength)
	}
	
	// Divide by count for means
	agg.MeanRecallAt1 /= n
	agg.MeanRecallAt3 /= n
	agg.MeanRecallAt5 /= n
	agg.MeanRecallAt10 /= n
	
	agg.MeanNDCG1 /= n
	agg.MeanNDCG3 /= n
	agg.MeanNDCG5 /= n
	agg.MeanNDCG10 /= n
	
	agg.MeanMAP /= n
	agg.MeanMRR /= n
	agg.MeanPrecision /= n
	agg.MeanF1Score /= n
	
	agg.MeanLatencyMs /= n
	agg.MeanMemoryMB /= n
	agg.MeanContextLen /= n
	
	// Calculate standard deviations for key metrics
	var sumSqRecall5, sumSqNDCG5, sumSqLatency float64
	
	for _, r := range results {
		sumSqRecall5 += math.Pow(r.RecallAt5-agg.MeanRecallAt5, 2)
		sumSqNDCG5 += math.Pow(r.NDCG5-agg.MeanNDCG5, 2)
		sumSqLatency += math.Pow(float64(r.LatencyMs)-agg.MeanLatencyMs, 2)
	}
	
	agg.StdRecallAt5 = math.Sqrt(sumSqRecall5 / n)
	agg.StdNDCG5 = math.Sqrt(sumSqNDCG5 / n)
	agg.StdLatencyMs = math.Sqrt(sumSqLatency / n)
	
	return agg
}
