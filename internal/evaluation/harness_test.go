package evaluation

import (
	"testing"
	"contextlite/pkg/types"
)

// Test data for evaluation harness
var testGroundTruth = []GroundTruth{
	{
		Query:     "machine learning algorithms",
		QueryType: "factual",
		Relevance: map[string]float64{
			"doc1": 3.0, // Highly relevant
			"doc2": 2.0, // Moderately relevant
			"doc3": 1.0, // Somewhat relevant
			"doc4": 0.0, // Not relevant
			"doc5": 2.5, // Highly relevant
		},
		Description: "Query about ML algorithms",
	},
	{
		Query:     "deep learning neural networks",
		QueryType: "analytical",
		Relevance: map[string]float64{
			"doc6":  3.0,
			"doc7":  1.5,
			"doc8":  2.0,
			"doc9":  0.5,
			"doc10": 2.5,
		},
		Description: "Query about deep learning",
	},
}

func TestRecallAtK(t *testing.T) {
	harness := NewEvaluationHarness(DefaultEvaluationConfig())
	harness.LoadGroundTruth(testGroundTruth)
	
	// Test perfect recall scenario
	perfectResults := []types.DocumentReference{
		{ID: "doc1", UtilityScore: 0.95, Content: "Sample content 1"},
		{ID: "doc2", UtilityScore: 0.85, Content: "Sample content 2"},
		{ID: "doc3", UtilityScore: 0.75, Content: "Sample content 3"},
		{ID: "doc5", UtilityScore: 0.65, Content: "Sample content 5"},
	}
	
	gt := &testGroundTruth[0]
	
	// Test Recall@1: should be 1.0 (1 relevant out of 1 retrieved, 4 total relevant)
	recall1 := harness.calculateRecallAtK(perfectResults, gt, 1)
	expected1 := 1.0 / 4.0 // 1 relevant doc retrieved, 4 total relevant (doc1,doc2,doc3,doc5)
	if abs(recall1-expected1) > 0.001 {
		t.Errorf("Recall@1: expected %.3f, got %.3f", expected1, recall1)
	}
	
	// Test Recall@3: should be 3/4 = 0.75
	recall3 := harness.calculateRecallAtK(perfectResults, gt, 3)
	expected3 := 3.0 / 4.0 // 3 relevant docs retrieved out of 4 total relevant
	if abs(recall3-expected3) > 0.001 {
		t.Errorf("Recall@3: expected %.3f, got %.3f", expected3, recall3)
	}
	
	// Test with partial results
	partialResults := []types.DocumentReference{
		{ID: "doc1", UtilityScore: 0.95, Content: "Sample content 1"},
		{ID: "doc4", UtilityScore: 0.85, Content: "Sample content 4"}, // Not relevant
	}
	
	recall2 := harness.calculateRecallAtK(partialResults, gt, 2)
	expected2 := 1.0 / 4.0 // 1 relevant out of 4 total relevant
	if abs(recall2-expected2) > 0.001 {
		t.Errorf("Partial Recall@2: expected %.3f, got %.3f", expected2, recall2)
	}
}

func TestNDCGAtK(t *testing.T) {
	harness := NewEvaluationHarness(DefaultEvaluationConfig())
	harness.LoadGroundTruth(testGroundTruth)
	
	// Test results in relevance order
	orderedResults := []types.DocumentReference{
		{ID: "doc1", UtilityScore: 0.95, Content: "Sample content 1"}, // relevance 3.0
		{ID: "doc5", UtilityScore: 0.85, Content: "Sample content 5"}, // relevance 2.5
		{ID: "doc2", UtilityScore: 0.75, Content: "Sample content 2"}, // relevance 2.0
	}
	
	gt := &testGroundTruth[0]
	
	// Calculate nDCG@3
	ndcg3 := harness.calculateNDCGAtK(orderedResults, gt, 3)
	
	// Manual calculation:
	// DCG = 3.0 + 2.5/log2(3) + 2.0/log2(4) = 3.0 + 1.585 + 1.0 = 5.585
	// IDCG = 3.0 + 2.5/log2(3) + 2.0/log2(4) = 5.585 (same order)
	// nDCG = 5.585 / 5.585 = 1.0
	expectedNDCG3 := 1.0
	if abs(ndcg3-expectedNDCG3) > 0.01 {
		t.Errorf("nDCG@3: expected %.3f, got %.3f", expectedNDCG3, ndcg3)
	}
	
	// Test with reversed order (worst case)
	reversedResults := []types.DocumentReference{
		{ID: "doc2", UtilityScore: 0.95, Content: "Sample content 2"}, // relevance 2.0
		{ID: "doc5", UtilityScore: 0.85, Content: "Sample content 5"}, // relevance 2.5
		{ID: "doc1", UtilityScore: 0.75, Content: "Sample content 1"}, // relevance 3.0
	}
	
	ndcg3Rev := harness.calculateNDCGAtK(reversedResults, gt, 3)
	// Should be lower than perfect ordering
	if ndcg3Rev >= ndcg3 {
		t.Errorf("Reversed order nDCG should be lower: perfect=%.3f, reversed=%.3f", ndcg3, ndcg3Rev)
	}
}

func TestMAPCalculation(t *testing.T) {
	harness := NewEvaluationHarness(DefaultEvaluationConfig())
	harness.LoadGroundTruth(testGroundTruth)
	
	// Test results with relevant docs at positions 1, 3, 4
	mixedResults := []types.DocumentReference{
		{ID: "doc1", UtilityScore: 0.95, Content: "Sample content 1"}, // relevant (pos 1)
		{ID: "doc4", UtilityScore: 0.85, Content: "Sample content 4"}, // not relevant (pos 2)
		{ID: "doc2", UtilityScore: 0.75, Content: "Sample content 2"}, // relevant (pos 3)
		{ID: "doc5", UtilityScore: 0.65, Content: "Sample content 5"}, // relevant (pos 4)
	}
	
	gt := &testGroundTruth[0]
	
	map_score := harness.calculateMAP(mixedResults, gt)
	
	// Manual calculation:
	// Precision at relevant positions: 1/1=1.0, 2/3=0.667, 3/4=0.75
	// MAP = (1.0 + 0.667 + 0.75) / 4 = 0.604 (averaged over 4 total relevant docs)
	expectedMAP := (1.0 + 2.0/3.0 + 3.0/4.0) / 4.0
	if abs(map_score-expectedMAP) > 0.01 {
		t.Errorf("MAP: expected %.3f, got %.3f", expectedMAP, map_score)
	}
}

func TestMRRCalculation(t *testing.T) {
	harness := NewEvaluationHarness(DefaultEvaluationConfig())
	harness.LoadGroundTruth(testGroundTruth)
	
	// Test with first relevant doc at position 3
	results := []types.DocumentReference{
		{ID: "doc4", UtilityScore: 0.95, Content: "Sample content 4"}, // not relevant
		{ID: "unknown", UtilityScore: 0.85, Content: "Sample content unknown"}, // not relevant
		{ID: "doc2", UtilityScore: 0.75, Content: "Sample content 2"}, // relevant (first)
	}
	
	gt := &testGroundTruth[0]
	
	mrr := harness.calculateMRR(results, gt)
	expectedMRR := 1.0 / 3.0 // First relevant doc at position 3
	
	if abs(mrr-expectedMRR) > 0.001 {
		t.Errorf("MRR: expected %.3f, got %.3f", expectedMRR, mrr)
	}
}

func TestEvaluateQuery(t *testing.T) {
	harness := NewEvaluationHarness(DefaultEvaluationConfig())
	harness.LoadGroundTruth(testGroundTruth)
	
	results := []types.DocumentReference{
		{ID: "doc1", UtilityScore: 0.95, Content: "Sample content for doc 1"},
		{ID: "doc2", UtilityScore: 0.85, Content: "Sample content for doc 2"},
		{ID: "doc4", UtilityScore: 0.75, Content: "Sample content for doc 4"},
	}
	
	evalResult, err := harness.EvaluateQuery(
		"machine learning algorithms",
		results,
		"contextlite_optimization",
		50, // latency
		25.5, // memory
	)
	
	if err != nil {
		t.Fatalf("EvaluateQuery failed: %v", err)
	}
	
	// Verify basic fields
	if evalResult.SystemType != "contextlite_optimization" {
		t.Errorf("Expected system type contextlite_optimization, got %s", evalResult.SystemType)
	}
	
	if evalResult.QueryType != "factual" {
		t.Errorf("Expected query type factual, got %s", evalResult.QueryType)
	}
	
	// Context length will be sum of content lengths / 4
	// "Sample content for doc 1" = 25 chars, "Sample content for doc 2" = 25 chars, "Sample content for doc 4" = 25 chars
	// Total = 75 chars, estimated tokens = 75/4 = 18
	if evalResult.ContextLength != 18 {
		t.Errorf("Expected context length 18, got %d", evalResult.ContextLength)
	}
	
	if evalResult.LatencyMs != 50 {
		t.Errorf("Expected latency 50ms, got %d", evalResult.LatencyMs)
	}
	
	// Verify metrics are computed
	if evalResult.RecallAt3 == 0 {
		t.Error("RecallAt3 should be > 0")
	}
	
	if evalResult.NDCG3 == 0 {
		t.Error("NDCG3 should be > 0")
	}
	
	if evalResult.MAP == 0 {
		t.Error("MAP should be > 0")
	}
}

func TestBatchEvaluate(t *testing.T) {
	harness := NewEvaluationHarness(DefaultEvaluationConfig())
	harness.LoadGroundTruth(testGroundTruth)
	
	queryResults := map[string]QueryResult{
		"machine learning algorithms": {
			Documents: []types.DocumentReference{
				{ID: "doc1", UtilityScore: 0.95, Content: "Machine learning content 1"},
				{ID: "doc2", UtilityScore: 0.85, Content: "Machine learning content 2"},
			},
			LatencyMs: 45,
			MemoryMB:  20.0,
		},
		"deep learning neural networks": {
			Documents: []types.DocumentReference{
				{ID: "doc6", UtilityScore: 0.90, Content: "Deep learning content 6"},
				{ID: "doc8", UtilityScore: 0.80, Content: "Deep learning content 8"},
			},
			LatencyMs: 55,
			MemoryMB:  22.0,
		},
	}
	
	aggResults, err := harness.BatchEvaluate(queryResults, "contextlite_optimization")
	if err != nil {
		t.Fatalf("BatchEvaluate failed: %v", err)
	}
	
	if aggResults.QueryCount != 2 {
		t.Errorf("Expected 2 queries, got %d", aggResults.QueryCount)
	}
	
	if aggResults.SystemType != "contextlite_optimization" {
		t.Errorf("Expected system type contextlite_optimization, got %s", aggResults.SystemType)
	}
	
	// Mean latency should be (45+55)/2 = 50
	expectedLatency := 50.0
	if abs(aggResults.MeanLatencyMs-expectedLatency) > 0.1 {
		t.Errorf("Expected mean latency %.1f, got %.1f", expectedLatency, aggResults.MeanLatencyMs)
	}
	
	// Verify standard deviations are computed
	if aggResults.StdLatencyMs == 0 {
		t.Error("Standard deviation should be > 0")
	}
}

func TestGroundTruthLoading(t *testing.T) {
	harness := NewEvaluationHarness(nil) // Test default config
	
	if len(harness.groundTruth) != 0 {
		t.Error("Initial ground truth should be empty")
	}
	
	harness.LoadGroundTruth(testGroundTruth)
	
	if len(harness.groundTruth) != 2 {
		t.Errorf("Expected 2 ground truth entries, got %d", len(harness.groundTruth))
	}
	
	// Test loading additional ground truth
	additionalGT := []GroundTruth{
		{
			Query:     "test query",
			QueryType: "factual",
			Relevance: map[string]float64{"doc_test": 2.0},
		},
	}
	
	harness.LoadGroundTruth(additionalGT)
	
	if len(harness.groundTruth) != 3 {
		t.Errorf("Expected 3 ground truth entries after addition, got %d", len(harness.groundTruth))
	}
}

// Helper function for floating point comparison
func abs(x float64) float64 {
	if x < 0 {
		return -x
	}
	return x
}

func TestMRREdgeCases(t *testing.T) {
	harness := NewEvaluationHarness(DefaultEvaluationConfig())
	harness.LoadGroundTruth(testGroundTruth)
	
	// Test with no relevant documents
	noRelevantResults := []types.DocumentReference{
		{ID: "doc4", UtilityScore: 0.95, Content: "Not relevant"}, // relevance 0.0
		{ID: "unknown", UtilityScore: 0.85, Content: "Unknown doc"},
	}
	
	gt := &testGroundTruth[0]
	mrr := harness.calculateMRR(noRelevantResults, gt)
	
	if mrr != 0.0 {
		t.Errorf("MRR with no relevant docs: expected 0.0, got %.3f", mrr)
	}
}

func TestBatchEvaluateEdgeCases(t *testing.T) {
	harness := NewEvaluationHarness(DefaultEvaluationConfig())
	harness.LoadGroundTruth(testGroundTruth)
	
	// Test with empty query results
	emptyResults := map[string]QueryResult{}
	
	_, err := harness.BatchEvaluate(emptyResults, "test_system")
	if err == nil {
		t.Error("Expected error for empty query results")
	}
	
	// Test with query not in ground truth
	unknownQueryResults := map[string]QueryResult{
		"unknown query": {
			Documents: []types.DocumentReference{
				{ID: "doc1", UtilityScore: 0.95, Content: "Content"},
			},
			LatencyMs: 50,
			MemoryMB:  25.0,
		},
	}
	
	_, err = harness.BatchEvaluate(unknownQueryResults, "test_system")
	if err == nil {
		t.Error("Expected error for unknown query")
	}
}

func TestCalculateRecallAtKEdgeCases(t *testing.T) {
	harness := NewEvaluationHarness(DefaultEvaluationConfig())
	harness.LoadGroundTruth(testGroundTruth)
	
	gt := &testGroundTruth[0]
	
	// Test with empty results
	emptyResults := []types.DocumentReference{}
	recall := harness.calculateRecallAtK(emptyResults, gt, 5)
	
	if recall != 0.0 {
		t.Errorf("Recall with empty results: expected 0.0, got %.3f", recall)
	}
	
	// Test with k larger than results
	smallResults := []types.DocumentReference{
		{ID: "doc1", UtilityScore: 0.95, Content: "Content"},
	}
	recall = harness.calculateRecallAtK(smallResults, gt, 10)
	expected := 1.0 / 4.0 // 1 relevant out of 4 total relevant
	
	if abs(recall-expected) > 0.001 {
		t.Errorf("Recall with k > results: expected %.3f, got %.3f", expected, recall)
	}
}

func TestCalculateNDCGAtKEdgeCases(t *testing.T) {
	harness := NewEvaluationHarness(DefaultEvaluationConfig())
	harness.LoadGroundTruth(testGroundTruth)
	
	gt := &testGroundTruth[0]
	
	// Test with empty results
	emptyResults := []types.DocumentReference{}
	ndcg := harness.calculateNDCGAtK(emptyResults, gt, 5)
	
	if ndcg != 0.0 {
		t.Errorf("NDCG with empty results: expected 0.0, got %.3f", ndcg)
	}
	
	// Test with no relevant documents
	irrelevantResults := []types.DocumentReference{
		{ID: "doc4", UtilityScore: 0.95, Content: "Content"}, // relevance 0.0
		{ID: "unknown", UtilityScore: 0.85, Content: "Content"},
	}
	ndcg = harness.calculateNDCGAtK(irrelevantResults, gt, 2)
	
	if ndcg != 0.0 {
		t.Errorf("NDCG with no relevant docs: expected 0.0, got %.3f", ndcg)
	}
}

func TestCalculateMAPEdgeCases(t *testing.T) {
	harness := NewEvaluationHarness(DefaultEvaluationConfig())
	harness.LoadGroundTruth(testGroundTruth)
	
	gt := &testGroundTruth[0]
	
	// Test with empty results
	emptyResults := []types.DocumentReference{}
	map_score := harness.calculateMAP(emptyResults, gt)
	
	if map_score != 0.0 {
		t.Errorf("MAP with empty results: expected 0.0, got %.3f", map_score)
	}
	
	// Test with no relevant documents
	irrelevantResults := []types.DocumentReference{
		{ID: "doc4", UtilityScore: 0.95, Content: "Content"}, // relevance 0.0
		{ID: "unknown", UtilityScore: 0.85, Content: "Content"},
	}
	map_score = harness.calculateMAP(irrelevantResults, gt)
	
	if map_score != 0.0 {
		t.Errorf("MAP with no relevant docs: expected 0.0, got %.3f", map_score)
	}
}
