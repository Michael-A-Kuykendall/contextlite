package types

import (
	"testing"
	"time"
)

func TestFeatureWeights_Fields(t *testing.T) {
	weights := FeatureWeights{
		Relevance:    0.30,
		Recency:      0.20,
		Entanglement: 0.15,
		Prior:        0.15,
		Authority:    0.10,
		Specificity:  0.05,
		Uncertainty:  0.05,
	}

	if weights.Relevance != 0.30 {
		t.Errorf("Expected Relevance to be 0.30, got %f", weights.Relevance)
	}
	if weights.Recency != 0.20 {
		t.Errorf("Expected Recency to be 0.20, got %f", weights.Recency)
	}
	if weights.Entanglement != 0.15 {
		t.Errorf("Expected Entanglement to be 0.15, got %f", weights.Entanglement)
	}
	if weights.Prior != 0.15 {
		t.Errorf("Expected Prior to be 0.15, got %f", weights.Prior)
	}
	if weights.Authority != 0.10 {
		t.Errorf("Expected Authority to be 0.10, got %f", weights.Authority)
	}
	if weights.Specificity != 0.05 {
		t.Errorf("Expected Specificity to be 0.05, got %f", weights.Specificity)
	}
	if weights.Uncertainty != 0.05 {
		t.Errorf("Expected Uncertainty to be 0.05, got %f", weights.Uncertainty)
	}
}

func TestSelectionConstraints_Fields(t *testing.T) {
	budgets := SelectionConstraints{
		MaxTokens:          4000,
		MaxDocuments:       10,
		MinRelevance:       0.3,
		DiversityThreshold: 0.5,
	}

	if budgets.MaxTokens != 4000 {
		t.Errorf("Expected MaxTokens to be 4000, got %d", budgets.MaxTokens)
	}
	if budgets.MaxDocuments != 10 {
		t.Errorf("Expected MaxDocuments to be 10, got %d", budgets.MaxDocuments)
	}
	if budgets.MinRelevance != 0.3 {
		t.Errorf("Expected MinRelevance to be 0.3, got %f", budgets.MinRelevance)
	}
	if budgets.DiversityThreshold != 0.5 {
		t.Errorf("Expected DiversityThreshold to be 0.5, got %f", budgets.DiversityThreshold)
	}
}

func TestOptimizationStrategy_Constants(t *testing.T) {
	if StrategyWeightedSum != "weighted-sum" {
		t.Errorf("Expected StrategyWeightedSum to be 'weighted-sum', got %s", StrategyWeightedSum)
	}
	if StrategyLexicographic != "lexicographic" {
		t.Errorf("Expected StrategyLexicographic to be 'lexicographic', got %s", StrategyLexicographic)
	}
	if StrategyEpsilonConstraint != "epsilon-budget" {
		t.Errorf("Expected StrategyEpsilonConstraint to be 'epsilon-budget', got %s", StrategyEpsilonConstraint)
	}
}

func TestSolverStats_Fields(t *testing.T) {
	duration := time.Duration(1500 * time.Microsecond)
	stats := SolverStats{
		TotalSolves:      100,
		AverageSolveTime: duration,
		TimeoutCount:     5,
		OptimalityGap:    0.02,
		LastSolveTime:    duration,
	}

	if stats.TotalSolves != 100 {
		t.Errorf("Expected TotalSolves to be 100, got %d", stats.TotalSolves)
	}
	if stats.AverageSolveTime != duration {
		t.Errorf("Expected AverageSolveTime to be %v, got %v", duration, stats.AverageSolveTime)
	}
	if stats.TimeoutCount != 5 {
		t.Errorf("Expected TimeoutCount to be 5, got %d", stats.TimeoutCount)
	}
	if stats.OptimalityGap != 0.02 {
		t.Errorf("Expected OptimalityGap to be 0.02, got %f", stats.OptimalityGap)
	}
	if stats.LastSolveTime != duration {
		t.Errorf("Expected LastSolveTime to be %v, got %v", duration, stats.LastSolveTime)
	}
}

func TestEngineConfig_Fields(t *testing.T) {
	weights := FeatureWeights{Relevance: 0.3, Recency: 0.2}
	timeout := time.Duration(500 * time.Millisecond)
	cacheTTL := time.Duration(300 * time.Second)

	config := EngineConfig{
		FeatureWeights:       weights,
		OptimizationStrategy: StrategyWeightedSum,
		SolverTimeout:        timeout,
		MaxOptimalityGap:     0.05,
		MaxCandidates:        100,
		ConcurrentWorkers:    4,
		CacheEnabled:         true,
		CacheSize:            1000,
		CacheTTL:             cacheTTL,
	}

	if config.FeatureWeights.Relevance != 0.3 {
		t.Errorf("Expected FeatureWeights.Relevance to be 0.3, got %f", config.FeatureWeights.Relevance)
	}
	if config.OptimizationStrategy != StrategyWeightedSum {
		t.Errorf("Expected OptimizationStrategy to be %s, got %s", StrategyWeightedSum, config.OptimizationStrategy)
	}
	if config.SolverTimeout != timeout {
		t.Errorf("Expected SolverTimeout to be %v, got %v", timeout, config.SolverTimeout)
	}
	if config.MaxOptimalityGap != 0.05 {
		t.Errorf("Expected MaxOptimalityGap to be 0.05, got %f", config.MaxOptimalityGap)
	}
	if config.MaxCandidates != 100 {
		t.Errorf("Expected MaxCandidates to be 100, got %d", config.MaxCandidates)
	}
	if config.ConcurrentWorkers != 4 {
		t.Errorf("Expected ConcurrentWorkers to be 4, got %d", config.ConcurrentWorkers)
	}
	if config.CacheEnabled != true {
		t.Errorf("Expected CacheEnabled to be true, got %t", config.CacheEnabled)
	}
	if config.CacheSize != 1000 {
		t.Errorf("Expected CacheSize to be 1000, got %d", config.CacheSize)
	}
	if config.CacheTTL != cacheTTL {
		t.Errorf("Expected CacheTTL to be %v, got %v", cacheTTL, config.CacheTTL)
	}
}

func TestEngineStats_Fields(t *testing.T) {
	queryTime := time.Duration(150 * time.Millisecond)
	featureTime := time.Duration(50 * time.Millisecond)
	solverStats := SolverStats{TotalSolves: 10}

	stats := EngineStats{
		TotalQueries:          1000,
		AverageQueryTime:      queryTime,
		CacheHitRate:          0.75,
		TotalDocuments:        5000,
		IndexedWorkspaces:     3,
		FeatureExtractionTime: featureTime,
		SolverStats:           solverStats,
		MemoryUsageMB:         256.5,
		LicenseTier:           "Professional",
		LicenseValid:          true,
	}

	if stats.TotalQueries != 1000 {
		t.Errorf("Expected TotalQueries to be 1000, got %d", stats.TotalQueries)
	}
	if stats.AverageQueryTime != queryTime {
		t.Errorf("Expected AverageQueryTime to be %v, got %v", queryTime, stats.AverageQueryTime)
	}
	if stats.CacheHitRate != 0.75 {
		t.Errorf("Expected CacheHitRate to be 0.75, got %f", stats.CacheHitRate)
	}
	if stats.TotalDocuments != 5000 {
		t.Errorf("Expected TotalDocuments to be 5000, got %d", stats.TotalDocuments)
	}
	if stats.IndexedWorkspaces != 3 {
		t.Errorf("Expected IndexedWorkspaces to be 3, got %d", stats.IndexedWorkspaces)
	}
	if stats.FeatureExtractionTime != featureTime {
		t.Errorf("Expected FeatureExtractionTime to be %v, got %v", featureTime, stats.FeatureExtractionTime)
	}
	if stats.SolverStats.TotalSolves != 10 {
		t.Errorf("Expected SolverStats.TotalSolves to be 10, got %d", stats.SolverStats.TotalSolves)
	}
	if stats.MemoryUsageMB != 256.5 {
		t.Errorf("Expected MemoryUsageMB to be 256.5, got %f", stats.MemoryUsageMB)
	}
	if stats.LicenseTier != "Professional" {
		t.Errorf("Expected LicenseTier to be 'Professional', got %s", stats.LicenseTier)
	}
	if stats.LicenseValid != true {
		t.Errorf("Expected LicenseValid to be true, got %t", stats.LicenseValid)
	}
}

func TestCacheStats_Fields(t *testing.T) {
	stats := CacheStats{
		Hits:    750,
		Misses:  250,
		HitRate: 0.75,
		L1Size:  100,
		L2Size:  500,
	}

	if stats.Hits != 750 {
		t.Errorf("Expected Hits to be 750, got %d", stats.Hits)
	}
	if stats.Misses != 250 {
		t.Errorf("Expected Misses to be 250, got %d", stats.Misses)
	}
	if stats.HitRate != 0.75 {
		t.Errorf("Expected HitRate to be 0.75, got %f", stats.HitRate)
	}
	if stats.L1Size != 100 {
		t.Errorf("Expected L1Size to be 100, got %d", stats.L1Size)
	}
	if stats.L2Size != 500 {
		t.Errorf("Expected L2Size to be 500, got %d", stats.L2Size)
	}
}

func TestWorkspaceStats_Fields(t *testing.T) {
	lastIndexed := time.Now()
	stats := WorkspaceStats{
		Path:            "/workspace/test",
		DocumentCount:   500,
		TotalTokens:     1000000,
		LastIndexed:     lastIndexed,
		Languages:       []string{"go", "python", "javascript"},
		AverageFileSize: 2048,
	}

	if stats.Path != "/workspace/test" {
		t.Errorf("Expected Path to be '/workspace/test', got %s", stats.Path)
	}
	if stats.DocumentCount != 500 {
		t.Errorf("Expected DocumentCount to be 500, got %d", stats.DocumentCount)
	}
	if stats.TotalTokens != 1000000 {
		t.Errorf("Expected TotalTokens to be 1000000, got %d", stats.TotalTokens)
	}
	if stats.LastIndexed != lastIndexed {
		t.Errorf("Expected LastIndexed to be %v, got %v", lastIndexed, stats.LastIndexed)
	}
	if len(stats.Languages) != 3 {
		t.Errorf("Expected Languages length to be 3, got %d", len(stats.Languages))
	}
	if stats.Languages[0] != "go" {
		t.Errorf("Expected Languages[0] to be 'go', got %s", stats.Languages[0])
	}
	if stats.AverageFileSize != 2048 {
		t.Errorf("Expected AverageFileSize to be 2048, got %d", stats.AverageFileSize)
	}
}

func TestoptimizationResult_Fields(t *testing.T) {
	result := optimizationResult{
		SelectedDocs:    []int{0, 2, 5, 8},
		SolverUsed:      "z3",
		optimizerStatus:        "sat",
		Objective:       123.45,
		SolveTimeUs:     1500,
		VariableCount:   20,
		ConstraintCount: 15,
		KCandidates:     10,
		PairsCount:      45,
		BudgetTokens:    4000,
		MaxDocs:         5,
		FallbackReason:  "",
	}

	if len(result.SelectedDocs) != 4 {
		t.Errorf("Expected SelectedDocs length to be 4, got %d", len(result.SelectedDocs))
	}
	if result.SelectedDocs[0] != 0 {
		t.Errorf("Expected SelectedDocs[0] to be 0, got %d", result.SelectedDocs[0])
	}
	if result.SolverUsed != "z3" {
		t.Errorf("Expected SolverUsed to be 'z3', got %s", result.SolverUsed)
	}
	if result.optimizerStatus != "sat" {
		t.Errorf("Expected optimizerStatus to be 'sat', got %s", result.optimizerStatus)
	}
	if result.Objective != 123.45 {
		t.Errorf("Expected Objective to be 123.45, got %f", result.Objective)
	}
	if result.SolveTimeUs != 1500 {
		t.Errorf("Expected SolveTimeUs to be 1500, got %d", result.SolveTimeUs)
	}
	if result.VariableCount != 20 {
		t.Errorf("Expected VariableCount to be 20, got %d", result.VariableCount)
	}
	if result.ConstraintCount != 15 {
		t.Errorf("Expected ConstraintCount to be 15, got %d", result.ConstraintCount)
	}
	if result.KCandidates != 10 {
		t.Errorf("Expected KCandidates to be 10, got %d", result.KCandidates)
	}
	if result.BudgetTokens != 4000 {
		t.Errorf("Expected BudgetTokens to be 4000, got %d", result.BudgetTokens)
	}
}

func TestContextRequest_Fields(t *testing.T) {
	req := ContextRequest{
		Query:         "test context request",
		MaxTokens:     3000,
		MaxDocuments:  8,
		WorkspacePath: "/test/workspace",
	}

	if req.Query != "test context request" {
		t.Errorf("Expected Query to be 'test context request', got %s", req.Query)
	}
	if req.MaxTokens != 3000 {
		t.Errorf("Expected MaxTokens to be 3000, got %d", req.MaxTokens)
	}
	if req.MaxDocuments != 8 {
		t.Errorf("Expected MaxDocuments to be 8, got %d", req.MaxDocuments)
	}
	if req.WorkspacePath != "/test/workspace" {
		t.Errorf("Expected WorkspacePath to be '/test/workspace', got %s", req.WorkspacePath)
	}
}

func TestContextResult_Fields(t *testing.T) {
	docs := []DocumentReference{{ID: "doc1"}, {ID: "doc2"}}
	processingTime := time.Duration(200 * time.Millisecond)
	optimizationMetrics := &optimizationResult{SolverUsed: "z3", optimizerStatus: "sat"}

	result := ContextResult{
		Context:        "assembled context content",
		Documents:      docs,
		TotalTokens:    2000,
		ProcessingTime: processingTime,
		CacheHit:       false,
		Message:        "context assembled successfully",
		CoherenceScore: 0.88,
		optimizationMetrics:     optimizationMetrics,
	}

	if result.Context != "assembled context content" {
		t.Errorf("Expected Context to be 'assembled context content', got %s", result.Context)
	}
	if len(result.Documents) != 2 {
		t.Errorf("Expected Documents length to be 2, got %d", len(result.Documents))
	}
	if result.Documents[0].ID != "doc1" {
		t.Errorf("Expected Documents[0].ID to be 'doc1', got %s", result.Documents[0].ID)
	}
	if result.TotalTokens != 2000 {
		t.Errorf("Expected TotalTokens to be 2000, got %d", result.TotalTokens)
	}
	if result.ProcessingTime != processingTime {
		t.Errorf("Expected ProcessingTime to be %v, got %v", processingTime, result.ProcessingTime)
	}
	if result.CacheHit != false {
		t.Errorf("Expected CacheHit to be false, got %t", result.CacheHit)
	}
	if result.Message != "context assembled successfully" {
		t.Errorf("Expected Message to be 'context assembled successfully', got %s", result.Message)
	}
	if result.CoherenceScore != 0.88 {
		t.Errorf("Expected CoherenceScore to be 0.88, got %f", result.CoherenceScore)
	}
	if result.optimizationMetrics.SolverUsed != "z3" {
		t.Errorf("Expected optimizationMetrics.SolverUsed to be 'z3', got %s", result.optimizationMetrics.SolverUsed)
	}
}