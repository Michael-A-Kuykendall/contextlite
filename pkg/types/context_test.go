package types

import (
	"testing"
)

func TestoptimizationMetrics_Fields(t *testing.T) {
	metrics := optimizationMetrics{
		SolverUsed:      "z3",
		optimizerStatus:        "sat",
		Objective:       12345,
		SolveTimeUs:     1000,
		SolveTimeMs:     1.0,
		optimizationWallUs:       1500,
		optimizationWallMs:       1.5,
		VariableCount:   10,
		ConstraintCount: 5,
		KCandidates:     20,
		PairsCount:      15,
		BudgetTokens:    4000,
		MaxDocs:         10,
		FallbackReason:  "timeout",
	}

	if metrics.SolverUsed != "z3" {
		t.Errorf("Expected SolverUsed to be 'z3', got %s", metrics.SolverUsed)
	}
	if metrics.optimizerStatus != "sat" {
		t.Errorf("Expected optimizerStatus to be 'sat', got %s", metrics.optimizerStatus)
	}
	if metrics.Objective != 12345 {
		t.Errorf("Expected Objective to be 12345, got %d", metrics.Objective)
	}
	if metrics.SolveTimeUs != 1000 {
		t.Errorf("Expected SolveTimeUs to be 1000, got %d", metrics.SolveTimeUs)
	}
	if metrics.SolveTimeMs != 1.0 {
		t.Errorf("Expected SolveTimeMs to be 1.0, got %f", metrics.SolveTimeMs)
	}
	if metrics.VariableCount != 10 {
		t.Errorf("Expected VariableCount to be 10, got %d", metrics.VariableCount)
	}
	if metrics.BudgetTokens != 4000 {
		t.Errorf("Expected BudgetTokens to be 4000, got %d", metrics.BudgetTokens)
	}
}

func TestStageTimings_Fields(t *testing.T) {
	timings := StageTimings{
		FTSHarvestUs:   1000,
		FeatureBuildUs: 2000,
		optimizationSolverUs:    3000,
		optimizationWallUs:      3500,
		TotalUs:        6500,
		FTSHarvestMs:   1.0,
		FeatureBuildMs: 2.0,
		optimizationSolverMs:    3.0,
		optimizationWallMs:      3.5,
		TotalMs:        6.5,
	}

	if timings.FTSHarvestUs != 1000 {
		t.Errorf("Expected FTSHarvestUs to be 1000, got %d", timings.FTSHarvestUs)
	}
	if timings.FeatureBuildUs != 2000 {
		t.Errorf("Expected FeatureBuildUs to be 2000, got %d", timings.FeatureBuildUs)
	}
	if timings.optimizationSolverUs != 3000 {
		t.Errorf("Expected optimizationSolverUs to be 3000, got %d", timings.optimizationSolverUs)
	}
	if timings.TotalMs != 6.5 {
		t.Errorf("Expected TotalMs to be 6.5, got %f", timings.TotalMs)
	}
}

func TestAssembleRequest_Fields(t *testing.T) {
	req := AssembleRequest{
		Query:           "test query",
		MaxTokens:       4000,
		MaxDocuments:    10,
		WorkspacePath:   "/workspace",
		IncludePatterns: []string{"*.go", "*.md"},
		ExcludePatterns: []string{"*.tmp"},
		ModelID:         "gpt-4",
		Useoptimization:          true,
		optimizationTimeoutMs:    500,
		MaxOptGap:       0.05,
		ObjectiveStyle:  "weighted-sum",
		EnableSampling:  false,
		Temperature:     0.7,
		TopK:            5,
		UseCache:        true,
		CacheTTL:        300,
	}

	if req.Query != "test query" {
		t.Errorf("Expected Query to be 'test query', got %s", req.Query)
	}
	if req.MaxTokens != 4000 {
		t.Errorf("Expected MaxTokens to be 4000, got %d", req.MaxTokens)
	}
	if req.MaxDocuments != 10 {
		t.Errorf("Expected MaxDocuments to be 10, got %d", req.MaxDocuments)
	}
	if req.WorkspacePath != "/workspace" {
		t.Errorf("Expected WorkspacePath to be '/workspace', got %s", req.WorkspacePath)
	}
	if len(req.IncludePatterns) != 2 {
		t.Errorf("Expected IncludePatterns length to be 2, got %d", len(req.IncludePatterns))
	}
	if req.Useoptimization != true {
		t.Errorf("Expected Useoptimization to be true, got %t", req.Useoptimization)
	}
	if req.optimizationTimeoutMs != 500 {
		t.Errorf("Expected optimizationTimeoutMs to be 500, got %d", req.optimizationTimeoutMs)
	}
	if req.MaxOptGap != 0.05 {
		t.Errorf("Expected MaxOptGap to be 0.05, got %f", req.MaxOptGap)
	}
	if req.ObjectiveStyle != "weighted-sum" {
		t.Errorf("Expected ObjectiveStyle to be 'weighted-sum', got %s", req.ObjectiveStyle)
	}
}

func TestAssembledContext_Fields(t *testing.T) {
	docs := []DocumentReference{
		{ID: "doc1", Path: "/path1"},
		{ID: "doc2", Path: "/path2"},
	}
	metrics := optimizationMetrics{SolverUsed: "z3", SolveTimeMs: 1.5}
	timings := StageTimings{TotalMs: 5.0}

	ctx := AssembledContext{
		Query:          "test query",
		Documents:      docs,
		TotalTokens:    2500,
		CoherenceScore: 0.85,
		optimizationMetrics:     metrics,
		Timings:        timings,
	}

	if ctx.Query != "test query" {
		t.Errorf("Expected Query to be 'test query', got %s", ctx.Query)
	}
	if len(ctx.Documents) != 2 {
		t.Errorf("Expected Documents length to be 2, got %d", len(ctx.Documents))
	}
	if ctx.TotalTokens != 2500 {
		t.Errorf("Expected TotalTokens to be 2500, got %d", ctx.TotalTokens)
	}
	if ctx.CoherenceScore != 0.85 {
		t.Errorf("Expected CoherenceScore to be 0.85, got %f", ctx.CoherenceScore)
	}
	if ctx.optimizationMetrics.SolverUsed != "z3" {
		t.Errorf("Expected optimizationMetrics.SolverUsed to be 'z3', got %s", ctx.optimizationMetrics.SolverUsed)
	}
}

func TestQueryResult_Fields(t *testing.T) {
	docs := []DocumentReference{{ID: "doc1"}}
	metrics := optimizationMetrics{SolverUsed: "z3"}
	timings := StageTimings{TotalMs: 3.0}

	result := QueryResult{
		Query:          "search query",
		Documents:      docs,
		TotalDocuments: 5,
		TotalTokens:    1500,
		CoherenceScore: 0.75,
		optimizationMetrics:     metrics,
		Timings:        timings,
		CacheHit:       true,
		CacheKey:       "cache123",
	}

	if result.Query != "search query" {
		t.Errorf("Expected Query to be 'search query', got %s", result.Query)
	}
	if result.TotalDocuments != 5 {
		t.Errorf("Expected TotalDocuments to be 5, got %d", result.TotalDocuments)
	}
	if result.TotalTokens != 1500 {
		t.Errorf("Expected TotalTokens to be 1500, got %d", result.TotalTokens)
	}
	if result.CoherenceScore != 0.75 {
		t.Errorf("Expected CoherenceScore to be 0.75, got %f", result.CoherenceScore)
	}
	if result.CacheHit != true {
		t.Errorf("Expected CacheHit to be true, got %t", result.CacheHit)
	}
	if result.CacheKey != "cache123" {
		t.Errorf("Expected CacheKey to be 'cache123', got %s", result.CacheKey)
	}
}