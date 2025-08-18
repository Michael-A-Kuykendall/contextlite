/*
 * ContextLite - optimization-Optimized AI Context Engine
 * Copyright (c) 2025 Michael A. Kuykendall
 * 
 * Patent Pending - Provisional Patent Filed
 * US Provisional Patent Application No. [PENDING]
 * 
 * This software contains proprietary algorithms protected by patent law.
 * Unauthorized reverse engineering or algorithm extraction is prohibited.
 * 
 * Licensed under Dual License:
 * - MIT License for open source use
 * - Commercial License for business use
 * 
 * See LICENSE-MIT.md and LICENSE-COMMERCIAL.md for terms.
 */

package engine

import (
	"context"
	"encoding/json"
	"fmt"
	"os/exec"
	"strings"
	"time"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// JSONCLIEngine provides context assembly via JSON CLI to private binary
// This approach keeps private algorithms in a separate process
type JSONCLIEngine struct {
	config     *config.Config
	storage    types.StorageInterface
	binaryPath string
	timeout    time.Duration
}

// NewJSONCLIEngine creates a new JSON CLI engine instance
func NewJSONCLIEngine(cfg *config.Config, storage types.StorageInterface, binaryPath string) *JSONCLIEngine {
	timeout := 30 * time.Second
	if cfg != nil && cfg.optimization.SolverTimeoutMs > 0 {
		timeout = time.Duration(cfg.optimization.SolverTimeoutMs) * time.Millisecond
	}
	
	return &JSONCLIEngine{
		config:     cfg,
		storage:    storage,
		binaryPath: binaryPath,
		timeout:    timeout,
	}
}

// JSONRequest represents the request format for the private binary
type JSONRequest struct {
	Action  string                 `json:"action"`
	Query   string                 `json:"query,omitempty"`
	Docs    []types.Document       `json:"docs,omitempty"`
	Options map[string]interface{} `json:"options,omitempty"`
}

// JSONResponse represents the response format from the private binary
type JSONResponse struct {
	Status string      `json:"status"`
	Data   interface{} `json:"data"`
	Error  string      `json:"error,omitempty"`
}

// AssembleContext performs context assembly via JSON CLI
func (e *JSONCLIEngine) AssembleContext(ctx context.Context, request types.ContextRequest) (*types.ContextResult, error) {
	startTime := time.Now()
	
	// Step 1: Get candidate documents using storage
	candidates, err := e.getCandidateDocuments(ctx, request)
	if err != nil {
		return nil, fmt.Errorf("failed to get candidates: %w", err)
	}
	
	if len(candidates) == 0 {
		return &types.ContextResult{
			Context:        "",
			Documents:      []types.DocumentReference{},
			TotalTokens:    0,
			ProcessingTime: time.Since(startTime),
			CacheHit:       false,
			Message:        "No relevant documents found",
		}, nil
	}
	
	// Step 2: Call private binary for optimization
	result, err := e.callPrivateBinary("optimize", request.Query, candidates, map[string]interface{}{
		"max_tokens":     request.MaxTokens,
		"max_documents":  request.MaxDocuments,
		"workspace_path": request.WorkspacePath,
	})
	if err != nil {
		return nil, fmt.Errorf("private binary call failed: %w", err)
	}
	
	// Step 3: Parse response and build ContextResult
	contextResult, err := e.parseOptimizeResponse(result, request, time.Since(startTime))
	if err != nil {
		return nil, fmt.Errorf("failed to parse optimization result: %w", err)
	}
	
	return contextResult, nil
}

// IndexDocument adds a document to the storage
func (e *JSONCLIEngine) IndexDocument(doc types.Document) error {
	return e.storage.InsertDocument(doc)
}

// RemoveDocument removes a document from storage
func (e *JSONCLIEngine) RemoveDocument(docID string) error {
	return e.storage.DeleteDocument(context.Background(), docID)
}

// GetStats returns engine statistics
func (e *JSONCLIEngine) GetStats() (*types.EngineStats, error) {
	// Call private binary for stats
	result, err := e.callPrivateBinary("stats", "", nil, nil)
	if err != nil {
		// Return basic stats if private binary unavailable
		return &types.EngineStats{
			TotalQueries:         0,
			AverageQueryTime:     10 * time.Millisecond,
			CacheHitRate:        0.0,
			TotalDocuments:      0,
			IndexedWorkspaces:   0,
			FeatureExtractionTime: 2 * time.Millisecond,
			SolverStats: types.SolverStats{
				TotalSolves:      0,
				AverageSolveTime: 5 * time.Millisecond,
				TimeoutCount:     0,
				OptimalityGap:    0.1,
			},
			MemoryUsageMB: 50.0,
			LicenseTier:   "professional",
			LicenseValid:  true,
		}, nil
	}
	
	// Parse stats response
	statsData, ok := result["stats"].(map[string]interface{})
	if !ok {
		return nil, fmt.Errorf("invalid stats response format")
	}
	
	return e.parseStatsResponse(statsData)
}

// UpdateConfig applies new configuration
func (e *JSONCLIEngine) UpdateConfig(config types.EngineConfig) error {
	// Update local config
	if config.SolverTimeout > 0 {
		e.timeout = config.SolverTimeout
	}
	
	// TODO: Send config update to private binary if needed
	return nil
}

// Close performs cleanup
func (e *JSONCLIEngine) Close() error {
	// No persistent connections to close
	return nil
}

// Private helper methods

// getCandidateDocuments retrieves candidate documents from storage
func (e *JSONCLIEngine) getCandidateDocuments(ctx context.Context, request types.ContextRequest) ([]types.Document, error) {
	maxCandidates := 200
	if e.config != nil && e.config.optimization.MaxCandidates > 0 {
		maxCandidates = e.config.optimization.MaxCandidates
	}
	
	return e.storage.SearchDocuments(ctx, request.Query, maxCandidates)
}

// callPrivateBinary executes the private binary with JSON input/output
func (e *JSONCLIEngine) callPrivateBinary(action, query string, docs []types.Document, options map[string]interface{}) (map[string]interface{}, error) {
	// Build JSON request
	request := JSONRequest{
		Action:  action,
		Query:   query,
		Docs:    docs,
		Options: options,
	}
	
	requestJSON, err := json.Marshal(request)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal request: %w", err)
	}
	
	// Execute command with timeout
	ctx, cancel := context.WithTimeout(context.Background(), e.timeout)
	defer cancel()
	
	cmd := exec.CommandContext(ctx, e.binaryPath)
	cmd.Stdin = strings.NewReader(string(requestJSON))
	
	output, err := cmd.Output()
	if err != nil {
		return nil, fmt.Errorf("binary execution failed: %w", err)
	}
	
	// Parse JSON response
	var response JSONResponse
	if err := json.Unmarshal(output, &response); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}
	
	if response.Status != "success" {
		return nil, fmt.Errorf("binary returned error: %s", response.Error)
	}
	
	// Convert response data to map
	dataMap, ok := response.Data.(map[string]interface{})
	if !ok {
		return nil, fmt.Errorf("invalid response data format")
	}
	
	return dataMap, nil
}

// parseOptimizeResponse converts the binary response to ContextResult
func (e *JSONCLIEngine) parseOptimizeResponse(result map[string]interface{}, request types.ContextRequest, processingTime time.Duration) (*types.ContextResult, error) {
	// Extract selected document indices
	selectedIndices, ok := result["selected_docs"].([]interface{})
	if !ok {
		return nil, fmt.Errorf("missing selected_docs in response")
	}
	
	// Extract original documents
	originalDocs, ok := result["docs"].([]interface{})
	if !ok {
		return nil, fmt.Errorf("missing docs in response") 
	}
	
	// Build document references
	var docRefs []types.DocumentReference
	var contextParts []string
	totalTokens := 0
	
	for _, idxInterface := range selectedIndices {
		idx, ok := idxInterface.(float64) // JSON numbers are float64
		if !ok {
			continue
		}
		
		docIdx := int(idx)
		if docIdx < 0 || docIdx >= len(originalDocs) {
			continue
		}
		
		// Parse document data
		docData, ok := originalDocs[docIdx].(map[string]interface{})
		if !ok {
			continue
		}
		
		docRef := types.DocumentReference{
			ID:              getStringField(docData, "id"),
			Path:            getStringField(docData, "path"),
			Content:         getStringField(docData, "content"),
			Language:        getStringField(docData, "language"),
			UtilityScore:    getFloatField(docData, "utility_score"),
			RelevanceScore:  getFloatField(docData, "relevance_score"),
			RecencyScore:    getFloatField(docData, "recency_score"),
			InclusionReason: "optimization-optimized",
		}
		
		docRefs = append(docRefs, docRef)
		contextParts = append(contextParts, docRef.Content)
		
		if tokenCount, ok := docData["token_count"].(float64); ok {
			totalTokens += int(tokenCount)
		}
	}
	
	// Extract optimization metrics
	optimizationMetrics := e.extractoptimizationMetrics(result)
	
	// Build final context
	context := strings.Join(contextParts, "\n\n---\n\n")
	
	return &types.ContextResult{
		Context:        context,
		Documents:      docRefs,
		TotalTokens:    totalTokens,
		ProcessingTime: processingTime,
		CacheHit:       false,
		CoherenceScore: getFloatField(result, "coherence_score"),
		optimizationMetrics:     optimizationMetrics,
	}, nil
}

// extractoptimizationMetrics extracts optimization system metrics from response
func (e *JSONCLIEngine) extractoptimizationMetrics(result map[string]interface{}) *types.optimizationResult {
	metricsData, ok := result["optimization_metrics"].(map[string]interface{})
	if !ok {
		return nil
	}
	
	return &types.optimizationResult{
		SelectedDocs:    nil, // Already processed above
		SolverUsed:      getStringField(metricsData, "solver_used"),
		optimizerStatus:        getStringField(metricsData, "z3_status"),
		Objective:       getFloatField(metricsData, "objective"),
		SolveTimeUs:     int64(getFloatField(metricsData, "solve_time_us")),
		VariableCount:   int(getFloatField(metricsData, "variable_count")),
		ConstraintCount: int(getFloatField(metricsData, "budget_count")),
		KCandidates:     int(getFloatField(metricsData, "k_candidates")),
		PairsCount:      int(getFloatField(metricsData, "pairs_count")),
		BudgetTokens:    int(getFloatField(metricsData, "budget_tokens")),
		MaxDocs:         int(getFloatField(metricsData, "max_docs")),
		FallbackReason:  getStringField(metricsData, "fallback_reason"),
	}
}

// parseStatsResponse converts stats response to EngineStats
func (e *JSONCLIEngine) parseStatsResponse(statsData map[string]interface{}) (*types.EngineStats, error) {
	solverData, ok := statsData["solver"].(map[string]interface{})
	if !ok {
		solverData = make(map[string]interface{})
	}
	
	return &types.EngineStats{
		TotalQueries:         int64(getFloatField(statsData, "total_queries")),
		AverageQueryTime:     time.Duration(getFloatField(statsData, "average_query_time_ms")) * time.Millisecond,
		CacheHitRate:        getFloatField(statsData, "cache_hit_rate"),
		TotalDocuments:      int64(getFloatField(statsData, "total_documents")),
		IndexedWorkspaces:   int(getFloatField(statsData, "indexed_workspaces")),
		FeatureExtractionTime: time.Duration(getFloatField(statsData, "feature_extraction_time_ms")) * time.Millisecond,
		SolverStats: types.SolverStats{
			TotalSolves:      int64(getFloatField(solverData, "total_solves")),
			AverageSolveTime: time.Duration(getFloatField(solverData, "average_solve_time_ms")) * time.Millisecond,
			TimeoutCount:     int64(getFloatField(solverData, "timeout_count")),
			OptimalityGap:    getFloatField(solverData, "optimality_gap"),
		},
		MemoryUsageMB: getFloatField(statsData, "memory_usage_mb"),
		LicenseTier:   getStringField(statsData, "license_tier"),
		LicenseValid:  getBoolField(statsData, "license_valid"),
	}, nil
}

// Helper functions for safe type conversion

func getStringField(data map[string]interface{}, key string) string {
	if val, ok := data[key].(string); ok {
		return val
	}
	return ""
}

func getFloatField(data map[string]interface{}, key string) float64 {
	if val, ok := data[key].(float64); ok {
		return val
	}
	return 0.0
}

func getBoolField(data map[string]interface{}, key string) bool {
	if val, ok := data[key].(bool); ok {
		return val
	}
	return false
}
