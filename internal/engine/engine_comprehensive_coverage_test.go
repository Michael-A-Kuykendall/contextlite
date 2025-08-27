package engine

import (
	"testing"
	"time"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// Test parseOptimizeResponse - currently at 0.0% coverage
func TestJSONCLIEngine_ParseOptimizeResponse_ZeroToPerfect(t *testing.T) {
	engine := &JSONCLIEngine{
		config: &config.Config{},
	}

	t.Run("ParseOptimizeResponse_ValidResponse", func(t *testing.T) {
		response := map[string]interface{}{
			"selected_docs": []interface{}{0.0, 1.0, 2.0},
			"docs": []interface{}{
				map[string]interface{}{
					"id":             "doc1",
					"path":           "/test/file1.go",
					"content":        "package test\nfunc Test1() {}",
					"language":       "go",
					"utility_score":  0.95,
					"relevance_score": 0.90,
					"recency_score":  0.85,
					"token_count":    25.0,
				},
				map[string]interface{}{
					"id":             "doc2",
					"path":           "/test/file2.go",
					"content":        "package test\nfunc Test2() {}",
					"language":       "go",
					"utility_score":  0.80,
					"relevance_score": 0.75,
					"recency_score":  0.70,
					"token_count":    20.0,
				},
				map[string]interface{}{
					"id":             "doc3",
					"path":           "/test/file3.go",
					"content":        "package test\nfunc Test3() {}",
					"language":       "go",
					"utility_score":  0.65,
					"relevance_score": 0.60,
					"recency_score":  0.55,
					"token_count":    15.0,
				},
			},
			"coherence_score": 0.88,
			"smt_metrics": map[string]interface{}{
				"solver_used":      "Z3",
				"z3_status":        "SAT",
				"objective":        45.5,
				"solve_time_us":    1200.0,
				"variable_count":   25.0,
				"constraint_count": 30.0,
				"k_candidates":     5.0,
				"pairs_count":      10.0,
				"budget_tokens":    8000.0,
				"max_docs":         10.0,
				"fallback_reason":  "",
			},
		}

		request := types.ContextRequest{
			Query:         "test function",
			MaxTokens:     8000,
			MaxDocuments:  5,
		}

		result, err := engine.parseOptimizeResponse(response, request, 150*time.Millisecond)
		if err != nil {
			t.Fatalf("parseOptimizeResponse failed: %v", err)
		}

		if result == nil {
			t.Fatal("Expected non-nil result")
		}

		// Verify documents
		if len(result.Documents) != 3 {
			t.Errorf("Expected 3 documents, got %d", len(result.Documents))
		}

		// Verify first document
		doc1 := result.Documents[0]
		if doc1.ID != "doc1" {
			t.Errorf("Expected doc1 ID, got %s", doc1.ID)
		}
		if doc1.Path != "/test/file1.go" {
			t.Errorf("Expected /test/file1.go path, got %s", doc1.Path)
		}
		if doc1.UtilityScore != 0.95 {
			t.Errorf("Expected utility score 0.95, got %f", doc1.UtilityScore)
		}
		if doc1.InclusionReason != "smt-optimized" {
			t.Errorf("Expected 'smt-optimized' reason, got %s", doc1.InclusionReason)
		}

		// Verify total tokens
		if result.TotalTokens != 60 { // 25 + 20 + 15
			t.Errorf("Expected total tokens 60, got %d", result.TotalTokens)
		}

		// Verify coherence score
		if result.CoherenceScore != 0.88 {
			t.Errorf("Expected coherence score 0.88, got %f", result.CoherenceScore)
		}

		// Verify context assembly
		if result.Context == "" {
			t.Error("Expected non-empty context")
		}

		// Verify SMT metrics
		if result.SMTMetrics == nil {
			t.Error("Expected SMT metrics")
		} else {
			if result.SMTMetrics.SolverUsed != "Z3" {
				t.Errorf("Expected Z3 solver, got %s", result.SMTMetrics.SolverUsed)
			}
			if result.SMTMetrics.VariableCount != 25 {
				t.Errorf("Expected 25 variables, got %d", result.SMTMetrics.VariableCount)
			}
		}

		// Verify processing time
		if result.ProcessingTime != 150*time.Millisecond {
			t.Errorf("Expected processing time 150ms, got %v", result.ProcessingTime)
		}
	})

	t.Run("ParseOptimizeResponse_MissingSelectedDocs", func(t *testing.T) {
		response := map[string]interface{}{
			"docs": []interface{}{},
		}

		request := types.ContextRequest{}

		_, err := engine.parseOptimizeResponse(response, request, 100*time.Millisecond)
		if err == nil {
			t.Error("Expected error for missing selected_docs")
		}
		if err.Error() != "missing selected_docs in response" {
			t.Errorf("Expected specific error message, got: %v", err)
		}
	})

	t.Run("ParseOptimizeResponse_MissingDocs", func(t *testing.T) {
		response := map[string]interface{}{
			"selected_docs": []interface{}{0.0},
		}

		request := types.ContextRequest{}

		_, err := engine.parseOptimizeResponse(response, request, 100*time.Millisecond)
		if err == nil {
			t.Error("Expected error for missing docs")
		}
		if err.Error() != "missing docs in response" {
			t.Errorf("Expected specific error message, got: %v", err)
		}
	})

	t.Run("ParseOptimizeResponse_InvalidDocumentIndex", func(t *testing.T) {
		response := map[string]interface{}{
			"selected_docs": []interface{}{99.0}, // Out of bounds index
			"docs": []interface{}{
				map[string]interface{}{
					"id":      "doc1",
					"path":    "/test/file1.go",
					"content": "test content",
				},
			},
		}

		request := types.ContextRequest{}

		result, err := engine.parseOptimizeResponse(response, request, 100*time.Millisecond)
		if err != nil {
			t.Fatalf("Unexpected error: %v", err)
		}

		// Should skip invalid indices and return empty documents
		if len(result.Documents) != 0 {
			t.Errorf("Expected 0 documents with invalid index, got %d", len(result.Documents))
		}
	})

	t.Run("ParseOptimizeResponse_InvalidDocumentData", func(t *testing.T) {
		response := map[string]interface{}{
			"selected_docs": []interface{}{0.0},
			"docs": []interface{}{
				"invalid_document_data", // Not a map
			},
		}

		request := types.ContextRequest{}

		result, err := engine.parseOptimizeResponse(response, request, 100*time.Millisecond)
		if err != nil {
			t.Fatalf("Unexpected error: %v", err)
		}

		// Should skip invalid document data
		if len(result.Documents) != 0 {
			t.Errorf("Expected 0 documents with invalid data, got %d", len(result.Documents))
		}
	})

	t.Run("ParseOptimizeResponse_NoSMTMetrics", func(t *testing.T) {
		response := map[string]interface{}{
			"selected_docs": []interface{}{0.0},
			"docs": []interface{}{
				map[string]interface{}{
					"id":      "doc1",
					"path":    "/test/file1.go",
					"content": "test content",
				},
			},
			// No smt_metrics
		}

		request := types.ContextRequest{}

		result, err := engine.parseOptimizeResponse(response, request, 100*time.Millisecond)
		if err != nil {
			t.Fatalf("Unexpected error: %v", err)
		}

		// Should handle missing SMT metrics gracefully
		if result.SMTMetrics != nil {
			t.Error("Expected nil SMT metrics when not provided")
		}
	})
}

// Test extractSMTMetrics - currently at 0.0% coverage
func TestJSONCLIEngine_ExtractSMTMetrics_ZeroToPerfect(t *testing.T) {
	engine := &JSONCLIEngine{}

	t.Run("ExtractSMTMetrics_ValidMetrics", func(t *testing.T) {
		response := map[string]interface{}{
			"smt_metrics": map[string]interface{}{
				"solver_used":      "Z3",
				"z3_status":        "SAT",
				"objective":        42.5,
				"solve_time_us":    1500.0,
				"variable_count":   30.0,
				"constraint_count": 45.0,
				"k_candidates":     8.0,
				"pairs_count":      15.0,
				"budget_tokens":    4000.0,
				"max_docs":         20.0,
				"fallback_reason":  "timeout",
			},
		}

		metrics := engine.extractSMTMetrics(response)
		if metrics == nil {
			t.Fatal("Expected non-nil SMT metrics")
		}

		if metrics.SolverUsed != "Z3" {
			t.Errorf("Expected solver Z3, got %s", metrics.SolverUsed)
		}
		if metrics.Z3Status != "SAT" {
			t.Errorf("Expected status SAT, got %s", metrics.Z3Status)
		}
		if metrics.Objective != 42.5 {
			t.Errorf("Expected objective 42.5, got %f", metrics.Objective)
		}
		if metrics.SolveTimeUs != 1500 {
			t.Errorf("Expected solve time 1500us, got %d", metrics.SolveTimeUs)
		}
		if metrics.VariableCount != 30 {
			t.Errorf("Expected 30 variables, got %d", metrics.VariableCount)
		}
		if metrics.ConstraintCount != 45 {
			t.Errorf("Expected 45 constraints, got %d", metrics.ConstraintCount)
		}
		if metrics.KCandidates != 8 {
			t.Errorf("Expected 8 k_candidates, got %d", metrics.KCandidates)
		}
		if metrics.PairsCount != 15 {
			t.Errorf("Expected 15 pairs, got %d", metrics.PairsCount)
		}
		if metrics.BudgetTokens != 4000 {
			t.Errorf("Expected 4000 budget tokens, got %d", metrics.BudgetTokens)
		}
		if metrics.MaxDocs != 20 {
			t.Errorf("Expected 20 max docs, got %d", metrics.MaxDocs)
		}
		if metrics.FallbackReason != "timeout" {
			t.Errorf("Expected 'timeout' fallback reason, got %s", metrics.FallbackReason)
		}
	})

	t.Run("ExtractSMTMetrics_MissingMetrics", func(t *testing.T) {
		response := map[string]interface{}{
			"other_data": "value",
		}

		metrics := engine.extractSMTMetrics(response)
		if metrics != nil {
			t.Error("Expected nil metrics when smt_metrics missing")
		}
	})

	t.Run("ExtractSMTMetrics_InvalidMetricsType", func(t *testing.T) {
		response := map[string]interface{}{
			"smt_metrics": "not_a_map",
		}

		metrics := engine.extractSMTMetrics(response)
		if metrics != nil {
			t.Error("Expected nil metrics when smt_metrics is not a map")
		}
	})

	t.Run("ExtractSMTMetrics_PartialMetrics", func(t *testing.T) {
		response := map[string]interface{}{
			"smt_metrics": map[string]interface{}{
				"solver_used": "Z3",
				// Missing other fields - should use defaults
			},
		}

		metrics := engine.extractSMTMetrics(response)
		if metrics == nil {
			t.Fatal("Expected non-nil metrics")
		}

		if metrics.SolverUsed != "Z3" {
			t.Errorf("Expected solver Z3, got %s", metrics.SolverUsed)
		}
		if metrics.VariableCount != 0 {
			t.Errorf("Expected default 0 variable count, got %d", metrics.VariableCount)
		}
		if metrics.Objective != 0.0 {
			t.Errorf("Expected default 0.0 objective, got %f", metrics.Objective)
		}
	})
}

// Test parseStatsResponse - currently at 0.0% coverage  
func TestJSONCLIEngine_ParseStatsResponse_ZeroToPerfect(t *testing.T) {
	engine := &JSONCLIEngine{}

	t.Run("ParseStatsResponse_CompleteStats", func(t *testing.T) {
		statsData := map[string]interface{}{
			"total_queries":              100.0,
			"average_query_time_ms":      250.5,
			"cache_hit_rate":             0.85,
			"total_documents":            5000.0,
			"indexed_workspaces":         12.0,
			"feature_extraction_time_ms": 45.2,
			"memory_usage_mb":            128.5,
			"license_tier":               "Professional",
			"license_valid":              true,
			"solver": map[string]interface{}{
				"total_solves":         75.0,
				"average_solve_time_ms": 180.3,
				"timeout_count":        3.0,
				"optimality_gap":       0.02,
			},
		}

		stats, err := engine.parseStatsResponse(statsData)
		if err != nil {
			t.Fatalf("parseStatsResponse failed: %v", err)
		}

		if stats.TotalQueries != 100 {
			t.Errorf("Expected 100 total queries, got %d", stats.TotalQueries)
		}
		// Time durations truncate to whole milliseconds in Go
		if stats.AverageQueryTime != 250*time.Millisecond {
			t.Errorf("Expected 250ms average query time, got %v", stats.AverageQueryTime)
		}
		if stats.CacheHitRate != 0.85 {
			t.Errorf("Expected 0.85 cache hit rate, got %f", stats.CacheHitRate)
		}
		if stats.TotalDocuments != 5000 {
			t.Errorf("Expected 5000 total documents, got %d", stats.TotalDocuments)
		}
		if stats.IndexedWorkspaces != 12 {
			t.Errorf("Expected 12 indexed workspaces, got %d", stats.IndexedWorkspaces)
		}
		if stats.FeatureExtractionTime != 45*time.Millisecond {
			t.Errorf("Expected 45ms feature extraction time, got %v", stats.FeatureExtractionTime)
		}
		if stats.MemoryUsageMB != 128.5 {
			t.Errorf("Expected 128.5MB memory usage, got %f", stats.MemoryUsageMB)
		}
		if stats.LicenseTier != "Professional" {
			t.Errorf("Expected Professional license tier, got %s", stats.LicenseTier)
		}
		if !stats.LicenseValid {
			t.Error("Expected license to be valid")
		}

		// Verify solver stats
		if stats.SolverStats.TotalSolves != 75 {
			t.Errorf("Expected 75 total solves, got %d", stats.SolverStats.TotalSolves)
		}
		if stats.SolverStats.AverageSolveTime != 180*time.Millisecond {
			t.Errorf("Expected 180ms average solve time, got %v", stats.SolverStats.AverageSolveTime)
		}
		if stats.SolverStats.TimeoutCount != 3 {
			t.Errorf("Expected 3 timeouts, got %d", stats.SolverStats.TimeoutCount)
		}
		if stats.SolverStats.OptimalityGap != 0.02 {
			t.Errorf("Expected 0.02 optimality gap, got %f", stats.SolverStats.OptimalityGap)
		}
	})

	t.Run("ParseStatsResponse_MissingSolverData", func(t *testing.T) {
		statsData := map[string]interface{}{
			"total_queries":     50.0,
			"cache_hit_rate":    0.70,
			"total_documents":   2000.0,
			"license_tier":      "Basic",
			"license_valid":     false,
			// No solver data
		}

		stats, err := engine.parseStatsResponse(statsData)
		if err != nil {
			t.Fatalf("parseStatsResponse failed: %v", err)
		}

		// Should handle missing solver data gracefully
		if stats.SolverStats.TotalSolves != 0 {
			t.Errorf("Expected 0 total solves when solver data missing, got %d", stats.SolverStats.TotalSolves)
		}
		if stats.LicenseTier != "Basic" {
			t.Errorf("Expected Basic license tier, got %s", stats.LicenseTier)
		}
		if stats.LicenseValid {
			t.Error("Expected license to be invalid")
		}
	})

	t.Run("ParseStatsResponse_InvalidSolverData", func(t *testing.T) {
		statsData := map[string]interface{}{
			"total_queries":  25.0,
			"total_documents": 1000.0,
			"solver":         "not_a_map", // Invalid solver data
		}

		stats, err := engine.parseStatsResponse(statsData)
		if err != nil {
			t.Fatalf("parseStatsResponse failed: %v", err)
		}

		// Should use empty solver data when invalid
		if stats.SolverStats.TotalSolves != 0 {
			t.Errorf("Expected 0 total solves with invalid solver data, got %d", stats.SolverStats.TotalSolves)
		}
	})

	t.Run("ParseStatsResponse_MinimalData", func(t *testing.T) {
		statsData := map[string]interface{}{
			// Only basic data provided
		}

		stats, err := engine.parseStatsResponse(statsData)
		if err != nil {
			t.Fatalf("parseStatsResponse failed: %v", err)
		}

		// Should handle empty data gracefully with defaults
		if stats.TotalQueries != 0 {
			t.Errorf("Expected 0 total queries with minimal data, got %d", stats.TotalQueries)
		}
		if stats.LicenseTier != "" {
			t.Errorf("Expected empty license tier with minimal data, got %s", stats.LicenseTier)
		}
		if stats.LicenseValid {
			t.Error("Expected license to be invalid with minimal data")
		}
	})
}

// Test helper functions coverage improvements
func TestJSONCLIEngine_HelperFunctions_ImproveCoverage(t *testing.T) {
	t.Run("GetStringField_ValidString", func(t *testing.T) {
		data := map[string]interface{}{
			"test_key": "test_value",
		}
		
		result := getStringField(data, "test_key")
		if result != "test_value" {
			t.Errorf("Expected 'test_value', got %s", result)
		}
	})

	t.Run("GetStringField_MissingKey", func(t *testing.T) {
		data := map[string]interface{}{}
		
		result := getStringField(data, "missing_key")
		if result != "" {
			t.Errorf("Expected empty string for missing key, got %s", result)
		}
	})

	t.Run("GetStringField_WrongType", func(t *testing.T) {
		data := map[string]interface{}{
			"test_key": 123, // Not a string
		}
		
		result := getStringField(data, "test_key")
		if result != "" {
			t.Errorf("Expected empty string for wrong type, got %s", result)
		}
	})

	t.Run("GetFloatField_ValidFloat", func(t *testing.T) {
		data := map[string]interface{}{
			"test_key": 42.5,
		}
		
		result := getFloatField(data, "test_key")
		if result != 42.5 {
			t.Errorf("Expected 42.5, got %f", result)
		}
	})

	t.Run("GetFloatField_MissingKey", func(t *testing.T) {
		data := map[string]interface{}{}
		
		result := getFloatField(data, "missing_key")
		if result != 0.0 {
			t.Errorf("Expected 0.0 for missing key, got %f", result)
		}
	})

	t.Run("GetFloatField_WrongType", func(t *testing.T) {
		data := map[string]interface{}{
			"test_key": "not_a_float",
		}
		
		result := getFloatField(data, "test_key")
		if result != 0.0 {
			t.Errorf("Expected 0.0 for wrong type, got %f", result)
		}
	})

	t.Run("GetBoolField_ValidBool", func(t *testing.T) {
		data := map[string]interface{}{
			"test_true":  true,
			"test_false": false,
		}
		
		result1 := getBoolField(data, "test_true")
		if !result1 {
			t.Error("Expected true")
		}
		
		result2 := getBoolField(data, "test_false")
		if result2 {
			t.Error("Expected false")
		}
	})

	t.Run("GetBoolField_MissingKey", func(t *testing.T) {
		data := map[string]interface{}{}
		
		result := getBoolField(data, "missing_key")
		if result {
			t.Error("Expected false for missing key")
		}
	})

	t.Run("GetBoolField_WrongType", func(t *testing.T) {
		data := map[string]interface{}{
			"test_key": "not_a_bool",
		}
		
		result := getBoolField(data, "test_key")
		if result {
			t.Error("Expected false for wrong type")
		}
	})
}

// Test additional engine functionality improvements
func TestEngineInfo_ImproveCoverage(t *testing.T) {
	t.Run("GetEngineInfo_PrivateAvailable", func(t *testing.T) {
		// Create a simple engine for testing
		cfg := &config.Config{}
		engine := &CoreEngine{config: cfg}
		
		info := GetEngineInfo(engine)
		
		// Should return engine info without error
		if info == nil {
			t.Error("Expected non-nil engine info")
		}
		
		// Check that info is returned as map
		if len(info) == 0 {
			t.Error("Expected non-empty engine info map")
		}
	})
}

// Test loader functionality improvements
func TestEngine_LoaderImprovements(t *testing.T) {
	t.Run("PrivateEngineAvailable_Check", func(t *testing.T) {
		// Should not crash and return a boolean
		available := PrivateEngineAvailable()
		t.Logf("Private engine available: %v", available)
		// Don't assert specific value since it depends on build environment
	})

	t.Run("FileExists_ValidPath", func(t *testing.T) {
		// Test with a file that should exist (this test file)
		exists := fileExists("json_cli_100_percent_test.go")
		if !exists {
			t.Error("Expected test file to exist")
		}
	})

	t.Run("FileExists_InvalidPath", func(t *testing.T) {
		// Test with a file that definitely doesn't exist
		exists := fileExists("/definitely/does/not/exist/nowhere.txt")
		if exists {
			t.Error("Expected non-existent file to return false")
		}
	})
}