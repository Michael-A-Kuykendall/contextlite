package bench

import (
	"bytes"
	"encoding/json"
	"net/http"
	"testing"
	"time"

	"contextlite/pkg/types"
)

// BenchmarkAssemble benchmarks the HTTP context assembly endpoint
func BenchmarkAssemble(b *testing.B) {
	// Disable cache for accurate timing measurements
	body := []byte(`{
		"query": "authentication security patterns",
		"max_tokens": 4000,
		"max_documents": 4,
		"use_cache": false,
		"use_optimization": true,
		"workspace_path": "/test/workspace"
	}`)
	
	client := &http.Client{
		Timeout: 10 * time.Second,
	}
	url := "http://127.0.0.1:8080/api/v1/context/assemble"
	
	// Warm-up request (not measured)
	req, _ := http.NewRequest("POST", url, bytes.NewReader(body))
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer contextlite-dev-token-2025")
	resp, err := client.Do(req)
	if err == nil {
		resp.Body.Close()
	}
	
	// Reset benchmark timer
	b.ResetTimer()
	
	// Benchmark loop
	for i := 0; i < b.N; i++ {
		req, _ := http.NewRequest("POST", url, bytes.NewReader(body))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer contextlite-dev-token-2025")
		
		resp, err := client.Do(req)
		if err != nil {
			b.Fatalf("Request failed: %v", err)
		}
		
		// Optionally parse response to check timing values
		var result types.QueryResult
		if err := json.NewDecoder(resp.Body).Decode(&result); err == nil {
			// Log microsecond timings for verification
			if i == 0 { // Only log first iteration to avoid spam
				b.Logf("Timings (μs): FTS=%d, Features=%d, optimization=%d, Total=%d", 
					result.Timings.FTSHarvestUs,
					result.Timings.FeatureBuildUs,
					result.Timings.optimizationSolverUs,
					result.Timings.TotalUs)
				b.Logf("Timings (ms): FTS=%.3f, Features=%.3f, optimization=%.3f, Total=%.3f", 
					result.Timings.FTSHarvestMs,
					result.Timings.FeatureBuildMs,
					result.Timings.optimizationSolverMs,
					result.Timings.TotalMs)
			}
		}
		
		resp.Body.Close()
	}
}

// BenchmarkAssemblyComponents benchmarks individual pipeline components
func BenchmarkAssemblyComponents(b *testing.B) {
	tests := []struct {
		name string
		body string
	}{
		{
			name: "CachedQuery",
			body: `{"query":"auth cached","max_tokens":4000,"use_cache":true,"use_optimization":true}`,
		},
		{
			name: "ColdQuery",
			body: `{"query":"auth cold unique","max_tokens":4000,"use_cache":false,"use_optimization":true}`,
		},
		{
			name: "MMRFallback",
			body: `{"query":"auth fallback","max_tokens":4000,"use_cache":false,"use_optimization":false}`,
		},
	}
	
	client := &http.Client{Timeout: 10 * time.Second}
	url := "http://127.0.0.1:8080/api/v1/context/assemble"
	
	for _, tt := range tests {
		b.Run(tt.name, func(b *testing.B) {
			body := []byte(tt.body)
			
			// Warm-up
			req, _ := http.NewRequest("POST", url, bytes.NewReader(body))
			req.Header.Set("Content-Type", "application/json")
			req.Header.Set("Authorization", "Bearer contextlite-dev-token-2025")
			resp, err := client.Do(req)
			if err == nil {
				resp.Body.Close()
			}
			
			b.ResetTimer()
			
			for i := 0; i < b.N; i++ {
				req, _ := http.NewRequest("POST", url, bytes.NewReader(body))
				req.Header.Set("Content-Type", "application/json")
				req.Header.Set("Authorization", "Bearer contextlite-dev-token-2025")
				
				resp, err := client.Do(req)
				if err != nil {
					b.Fatalf("Request failed: %v", err)
				}
				resp.Body.Close()
			}
		})
	}
}

// TestTimingPrecision validates that timing measurements are non-zero and reasonable
func TestTimingPrecision(t *testing.T) {
	body := []byte(`{
		"query": "timing precision test",
		"max_tokens": 4000,
		"max_documents": 3,
		"use_cache": false,
		"use_optimization": true
	}`)
	
	client := &http.Client{Timeout: 10 * time.Second}
	url := "http://127.0.0.1:8080/api/v1/context/assemble"
	
	req, _ := http.NewRequest("POST", url, bytes.NewReader(body))
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer contextlite-dev-token-2025")
	
	resp, err := client.Do(req)
	if err != nil {
		t.Fatalf("Request failed: %v", err)
	}
	defer resp.Body.Close()
	
	var result types.QueryResult
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		t.Fatalf("Failed to decode response: %v", err)
	}
	
	// Validate that timings are non-zero and reasonable
	if result.Timings.TotalUs <= 0 {
		t.Errorf("Total timing should be > 0, got %d μs", result.Timings.TotalUs)
	}
	
	if result.Timings.FTSHarvestUs <= 0 {
		t.Errorf("FTS harvest timing should be > 0, got %d μs", result.Timings.FTSHarvestUs)
	}
	
	if result.Timings.FeatureBuildUs <= 0 {
		t.Errorf("Feature build timing should be > 0, got %d μs", result.Timings.FeatureBuildUs)
	}
	
	// optimization timing might be 0 for fallback cases, but should be consistent with solver used
	if result.optimizationMetrics.SolverUsed == "z3opt" && result.Timings.optimizationSolverUs <= 0 {
		t.Errorf("optimization engine timing should be > 0 when optimizer is used, got %d μs", result.Timings.optimizationSolverUs)
	}
	
	// Validate float millisecond conversions
	expectedFTSMs := float64(result.Timings.FTSHarvestUs) / 1000.0
	if abs(result.Timings.FTSHarvestMs-expectedFTSMs) > 0.001 {
		t.Errorf("FTS timing conversion mismatch: %f ms != %f ms", result.Timings.FTSHarvestMs, expectedFTSMs)
	}
	
	t.Logf("Timing validation passed:")
	t.Logf("  FTS Harvest: %d μs (%.3f ms)", result.Timings.FTSHarvestUs, result.Timings.FTSHarvestMs)
	t.Logf("  Feature Build: %d μs (%.3f ms)", result.Timings.FeatureBuildUs, result.Timings.FeatureBuildMs)
	t.Logf("  optimization Solver: %d μs (%.3f ms)", result.Timings.optimizationSolverUs, result.Timings.optimizationSolverMs)
	t.Logf("  optimization Wall: %d μs (%.3f ms)", result.Timings.optimizationWallUs, result.Timings.optimizationWallMs)
	t.Logf("  Total: %d μs (%.3f ms)", result.Timings.TotalUs, result.Timings.TotalMs)
	t.Logf("  Solver Used: %s", result.optimizationMetrics.SolverUsed)
}

func abs(x float64) float64 {
	if x < 0 {
		return -x
	}
	return x
}
