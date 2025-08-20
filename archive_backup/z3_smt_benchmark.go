package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"time"
)

const (
	baseURL   = "http://127.0.0.1:8082"
	authToken = "contextlite-dev-token-2025"
)

type QueryRequest struct {
	Query      string `json:"query"`
	MaxResults int    `json:"max_results,omitempty"`
}

type optimizationMetrics struct {
	SolverUsed     string  `json:"solver_used"`
	optimizerStatus       string  `json:"z3_status"`
	Objective      int     `json:"objective"`
	SolveTimeUs    int     `json:"solve_time_us"`
	SolveTimeMs    float64 `json:"solve_time_ms"`
	optimizationWallUs      int     `json:"optimization_wall_us"`
	optimizationWallMs      float64 `json:"optimization_wall_ms"`
	VariableCount  int     `json:"variable_count"`
	ConstraintCount int    `json:"budget_count"`
	KCandidates    int     `json:"K_candidates"`
	PairsCount     int     `json:"pairs_count"`
	BudgetTokens   int     `json:"budget_tokens"`
	MaxDocs        int     `json:"max_docs"`
}

type ContextResponse struct {
	Query        string      `json:"query"`
	Documents    []Document  `json:"documents"`
	TotalDocs    int         `json:"total_documents"`
	TotalTokens  int         `json:"total_tokens"`
	Coherence    float64     `json:"coherence_score"`
	optimizationMetrics   optimizationMetrics  `json:"optimization_metrics"`
	Timings      interface{} `json:"timings"`
	CacheHit     bool        `json:"cache_hit"`
}

type Document struct {
	ID            string  `json:"id"`
	Path          string  `json:"path"`
	Content       string  `json:"content"`
	Language      string  `json:"language"`
	UtilityScore  float64 `json:"utility_score"`
	RelevanceScore float64 `json:"relevance_score"`
	RecencyScore  float64 `json:"recency_score"`
	Reason        string  `json:"inclusion_reason"`
}

type StorageInfo struct {
	DatabaseSize string `json:"database_size"`
	IndexSize    string `json:"index_size"`
	TotalDocs    int    `json:"total_documents"`
	AvgDocSize   string `json:"avg_document_size"`
	LastUpdate   int64  `json:"last_update"`
}

func makeRequest(method, endpoint string, body interface{}) ([]byte, error) {
	var reqBody *bytes.Buffer
	if body != nil {
		jsonData, err := json.Marshal(body)
		if err != nil {
			return nil, err
		}
		reqBody = bytes.NewBuffer(jsonData)
	}

	var req *http.Request
	var err error
	if reqBody != nil {
		req, err = http.NewRequest(method, baseURL+endpoint, reqBody)
		req.Header.Set("Content-Type", "application/json")
	} else {
		req, err = http.NewRequest(method, baseURL+endpoint, nil)
	}
	if err != nil {
		return nil, err
	}

	req.Header.Set("Authorization", "Bearer "+authToken)

	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	respBody := make([]byte, 0)
	buf := make([]byte, 1024)
	for {
		n, err := resp.Body.Read(buf)
		if n > 0 {
			respBody = append(respBody, buf[:n]...)
		}
		if err != nil {
			break
		}
	}

	return respBody, nil
}

func getStorageInfo() (*StorageInfo, error) {
	data, err := makeRequest("GET", "/api/v1/storage/info", nil)
	if err != nil {
		return nil, err
	}

	var info StorageInfo
	err = json.Unmarshal(data, &info)
	return &info, err
}

func runQuery(query string, maxResults int) (*ContextResponse, time.Duration, error) {
	start := time.Now()
	
	req := QueryRequest{
		Query:      query,
		MaxResults: maxResults,
	}

	data, err := makeRequest("POST", "/api/v1/context/assemble", req)
	duration := time.Since(start)
	
	if err != nil {
		return nil, duration, err
	}

	var response ContextResponse
	err = json.Unmarshal(data, &response)
	return &response, duration, err
}

func main() {
	fmt.Println("=== ContextLite optimizer optimization Optimization Benchmark ===")
	
	// Check initial state
	info, err := getStorageInfo()
	if err != nil {
		log.Printf("Warning: Could not get storage info: %v", err)
	} else {
		fmt.Printf("Database: %d documents, %s size\n", info.TotalDocs, info.DatabaseSize)
	}

	// Comprehensive test queries
	testQueries := []struct {
		query      string
		maxResults int
	}{
		{"contextlite configuration settings", 5},
		{"optimizer optimization system optimization", 3},
		{"database indexing and storage", 7},
		{"Go programming patterns", 4},
		{"authentication middleware implementation", 6},
		{"JSON API endpoints design", 5},
		{"concurrent processing algorithms", 8},
		{"document similarity scoring", 4},
		{"cache management strategies", 6},
		{"performance optimization techniques", 10},
	}

	fmt.Printf("\n=== Running %d Test Queries ===\n", len(testQueries))
	
	var totaloptimizerTime time.Duration
	var totalQueries int
	var z3Solves int
	var cacheMisses int
	var satisfiableResults int
	
	for i, test := range testQueries {
		fmt.Printf("\nQuery %d: %s (max_results=%d)\n", i+1, test.query, test.maxResults)
		
		response, duration, err := runQuery(test.query, test.maxResults)
		if err != nil {
			fmt.Printf("Error: %v\n", err)
			continue
		}
		
		totalQueries++
		
		if !response.CacheHit {
			cacheMisses++
		}
		
		optimization := response.optimizationMetrics
		if optimization.SolverUsed == "z3opt" {
			z3Solves++
			totaloptimizerTime += time.Duration(optimization.optimizationWallUs) * time.Microsecond
			
			if optimization.optimizerStatus == "sat" {
				satisfiableResults++
			}
		}
		
		fmt.Printf("Response time: %v\n", duration)
		fmt.Printf("Documents found: %d (of %d total)\n", len(response.Documents), response.TotalDocs)
		fmt.Printf("Coherence score: %.3f\n", response.Coherence)
		fmt.Printf("Cache hit: %v\n", response.CacheHit)
		
		fmt.Printf("optimization Metrics:\n")
		fmt.Printf("  Solver: %s, Status: %s\n", optimization.SolverUsed, optimization.optimizerStatus)
		fmt.Printf("  Solve time: %.2f ms (Wall: %.2f ms)\n", optimization.SolveTimeMs, optimization.optimizationWallMs)
		fmt.Printf("  Variables: %d, Constraints: %d\n", optimization.VariableCount, optimization.ConstraintCount)
		fmt.Printf("  Candidates: %d, Pairs: %d\n", optimization.KCandidates, optimization.PairsCount)
		fmt.Printf("  Objective value: %d\n", optimization.Objective)
		
		if len(response.Documents) > 0 {
			fmt.Printf("Top document: %s (utility: %.3f)\n", 
				response.Documents[0].ID, response.Documents[0].UtilityScore)
		}
		
		// Brief pause to avoid overwhelming the server
		time.Sleep(100 * time.Millisecond)
	}

	fmt.Printf("\n=== Benchmark Results Summary ===\n")
	fmt.Printf("Total queries: %d\n", totalQueries)
	fmt.Printf("optimizer optimization solves: %d\n", z3Solves)
	fmt.Printf("Cache misses: %d\n", cacheMisses)
	fmt.Printf("Satisfiable results: %d\n", satisfiableResults)
	
	if z3Solves > 0 {
		avgoptimizerTime := totaloptimizerTime / time.Duration(z3Solves)
		fmt.Printf("Average optimizer solve time: %v\n", avgoptimizerTime)
		fmt.Printf("Total optimizer computation: %v\n", totaloptimizerTime)
		
		satisfiabilityRate := float64(satisfiableResults) / float64(z3Solves) * 100
		fmt.Printf("optimizer satisfiability rate: %.1f%%\n", satisfiabilityRate)
	}
	
	// Final storage check
	finalInfo, err := getStorageInfo()
	if err == nil {
		fmt.Printf("\nFinal database: %d documents, %s size\n", 
			finalInfo.TotalDocs, finalInfo.DatabaseSize)
	}
	
	fmt.Printf("\n=== optimizer optimization Benchmark Complete ===\n")
}
