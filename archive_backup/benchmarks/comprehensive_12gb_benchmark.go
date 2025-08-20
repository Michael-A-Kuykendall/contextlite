package main

import (
	"fmt"
	"io/fs"
	"log"
	"os"
	"path/filepath"
	"strings"
	"time"
	"encoding/json"
	"net/http"
	"bytes"
)

type DocumentRequest struct {
	ID       string            `json:"id"`
	Content  string            `json:"content"`
	Path     string            `json:"path,omitempty"`
	Language string            `json:"language,omitempty"`
	Metadata map[string]string `json:"metadata,omitempty"`
}

type QueryRequest struct {
	Query string `json:"query"`
	MaxResults int `json:"max_results,omitempty"`
}

const (
	baseURL = "http://127.0.0.1:8082"
	authToken = "contextlite-dev-token-2025"
	batchSize = 100
	reposRoot = "C:\\Users\\micha\\repos"
)

var includeExtensions = map[string]bool{
	".go": true, ".js": true, ".ts": true, ".py": true, ".java": true,
	".cpp": true, ".c": true, ".h": true, ".cs": true, ".php": true,
	".rb": true, ".rs": true, ".kt": true, ".swift": true,
	".md": true, ".txt": true, ".json": true, ".yaml": true, ".yml": true,
}

var excludePaths = []string{
	"node_modules", ".git", "build", "dist", "target", "bin", "obj", ".vscode",
	"__pycache__", ".pytest_cache", "coverage", ".nyc_output", "logs",
	".idea", ".vs", "tmp", "temp", "cache", ".cache",
}

func shouldIncludeFile(path string) bool {
	// Check extension
	ext := strings.ToLower(filepath.Ext(path))
	if !includeExtensions[ext] {
		return false
	}
	
	// Check excluded paths
	pathParts := strings.Split(filepath.ToSlash(path), "/")
	for _, part := range pathParts {
		for _, exclude := range excludePaths {
			if strings.Contains(strings.ToLower(part), exclude) {
				return false
			}
		}
	}
	
	return true
}

func makeRequest(method, endpoint string, body interface{}) (*http.Response, error) {
	var reqBody *bytes.Reader
	if body != nil {
		jsonData, err := json.Marshal(body)
		if err != nil {
			return nil, err
		}
		reqBody = bytes.NewReader(jsonData)
	}
	
	var req *http.Request
	var err error
	if reqBody != nil {
		req, err = http.NewRequest(method, baseURL+endpoint, reqBody)
	} else {
		req, err = http.NewRequest(method, baseURL+endpoint, nil)
	}
	if err != nil {
		return nil, err
	}
	
	req.Header.Set("Authorization", "Bearer "+authToken)
	if body != nil {
		req.Header.Set("Content-Type", "application/json")
	}
	
	client := &http.Client{Timeout: 30 * time.Second}
	return client.Do(req)
}

func indexFile(filePath string) error {
	content, err := os.ReadFile(filePath)
	if err != nil {
		return err
	}
	
	// Skip very large files (>1MB)
	if len(content) > 1024*1024 {
		return nil
	}
	
	relPath, _ := filepath.Rel(reposRoot, filePath)
	metadata := map[string]string{
		"size": fmt.Sprintf("%d", len(content)),
		"ext":  filepath.Ext(filePath),
	}
	
	req := DocumentRequest{
		ID:       relPath,
		Content:  string(content),
		Path:     relPath,
		Language: strings.TrimPrefix(filepath.Ext(filePath), "."),
		Metadata: metadata,
	}
	
	resp, err := makeRequest("POST", "/api/v1/documents", req)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	
	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusCreated {
		return fmt.Errorf("failed to index %s: status %d", relPath, resp.StatusCode)
	}
	
	return nil
}

func getStats() (map[string]interface{}, error) {
	resp, err := makeRequest("GET", "/api/v1/storage/info", nil)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	
	var stats map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&stats); err != nil {
		return nil, err
	}
	
	return stats, nil
}

func getSMTStats() (map[string]interface{}, error) {
	resp, err := makeRequest("GET", "/api/v1/smt/stats", nil)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	
	var stats map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&stats); err != nil {
		return nil, err
	}
	
	return stats, nil
}

func runBenchmarkQueries() {
	queries := []string{
		"GraphQL schema resolver implementation",
		"database transaction handling error recovery",
		"authentication middleware security patterns",
		"Redis caching optimization strategies",
		"microservice communication patterns",
		"concurrent data processing algorithms",
		"API rate limiting implementation",
		"event-driven architecture design",
		"message queue consumer patterns",
		"distributed system consensus algorithms",
	}
	
	fmt.Println("\n=== Running Z3 SMT Optimization Benchmark ===")
	
	for i, query := range queries {
		fmt.Printf("\nQuery %d: %s\n", i+1, query)
		
		start := time.Now()
		
		req := QueryRequest{
			Query:      query,
			MaxResults: 10,
		}
		
		resp, err := makeRequest("POST", "/api/v1/query", req)
		if err != nil {
			fmt.Printf("Error: %v\n", err)
			continue
		}
		defer resp.Body.Close()
		
		duration := time.Since(start)
		fmt.Printf("Response time: %v\n", duration)
		
		if resp.StatusCode == http.StatusOK {
			var result map[string]interface{}
			json.NewDecoder(resp.Body).Decode(&result)
			if docs, ok := result["documents"].([]interface{}); ok {
				fmt.Printf("Results: %d documents\n", len(docs))
			}
		}
		
		// Brief pause between queries
		time.Sleep(100 * time.Millisecond)
	}
	
	// Get final SMT stats
	smtStats, err := getSMTStats()
	if err == nil {
		fmt.Println("\n=== Final Z3 SMT Statistics ===")
		statsJson, _ := json.MarshalIndent(smtStats, "", "  ")
		fmt.Println(string(statsJson))
	}
}

func main() {
	fmt.Println("=== ContextLite 12GB Comprehensive Benchmark ===")
	fmt.Printf("Indexing root: %s\n", reposRoot)
	
	// Get initial stats
	initialStats, err := getStats()
	if err != nil {
		log.Printf("Warning: Could not get initial stats: %v", err)
	} else {
		fmt.Printf("Initial database state: %v documents\n", initialStats["total_documents"])
	}
	
	startTime := time.Now()
	var totalFiles, indexedFiles, errorCount int
	
	err = filepath.WalkDir(reposRoot, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return nil // Skip errors, continue walking
		}
		
		if d.IsDir() {
			return nil
		}
		
		if !shouldIncludeFile(path) {
			return nil
		}
		
		totalFiles++
		
		if err := indexFile(path); err != nil {
			errorCount++
			if errorCount < 10 {
				log.Printf("Error indexing %s: %v", path, err)
			}
		} else {
			indexedFiles++
		}
		
		// Progress reporting
		if totalFiles%1000 == 0 {
			elapsed := time.Since(startTime)
			rate := float64(totalFiles) / elapsed.Seconds()
			fmt.Printf("Progress: %d files processed (%d indexed, %d errors) - %.1f files/sec\n", 
				totalFiles, indexedFiles, errorCount, rate)
			
			// Get current stats
			if stats, err := getStats(); err == nil {
				fmt.Printf("Database: %v documents, %s size\n", 
					stats["total_documents"], stats["database_size"])
			}
		}
		
		return nil
	})
	
	if err != nil {
		log.Printf("Walk error: %v", err)
	}
	
	duration := time.Since(startTime)
	
	fmt.Println("\n=== Indexing Complete ===")
	fmt.Printf("Total files processed: %d\n", totalFiles)
	fmt.Printf("Successfully indexed: %d\n", indexedFiles)
	fmt.Printf("Errors: %d\n", errorCount)
	fmt.Printf("Total time: %v\n", duration)
	fmt.Printf("Average rate: %.1f files/sec\n", float64(totalFiles)/duration.Seconds())
	
	// Get final stats
	finalStats, err := getStats()
	if err != nil {
		log.Printf("Error getting final stats: %v", err)
	} else {
		fmt.Println("\n=== Final Database Statistics ===")
		statsJson, _ := json.MarshalIndent(finalStats, "", "  ")
		fmt.Println(string(statsJson))
	}
	
	// Run benchmark queries
	runBenchmarkQueries()
	
	fmt.Println("\n=== 12GB Benchmark Complete ===")
}
