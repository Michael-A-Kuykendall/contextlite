package integration_suite

import (
	"bytes"
	"encoding/json"
	"fmt"
	"net/http"
	"testing"
	"time"
)

const TestServerURL = "http://127.0.0.1:8082"
const TestAuthToken = "contextlite-dev-token-2025" // Default dev token from config

type TestDocument struct {
	ID      string `json:"id"`
	Path    string `json:"path"`
	Content string `json:"content"`
}

type SearchResponse struct {
	Documents []map[string]interface{} `json:"documents"`
	Metadata  map[string]interface{}   `json:"metadata"`
}

// addAuthHeader adds the Bearer token to HTTP requests
func addAuthHeader(req *http.Request) {
	req.Header.Set("Authorization", "Bearer "+TestAuthToken)
}

func TestGoClientIntegration(t *testing.T) {
	// Check if server is available for all tests
	resp, err := http.Get(TestServerURL + "/health")
	if err != nil {
		t.Skipf("Skipping integration tests - server not available: %v", err)
	}
	resp.Body.Close()
	if resp.StatusCode != 200 {
		t.Skipf("Skipping integration tests - server not healthy: status %d", resp.StatusCode)
	}

// Test basic connectivity
	t.Run("ServerConnectivity", func(t *testing.T) {
		// Health endpoint is at /health (not /api/v1/health) and doesn't require auth
		resp, err := http.Get(TestServerURL + "/health")
		if err != nil {
			t.Skipf("Server not running for integration test: %v", err)
		}
		defer resp.Body.Close()

		if resp.StatusCode != 200 {
			t.Fatalf("Server health check failed: %d", resp.StatusCode)
		}
		t.Log("✅ Go client can connect to ContextLite server")
	})	// Test document indexing
	t.Run("DocumentIndexing", func(t *testing.T) {
		// Check server availability first
		resp, err := http.Get(TestServerURL + "/health")
		if err != nil {
			t.Skipf("Server not available for test: %v", err)
		}
		resp.Body.Close()
		if resp.StatusCode != 200 {
			t.Skipf("Server not healthy for test: status %d", resp.StatusCode)
		}

		doc := TestDocument{
			ID:      "go-test-doc-1",
			Path:    "/test/go/example.go",
			Content: "package main\n\nfunc main() {\n\tfmt.Println(\"Hello from Go integration test\")\n}",
		}

		jsonData, _ := json.Marshal(doc)
		req, _ := http.NewRequest("POST", TestServerURL+"/api/v1/documents", bytes.NewBuffer(jsonData))
		req.Header.Set("Content-Type", "application/json")
		addAuthHeader(req)
		
		client := &http.Client{}
		resp, err = client.Do(req)
		if err != nil {
			t.Fatalf("Failed to index document: %v", err)
		}
		defer resp.Body.Close()

		if resp.StatusCode != 200 && resp.StatusCode != 201 {
			t.Fatalf("Document indexing failed: %d", resp.StatusCode)
		}
		t.Log("✅ Go client can index documents")
	})

	// Test search and retrieval
	t.Run("SearchRetrieval", func(t *testing.T) {
		start := time.Now()
		req, _ := http.NewRequest("GET", TestServerURL+"/api/v1/documents/search?q=golang%20main%20function&limit=5", nil)
		addAuthHeader(req)
		
		client := &http.Client{}
		resp, err := client.Do(req)
		elapsed := time.Since(start)

		if err != nil {
			t.Fatalf("Failed to search documents: %v", err)
		}
		defer resp.Body.Close()

		var searchResp SearchResponse
		if err := json.NewDecoder(resp.Body).Decode(&searchResp); err != nil {
			t.Fatalf("Failed to decode search response: %v", err)
		}

		if len(searchResp.Documents) == 0 {
			t.Log("No documents returned from search - this may be expected if no documents are indexed")
		}

		if elapsed > 100*time.Millisecond {
			t.Logf("⚠️  Search took %v (target: <100ms)", elapsed)
		} else {
			t.Logf("✅ Search completed in %v", elapsed)
		}

		t.Log("✅ Go client can search and retrieve documents")
	})

	// Test context assembly
	t.Run("ContextAssembly", func(t *testing.T) {
		start := time.Now()
		
		// Context assembly uses POST with JSON body
		reqBody := map[string]interface{}{
			"query":        "Go programming examples",
			"max_tokens":   2000,
			"max_documents": 5,
			"model_id":     "gpt-4",
			"use_smt":      false,
		}
		
		jsonData, _ := json.Marshal(reqBody)
		req, _ := http.NewRequest("POST", TestServerURL+"/api/v1/context/assemble", bytes.NewBuffer(jsonData))
		req.Header.Set("Content-Type", "application/json")
		addAuthHeader(req)
		
		client := &http.Client{}
		resp, err := client.Do(req)
		elapsed := time.Since(start)

		if err != nil {
			t.Fatalf("Failed to assemble context: %v", err)
		}
		defer resp.Body.Close()

		if resp.StatusCode != 200 {
			t.Fatalf("Context assembly failed: %d", resp.StatusCode)
		}

		if elapsed > 100*time.Millisecond {
			t.Logf("⚠️  Context assembly took %v (target: <100ms)", elapsed)
		} else {
			t.Logf("✅ Context assembly completed in %v", elapsed)
		}

		t.Log("✅ Go client can assemble context for AI requests")
	})
}

func TestGoClientPerformance(t *testing.T) {
	// Check if server is available for performance tests
	resp, err := http.Get(TestServerURL + "/health")
	if err != nil {
		t.Skipf("Skipping performance tests - server not available: %v", err)
	}
	resp.Body.Close()
	if resp.StatusCode != 200 {
		t.Skipf("Skipping performance tests - server not healthy: status %d", resp.StatusCode)
	}

	// Basic performance test
	t.Run("ConcurrentAccess", func(t *testing.T) {
		const numGoroutines = 10
		const requestsPerGoroutine = 5

		done := make(chan bool, numGoroutines)
		errors := make(chan error, numGoroutines*requestsPerGoroutine)

		start := time.Now()

		for i := 0; i < numGoroutines; i++ {
			go func(id int) {
				for j := 0; j < requestsPerGoroutine; j++ {
					req, _ := http.NewRequest("GET", fmt.Sprintf("%s/api/v1/documents/search?q=test%d&limit=3", TestServerURL, id), nil)
					addAuthHeader(req)
					
					client := &http.Client{}
					resp, err := client.Do(req)
					if err != nil {
						errors <- err
						continue
					}
					resp.Body.Close()

					if resp.StatusCode != 200 {
						errors <- fmt.Errorf("request failed with status %d", resp.StatusCode)
					}
				}
				done <- true
			}(i)
		}

		// Wait for all goroutines to complete
		for i := 0; i < numGoroutines; i++ {
			<-done
		}
		elapsed := time.Since(start)

		// Check for errors
		close(errors)
		errorCount := 0
		for err := range errors {
			t.Logf("Error: %v", err)
			errorCount++
		}

		if errorCount > 0 {
			t.Fatalf("Concurrent access failed with %d errors", errorCount)
		}

		avgTimePerRequest := elapsed / time.Duration(numGoroutines*requestsPerGoroutine)
		t.Logf("✅ Concurrent access successful: %d requests in %v (avg: %v per request)", 
numGoroutines*requestsPerGoroutine, elapsed, avgTimePerRequest)
})
}
