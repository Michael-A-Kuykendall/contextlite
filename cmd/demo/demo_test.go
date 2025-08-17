package main

import (
	"bytes"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"testing"
	"time"
)

func TestCreateDocumentRequest(t *testing.T) {
	// Test creating a document request
	req := DocumentRequest{
		Path:     "/test/file.go",
		Content:  "package main\nfunc main() {}",
		Type:     "source",
		Language: "go",
	}
	
	if req.Path != "/test/file.go" {
		t.Errorf("Expected path '/test/file.go', got '%s'", req.Path)
	}
	
	if req.Language != "go" {
		t.Errorf("Expected language 'go', got '%s'", req.Language)
	}
}

func TestCreateContextRequest(t *testing.T) {
	// Test creating a context request
	req := ContextRequest{
		Query:        "test query",
		MaxTokens:    1000,
		MaxDocuments: 5,
		Useoptimization:       true,
		UseCache:     false,
	}
	
	if req.Query != "test query" {
		t.Errorf("Expected query 'test query', got '%s'", req.Query)
	}
	
	if req.MaxTokens != 1000 {
		t.Errorf("Expected max tokens 1000, got %d", req.MaxTokens)
	}
	
	if req.MaxDocuments != 5 {
		t.Errorf("Expected max documents 5, got %d", req.MaxDocuments)
	}
	
	if !req.Useoptimization {
		t.Errorf("Expected Useoptimization to be true")
	}
	
	if req.UseCache {
		t.Errorf("Expected UseCache to be false")
	}
}

func TestMakeRequest(t *testing.T) {
	// Create a mock server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Check authorization header
		if r.Header.Get("Authorization") != "Bearer "+token {
			w.WriteHeader(http.StatusUnauthorized)
			return
		}
		
		// Return a mock response
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusOK)
		w.Write([]byte(`{"success": true}`))
	}))
	defer server.Close()
	
	// Test making a request to the mock server
	reqData := map[string]interface{}{
		"test": "data",
	}
	
	data, _ := json.Marshal(reqData)
	req, _ := http.NewRequest("POST", server.URL+"/test", bytes.NewBuffer(data))
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer "+token)
	
	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		t.Fatalf("Request failed: %v", err)
	}
	defer resp.Body.Close()
	
	if resp.StatusCode != http.StatusOK {
		t.Errorf("Expected status 200, got %d", resp.StatusCode)
	}
}

func TestConstants(t *testing.T) {
	// Test that constants are defined
	if baseURL == "" {
		t.Errorf("baseURL should not be empty")
	}
	
	if token == "" {
		t.Errorf("token should not be empty")
	}
	
	// Check that baseURL looks like a URL
	if len(baseURL) < 7 || baseURL[:7] != "http://" && baseURL[:8] != "https://" {
		t.Errorf("baseURL should start with http:// or https://")
	}
}

func TestJSONSerialization(t *testing.T) {
	// Test that our types can be serialized to JSON
	contextReq := ContextRequest{
		Query:        "test",
		MaxTokens:    100,
		MaxDocuments: 2,
		Useoptimization:       true,
		UseCache:     false,
	}
	
	data, err := json.Marshal(contextReq)
	if err != nil {
		t.Fatalf("Failed to marshal ContextRequest: %v", err)
	}
	
	var unmarshaled ContextRequest
	err = json.Unmarshal(data, &unmarshaled)
	if err != nil {
		t.Fatalf("Failed to unmarshal ContextRequest: %v", err)
	}
	
	if unmarshaled.Query != contextReq.Query {
		t.Errorf("Query mismatch after JSON round trip")
	}
	
	if unmarshaled.Useoptimization != contextReq.Useoptimization {
		t.Errorf("Useoptimization mismatch after JSON round trip")
	}
}

func TestDocumentRequestSerialization(t *testing.T) {
	// Test DocumentRequest JSON serialization
	docReq := DocumentRequest{
		Path:     "/test/path",
		Content:  "test content",
		Type:     "source",
		Language: "go",
	}
	
	data, err := json.Marshal(docReq)
	if err != nil {
		t.Fatalf("Failed to marshal DocumentRequest: %v", err)
	}
	
	var unmarshaled DocumentRequest
	err = json.Unmarshal(data, &unmarshaled)
	if err != nil {
		t.Fatalf("Failed to unmarshal DocumentRequest: %v", err)
	}
	
	if unmarshaled.Path != docReq.Path {
		t.Errorf("Path mismatch after JSON round trip")
	}
	
	if unmarshaled.Language != docReq.Language {
		t.Errorf("Language mismatch after JSON round trip")
	}
}
