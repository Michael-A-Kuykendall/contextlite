package helpers

import (
	"bytes"
	"encoding/json"
	"fmt"
	"net/http"
	"os"
	"path/filepath"
	"strconv"
	"testing"
	"time"

	"contextlite/internal/storage"
)

// TestServer represents a test server instance
type TestServer struct {
	BaseURL string
	DBPath  string
	Storage *storage.Storage
	t       *testing.T
}

// StartTestServer creates and returns a test server instance
func StartTestServer(t *testing.T) *TestServer {
	// Create temp directory for test database
	tempDir := os.TempDir()
	dbPath := filepath.Join(tempDir, fmt.Sprintf("test_contextlite_%d.db", time.Now().UnixNano()))

	// Initialize storage
	store, err := storage.New(dbPath)
	if err != nil {
		t.Fatalf("Failed to create storage: %v", err)
	}

	server := &TestServer{
		BaseURL: "http://127.0.0.1:8083", // Use fixed test URL - assumes server running
		DBPath:  dbPath,
		Storage: store,
		t:       t,
	}

	// Wait a moment for server to be ready
	time.Sleep(100 * time.Millisecond)
	
	return server
}

// Stop cleans up the test server
func (s *TestServer) Stop() {
	if s.Storage != nil {
		s.Storage.Close()
	}
	if s.DBPath != "" {
		os.Remove(s.DBPath)
	}
}

// AddTestDocument adds a test document to the server
func (s *TestServer) AddTestDocument(id, content string) error {
	doc := map[string]interface{}{
		"id":      id,
		"content": content,
		"metadata": map[string]interface{}{
			"path": fmt.Sprintf("/test/%s", id),
		},
	}

	docJSON, _ := json.Marshal(doc)
	resp, err := http.Post(s.BaseURL+"/api/v1/documents", "application/json", bytes.NewReader(docJSON))
	if err != nil {
		return err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusCreated && resp.StatusCode != http.StatusOK {
		return fmt.Errorf("unexpected status code: %d", resp.StatusCode)
	}

	return nil
}

// GetTestDocumentCount returns the number of documents in the test database
func (s *TestServer) GetTestDocumentCount() (int, error) {
	resp, err := http.Get(s.BaseURL + "/api/v1/storage/info")
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()

	var result map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return 0, err
	}

	if count, ok := result["total_documents"].(float64); ok {
		return int(count), nil
	}

	if countStr, ok := result["total_documents"].(string); ok {
		return strconv.Atoi(countStr)
	}

	return 0, fmt.Errorf("could not determine document count")
}
