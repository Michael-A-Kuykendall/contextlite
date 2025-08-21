package pipeline

import (
	"context"
	"testing"
	"time"

	"contextlite/pkg/types"
)

// Simple test to debug document retrieval
func TestPipeline_Debug_DocumentRetrieval(t *testing.T) {
	pipeline, store, cleanup := setupTestPipeline(t)
	defer cleanup()
	
	// Add a simple test document
	ctx := context.Background()
	doc := &types.Document{
		ID:           "test-doc",
		Path:         "/test/main.go",
		Content:      "package main func main() golang programming",
		Language:     "go",
		TokenCount:   10,
		ModifiedTime: time.Now().Unix(),
	}
	
	err := store.AddDocument(ctx, doc)
	if err != nil {
		t.Fatalf("Failed to add test document: %v", err)
	}
	
	// Try to retrieve it
	docs, err := store.SearchDocuments(ctx, "main", 10)
	if err != nil {
		t.Fatalf("Failed to search documents: %v", err)
	}
	
	t.Logf("Found %d documents for query 'main'", len(docs))
	for i, d := range docs {
		t.Logf("Doc %d: ID=%s, Path=%s, Content=%s", i, d.ID, d.Path, d.Content[:min(50, len(d.Content))])
	}
	
	// Now test the pipeline
	req := &types.AssembleRequest{
		Query:         "main",
		MaxTokens:     100,
		MaxDocuments:  2,
		WorkspacePath: "/test",
		ModelID:       "test-model",
	}
	
	result, err := pipeline.AssembleContext(ctx, req)
	if err != nil {
		t.Fatalf("Failed to assemble context: %v", err)
	}
	
	t.Logf("Pipeline returned %d documents", len(result.Documents))
	if len(result.Documents) == 0 {
		t.Error("Expected at least one document from pipeline")
	}
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}
