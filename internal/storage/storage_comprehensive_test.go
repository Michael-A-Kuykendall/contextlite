package storage

import (
	"context"
	"fmt"
	"strings"
	"testing"
	"time"

	"contextlite/pkg/types"
)

// Test GetWorkspaceStats (currently 0.0% coverage)
func TestStorage_GetWorkspaceStats_Comprehensive(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()
	workspacePath := "/test/workspace"

	// Test 1: Empty workspace stats
	stats, err := storage.GetWorkspaceStats(workspacePath)
	if err != nil {
		t.Fatalf("GetWorkspaceStats failed for empty workspace: %v", err)
	}
	
	if stats.DocumentCount != 0 {
		t.Errorf("Expected 0 documents in empty workspace, got %d", stats.DocumentCount)
	}
	if stats.TotalTokens != 0 {
		t.Errorf("Expected 0 tokens in empty workspace, got %d", stats.TotalTokens)
	}

	// Test 2: Add documents and verify stats
	doc1 := &types.Document{
		ID:           "ws-doc-1",
		Path:         "/test/workspace/file1.go",
		Content:      "package main\nfunc main() {}",
		TokenCount:   10,
		Language:     "go",
		ModifiedTime: time.Now().Unix(),
	}

	doc2 := &types.Document{
		ID:           "ws-doc-2",
		Path:         "/test/workspace/subdir/file2.go",
		Content:      "package subdir\ntype Config struct {}",
		TokenCount:   15,
		Language:     "go",
		ModifiedTime: time.Now().Unix(),
	}

	// Add documents
	err = storage.AddDocument(ctx, doc1)
	if err != nil {
		t.Fatalf("Failed to add doc1: %v", err)
	}
	err = storage.AddDocument(ctx, doc2)
	if err != nil {
		t.Fatalf("Failed to add doc2: %v", err)
	}

	// Test workspace stats with documents
	stats, err = storage.GetWorkspaceStats(workspacePath)
	if err != nil {
		t.Fatalf("GetWorkspaceStats failed with documents: %v", err)
	}

	if stats.DocumentCount != 2 {
		t.Errorf("Expected 2 documents in workspace, got %d", stats.DocumentCount)
	}
	if stats.TotalTokens != 25 {
		t.Errorf("Expected 25 total tokens, got %d", stats.TotalTokens)
	}

	// Test 3: Different workspace path (should not include our docs)
	differentStats, err := storage.GetWorkspaceStats("/different/workspace")
	if err != nil {
		t.Fatalf("GetWorkspaceStats failed for different workspace: %v", err)
	}
	
	if differentStats.DocumentCount != 0 {
		t.Errorf("Expected 0 documents in different workspace, got %d", differentStats.DocumentCount)
	}
}

// Test InsertDocument (currently 0.0% coverage)
func TestStorage_InsertDocument_Comprehensive(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	// Test 1: Valid document insert
	doc := types.Document{
		ID:           "insert-test-1",
		Path:         "/test/insert/file.go",
		Content:      "package insert\nfunc TestFunc() {}",
		TokenCount:   8,
		Language:     "go",
		ModifiedTime: time.Now().Unix(),
	}

	err := storage.InsertDocument(doc)
	if err != nil {
		t.Fatalf("InsertDocument failed: %v", err)
	}

	// Verify the document was inserted
	retrieved, err := storage.GetDocument(context.Background(), doc.ID)
	if err != nil {
		t.Fatalf("Failed to retrieve inserted document: %v", err)
	}

	if retrieved.ID != doc.ID {
		t.Errorf("Expected ID %s, got %s", doc.ID, retrieved.ID)
	}
	if retrieved.Path != doc.Path {
		t.Errorf("Expected path %s, got %s", doc.Path, retrieved.Path)
	}

	// Test 2: Insert duplicate (should update)
	docUpdate := types.Document{
		ID:           "insert-test-1",
		Path:         "/test/insert/file.go",
		Content:      "package insert\nfunc TestFunc() {}\nfunc NewFunc() {}",
		TokenCount:   12,
		Language:     "go",
		ModifiedTime: time.Now().Unix(),
	}

	err = storage.InsertDocument(docUpdate)
	if err != nil {
		t.Fatalf("InsertDocument failed for update: %v", err)
	}

	// Verify the document was updated
	retrieved, err = storage.GetDocument(context.Background(), docUpdate.ID)
	if err != nil {
		t.Fatalf("Failed to retrieve updated document: %v", err)
	}

	if retrieved.TokenCount != 12 {
		t.Errorf("Expected token count 12, got %d", retrieved.TokenCount)
	}
}

// Test UpdateDocument (currently 0.0% coverage)
func TestStorage_UpdateDocument_Comprehensive(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	// First insert a document
	original := types.Document{
		ID:           "update-test-1",
		Path:         "/test/update/file.go",
		Content:      "package update\nfunc OriginalFunc() {}",
		TokenCount:   6,
		Language:     "go",
		ModifiedTime: time.Now().Unix(),
	}

	err := storage.AddDocument(ctx, &original)
	if err != nil {
		t.Fatalf("Failed to add original document: %v", err)
	}

	// Test UpdateDocument
	updated := types.Document{
		ID:           "update-test-1",
		Path:         "/test/update/file.go",
		Content:      "package update\nfunc OriginalFunc() {}\nfunc UpdatedFunc() {}",
		TokenCount:   10,
		Language:     "go",
		ModifiedTime: time.Now().Add(time.Hour).Unix(),
	}

	err = storage.UpdateDocument(updated)
	if err != nil {
		t.Fatalf("UpdateDocument failed: %v", err)
	}

	// Verify the update
	retrieved, err := storage.GetDocument(ctx, updated.ID)
	if err != nil {
		t.Fatalf("Failed to retrieve updated document: %v", err)
	}

	if retrieved.TokenCount != 10 {
		t.Errorf("Expected token count 10, got %d", retrieved.TokenCount)
	}
	if !strings.Contains(retrieved.Content, "UpdatedFunc") {
		t.Error("Expected updated content to contain UpdatedFunc")
	}
}

// Test GetDocumentByPath (currently 0.0% coverage)
func TestStorage_GetDocumentByPath_Comprehensive(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	// Test 1: Document not found
	_, err := storage.GetDocumentByPath(ctx, "/nonexistent/path.go")
	if err == nil {
		t.Error("Expected error for nonexistent document path")
	}

	// Test 2: Add document and retrieve by path
	doc := &types.Document{
		ID:           "path-test-1",
		Path:         "/test/path/unique_file.go",
		Content:      "package path\nfunc PathTest() {}",
		TokenCount:   5,
		Language:     "go",
		ModifiedTime: time.Now().Unix(),
	}

	err = storage.AddDocument(ctx, doc)
	if err != nil {
		t.Fatalf("Failed to add document: %v", err)
	}

	// Retrieve by path
	retrieved, err := storage.GetDocumentByPath(ctx, doc.Path)
	if err != nil {
		t.Fatalf("GetDocumentByPath failed: %v", err)
	}

	if retrieved.ID != doc.ID {
		t.Errorf("Expected ID %s, got %s", doc.ID, retrieved.ID)
	}
	if retrieved.Path != doc.Path {
		t.Errorf("Expected path %s, got %s", doc.Path, retrieved.Path)
	}
	if retrieved.Content != doc.Content {
		t.Errorf("Expected content %s, got %s", doc.Content, retrieved.Content)
	}

	// Test 3: Path with special characters
	specialDoc := &types.Document{
		ID:           "path-test-2",
		Path:         "/test/path/file with spaces & symbols.go",
		Content:      "package special\nfunc SpecialTest() {}",
		TokenCount:   6,
		Language:     "go",
		ModifiedTime: time.Now().Unix(),
	}

	err = storage.AddDocument(ctx, specialDoc)
	if err != nil {
		t.Fatalf("Failed to add special document: %v", err)
	}

	retrieved, err = storage.GetDocumentByPath(ctx, specialDoc.Path)
	if err != nil {
		t.Fatalf("GetDocumentByPath failed for special path: %v", err)
	}

	if retrieved.ID != specialDoc.ID {
		t.Errorf("Expected ID %s, got %s", specialDoc.ID, retrieved.ID)
	}
}

// Test error conditions and edge cases for coverage improvement
func TestStorage_ErrorConditions_Comprehensive(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	// Test AddDocument with various edge cases
	t.Run("AddDocument_EmptyContent", func(t *testing.T) {
		doc := &types.Document{
			ID:           "empty-content",
			Path:         "/test/empty.go",
			Content:      "",
			TokenCount:   0,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		}

		err := storage.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("AddDocument should handle empty content: %v", err)
		}
	})

	t.Run("AddDocument_LongContent", func(t *testing.T) {
		longContent := strings.Repeat("func test() {}\n", 1000)
		doc := &types.Document{
			ID:           "long-content",
			Path:         "/test/long.go",
			Content:      longContent,
			TokenCount:   4000,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		}

		err := storage.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("AddDocument should handle long content: %v", err)
		}
	})

	t.Run("DeleteDocument_EdgeCases", func(t *testing.T) {
		// Test deleting non-existent document
		err := storage.DeleteDocument(ctx, "non-existent-id")
		if err != nil {
			t.Logf("DeleteDocument for non-existent ID returned error (expected): %v", err)
		}

		// Add and delete a document to test the normal path
		doc := &types.Document{
			ID:           "delete-test",
			Path:         "/test/delete.go",
			Content:      "package delete\nfunc DeleteTest() {}",
			TokenCount:   5,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		}

		err = storage.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("Failed to add document for deletion: %v", err)
		}

		err = storage.DeleteDocument(ctx, doc.ID)
		if err != nil {
			t.Fatalf("DeleteDocument failed: %v", err)
		}

		// Verify deletion
		_, err = storage.GetDocument(ctx, doc.ID)
		if err == nil {
			t.Error("Expected error when getting deleted document")
		}
	})
}

// Test cache operations for improved coverage
func TestStorage_CacheOperations_Comprehensive(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	// Test SaveQueryCache and GetQueryCache
	t.Run("QueryCache_Operations", func(t *testing.T) {
		queryHash := "test-query-hash"
		corpusHash := "test-corpus-hash"
		modelID := "gpt-4"
		tokenizerVersion := "1.0"
		expiresAt := time.Now().Add(5 * time.Minute)

		result := &types.QueryResult{
			Documents: []types.DocumentReference{
				{
					ID:              "cache-doc-1",
					Path:            "/test/cache1.go",
					Content:         "package cache",
					Language:        "go",
					UtilityScore:    0.8,
					InclusionReason: "test",
				},
			},
			optimizationMetrics: types.optimizationMetrics{
				SolverUsed:  "optimizer",
				SolveTimeMs: 10.5,
			},
			CoherenceScore: 0.85,
		}

		// Save to cache
		err := storage.SaveQueryCache(ctx, queryHash, corpusHash, modelID, tokenizerVersion, result, expiresAt)
		if err != nil {
			t.Fatalf("SaveQueryCache failed: %v", err)
		}

		// Get from cache
		cached, err := storage.GetQueryCache(ctx, queryHash, corpusHash, modelID, tokenizerVersion)
		if err != nil {
			t.Fatalf("GetQueryCache failed: %v", err)
		}

		if cached == nil {
			t.Error("Expected cache hit, got nil")
			return
		}

		if len(cached.Documents) != 1 {
			t.Errorf("Expected 1 cached document, got %d", len(cached.Documents))
		}

		if len(cached.Documents) > 0 && cached.Documents[0].ID != result.Documents[0].ID {
			t.Errorf("Expected cached doc ID %s, got %s", result.Documents[0].ID, cached.Documents[0].ID)
		}
	})

	t.Run("QueryCache_WithKey_Operations", func(t *testing.T) {
		cacheKey := "test-cache-with-key"
		queryHash := "test-query-hash-key"
		corpusHash := "test-corpus-hash-key"
		modelID := "gpt-4"
		tokenizerVersion := "1.0"
		// contextID removed from function signature
		expiresAt := time.Now().Add(10 * time.Minute)

		result := &types.QueryResult{
			Documents: []types.DocumentReference{
				{
					ID:              "cache-key-doc-1",
					Path:            "/test/cachekey.go", 
					Content:         "package cachekey",
					Language:        "go",
					UtilityScore:    0.7,
					InclusionReason: "test",
				},
			},
			optimizationMetrics: types.optimizationMetrics{
				SolverUsed:  "optimizer",
				SolveTimeMs: 15.2,
			},
			CoherenceScore: 0.75,
		}

		// Save to cache with key
		err := storage.SaveQueryCacheWithKey(ctx, queryHash, corpusHash, modelID, tokenizerVersion, cacheKey, result, expiresAt)
		if err != nil {
			t.Fatalf("SaveQueryCacheWithKey failed: %v", err)
		}

		// Get from cache by key
		cached, err := storage.GetCachedResultByKey(ctx, cacheKey)
		if err != nil {
			t.Fatalf("GetCachedResultByKey failed: %v", err)
		}

		if cached == nil {
			t.Error("Expected cache hit, got nil")
			return
		}

		if len(cached.Documents) != 1 {
			t.Errorf("Expected 1 document, got %d", len(cached.Documents))
		}
	})

	t.Run("InvalidateCache_Operations", func(t *testing.T) {
		// Add some cache entries first
		queryHash1 := "invalidate-test-1"
		queryHash2 := "invalidate-test-2"
		corpusHash := "test-corpus"
		modelID := "gpt-4"
		tokenizerVersion := "1.0"
		expiresAt := time.Now().Add(5 * time.Minute)
		
		result := &types.QueryResult{
			Documents: []types.DocumentReference{
				{ID: "inv-doc-1", Path: "/test/inv1.go"},
			},
			optimizationMetrics: types.optimizationMetrics{SolverUsed: "optimizer"},
		}

		err := storage.SaveQueryCache(ctx, queryHash1, corpusHash, modelID, tokenizerVersion, result, expiresAt)
		if err != nil {
			t.Fatalf("Failed to save cache entry 1: %v", err)
		}

		err = storage.SaveQueryCache(ctx, queryHash2, corpusHash, modelID, tokenizerVersion, result, expiresAt)
		if err != nil {
			t.Fatalf("Failed to save cache entry 2: %v", err)
		}

		// Invalidate cache
		err = storage.InvalidateCache(ctx)
		if err != nil {
			t.Fatalf("InvalidateCache failed: %v", err)
		}

		// Verify cache entries are gone
		_, err = storage.GetQueryCache(ctx, queryHash1, corpusHash, modelID, tokenizerVersion)
		if err == nil {
			t.Error("Expected cache miss after invalidation, got hit")
		}

		_, err = storage.GetQueryCache(ctx, queryHash2, corpusHash, modelID, tokenizerVersion)
		if err == nil {
			t.Error("Expected cache miss after invalidation, got hit")
		}
	})
}

// Test storage stats for improved coverage
func TestStorage_StorageStats_EdgeCases(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	// Test GetStorageStats with empty database
	stats, err := storage.GetStorageStats(ctx)
	if err != nil {
		t.Fatalf("GetStorageStats failed on empty database: %v", err)
	}

	if totalDocs, ok := stats["total_documents"].(int); !ok || totalDocs != 0 {
		t.Errorf("Expected 0 documents in empty database, got %v", stats["total_documents"])
	}

	// Add documents and test stats
	for i := 0; i < 5; i++ {
		doc := &types.Document{
			ID:           fmt.Sprintf("stats-doc-%d", i),
			Path:         fmt.Sprintf("/test/stats/file%d.go", i),
			Content:      fmt.Sprintf("package stats%d\nfunc Test%d() {}", i, i),
			TokenCount:   5 + i,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		}

		err := storage.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("Failed to add stats doc %d: %v", i, err)
		}
	}

	// Get stats again
	stats, err = storage.GetStorageStats(ctx)
	if err != nil {
		t.Fatalf("GetStorageStats failed with documents: %v", err)
	}

	if totalDocs, ok := stats["total_documents"].(int); !ok || totalDocs != 5 {
		t.Errorf("Expected 5 documents, got %v", stats["total_documents"])
	}

	// Test GetCacheStats
	cacheStats, err := storage.GetCacheStats(ctx)
	if err != nil {
		t.Fatalf("GetCacheStats failed: %v", err)
	}

	// Cache stats should be initialized
	if cacheStats.Hits < 0 {
		t.Error("Cache hits should not be negative")
	}
	if cacheStats.Misses < 0 {
		t.Error("Cache misses should not be negative")
	}
}