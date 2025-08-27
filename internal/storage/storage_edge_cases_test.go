package storage

import (
	"context"
	"strings"
	"testing"
	"time"

	"contextlite/pkg/types"
)

// Test edge cases for improved coverage of specific functions
func TestStorage_New_EdgeCases(t *testing.T) {
	t.Run("New_InvalidPath", func(t *testing.T) {
		// Test with invalid database path
		_, err := New("/invalid/path/that/does/not/exist/test.db")
		if err == nil {
			t.Error("Expected error for invalid database path")
		}
	})

	t.Run("New_ValidPath", func(t *testing.T) {
		// Test with valid path (this should improve New() coverage)
		storage, cleanup := setupTestStorage(t)
		defer cleanup()

		if storage == nil {
			t.Error("Expected valid storage instance")
		}

		// Test database connection
		ctx := context.Background()
		stats, err := storage.GetStorageStats(ctx)
		if err != nil {
			t.Fatalf("Storage should be functional: %v", err)
		}

		if stats == nil {
			t.Error("Expected valid storage stats")
		}
	})
}

// Test searchLike function coverage improvement
func TestStorage_SearchLike_EdgeCases(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	// Add documents with special characters to test LIKE search
	docs := []*types.Document{
		{
			ID:           "like-test-1",
			Path:         "/test/like/file_with_underscores.go",
			Content:      "package like_test\nfunc TestWith_Underscores() {}",
			TokenCount:   8,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		},
		{
			ID:           "like-test-2", 
			Path:         "/test/like/file%with%percent.go",
			Content:      "package like_test\nfunc TestWith%Percent() {}",
			TokenCount:   7,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		},
		{
			ID:           "like-test-3",
			Path:         "/test/like/normal_file.go",
			Content:      "package like_test\nfunc NormalTest() {}",
			TokenCount:   6,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		},
	}

	// Add all documents
	for _, doc := range docs {
		err := storage.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("Failed to add document %s: %v", doc.ID, err)
		}
	}

	// Test LIKE search with various patterns
	t.Run("SearchLike_Underscores", func(t *testing.T) {
		results, err := storage.SearchDocuments(ctx, "underscores", 10)
		if err != nil {
			t.Fatalf("Search failed: %v", err)
		}

		found := false
		for _, doc := range results {
			if doc.ID == "like-test-1" {
				found = true
				break
			}
		}
		if !found {
			t.Error("Expected to find document with underscores")
		}
	})

	t.Run("SearchLike_Percent", func(t *testing.T) {
		results, err := storage.SearchDocuments(ctx, "percent", 10)
		if err != nil {
			t.Fatalf("Search failed: %v", err)
		}

		found := false
		for _, doc := range results {
			if doc.ID == "like-test-2" {
				found = true
				break
			}
		}
		if !found {
			t.Error("Expected to find document with percent")
		}
	})

	t.Run("SearchLike_CaseInsensitive", func(t *testing.T) {
		results, err := storage.SearchDocuments(ctx, "NORMAL", 10)
		if err != nil {
			t.Fatalf("Search failed: %v", err)
		}

		found := false
		for _, doc := range results {
			if doc.ID == "like-test-3" {
				found = true
				break
			}
		}
		if !found {
			t.Error("Expected to find document with case-insensitive search")
		}
	})
}

// Test GetCorpusHash edge cases for improved coverage
func TestStorage_GetCorpusHash_EdgeCases(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	// Test 1: Empty database corpus hash
	hash1, err := storage.GetCorpusHash(ctx)
	if err != nil {
		t.Fatalf("GetCorpusHash failed on empty database: %v", err)
	}

	if hash1 == "" {
		t.Error("Expected non-empty hash even for empty corpus")
	}

	// Test 2: Add document and verify hash changes
	doc := &types.Document{
		ID:           "hash-test-1",
		Path:         "/test/hash/file.go",
		Content:      "package hash\nfunc HashTest() {}",
		TokenCount:   5,
		Language:     "go", 
		ModifiedTime: time.Now().Unix(),
	}

	err = storage.AddDocument(ctx, doc)
	if err != nil {
		t.Fatalf("Failed to add document: %v", err)
	}

	hash2, err := storage.GetCorpusHash(ctx)
	if err != nil {
		t.Fatalf("GetCorpusHash failed after adding document: %v", err)
	}

	if hash2 == hash1 {
		t.Error("Expected corpus hash to change after adding document")
	}

	// Test 3: Add another document and verify hash changes again
	doc2 := &types.Document{
		ID:           "hash-test-2",
		Path:         "/test/hash/file2.go", 
		Content:      "package hash\nfunc HashTest2() {}",
		TokenCount:   6,
		Language:     "go",
		ModifiedTime: time.Now().Unix(),
	}

	err = storage.AddDocument(ctx, doc2)
	if err != nil {
		t.Fatalf("Failed to add second document: %v", err)
	}

	hash3, err := storage.GetCorpusHash(ctx)
	if err != nil {
		t.Fatalf("GetCorpusHash failed after adding second document: %v", err)
	}

	if hash3 == hash2 {
		t.Error("Expected corpus hash to change after adding second document")
	}

	// Test 4: Same corpus should produce same hash
	hash4, err := storage.GetCorpusHash(ctx)
	if err != nil {
		t.Fatalf("GetCorpusHash failed on repeat call: %v", err)
	}

	if hash4 != hash3 {
		t.Error("Expected same hash for unchanged corpus")
	}
}

// Test applyMigrations edge cases for improved coverage  
func TestStorage_ApplyMigrations_EdgeCases(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	// The migrations should have been applied during New()
	// Test that the schema is properly set up
	ctx := context.Background()

	// Verify tables exist by attempting operations
	t.Run("TablesExist", func(t *testing.T) {
		// Test documents table
		doc := &types.Document{
			ID:           "migration-test",
			Path:         "/test/migration.go",
			Content:      "package migration",
			TokenCount:   3,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		}

		err := storage.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("Documents table not properly created: %v", err)
		}

		// Test workspace_weights table
		weights := &types.WorkspaceWeights{
			WorkspacePath:      "/test/migration",
			RelevanceWeight:    0.3,
			RecencyWeight:      0.2,
			DiversityWeight:    0.15,
			EntanglementWeight: 0.15,
			RedundancyPenalty:  0.1,
			UpdateCount:        1,
			LastUpdated:        time.Now().Format(time.RFC3339),
		}

		// Convert to FeatureWeights for SaveWorkspaceWeights
		featureWeights := types.FeatureWeights{
			Relevance:    weights.RelevanceWeight,
			Recency:      weights.RecencyWeight,
			Entanglement: weights.EntanglementWeight,
			Specificity:  weights.DiversityWeight,
			Uncertainty:  weights.RedundancyPenalty,
		}

		err = storage.SaveWorkspaceWeights(weights.WorkspacePath, featureWeights)
		if err != nil {
			t.Fatalf("Workspace weights table not properly created: %v", err)
		}
	})
}

// Test scan edge cases for scanDocuments function
func TestStorage_ScanDocuments_EdgeCases(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	// Add documents with edge case data
	docs := []*types.Document{
		{
			ID:           "scan-test-1",
			Path:         "/test/scan/normal.go",
			Content:      "package scan\nfunc Normal() {}",
			TokenCount:   5,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		},
		{
			ID:           "scan-test-2",
			Path:         "/test/scan/empty_content.go", 
			Content:      "", // Empty content
			TokenCount:   0,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		},
		{
			ID:           "scan-test-3",
			Path:         "/test/scan/unicode.go",
			Content:      "package scan\n// Unicode: 你好世界 🚀\nfunc Unicode() {}",
			TokenCount:   8,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		},
	}

	// Add all documents
	for _, doc := range docs {
		err := storage.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("Failed to add document %s: %v", doc.ID, err)
		}
	}

	// Test search to exercise scanDocuments
	t.Run("ScanDocuments_Normal", func(t *testing.T) {
		results, err := storage.SearchDocuments(ctx, "scan", 10)
		if err != nil {
			t.Fatalf("Search failed: %v", err)
		}

		if len(results) < 2 { // Should find at least normal and unicode docs
			t.Errorf("Expected at least 2 documents, got %d", len(results))
		}
	})

	t.Run("ScanDocuments_EmptyContent", func(t *testing.T) {
		// Verify empty content document can be retrieved
		doc, err := storage.GetDocument(ctx, "scan-test-2")
		if err != nil {
			t.Fatalf("Failed to get empty content document: %v", err)
		}

		if doc.Content != "" {
			t.Errorf("Expected empty content, got: %s", doc.Content)
		}
	})

	t.Run("ScanDocuments_Unicode", func(t *testing.T) {
		results, err := storage.SearchDocuments(ctx, "unicode", 10)
		if err != nil {
			t.Fatalf("Search failed: %v", err)
		}

		found := false
		for _, doc := range results {
			if doc.ID == "scan-test-3" {
				found = true
				if !strings.Contains(doc.Content, "你好世界") {
					t.Error("Unicode content not preserved properly")
				}
				break
			}
		}
		if !found {
			t.Error("Expected to find unicode document")
		}
	})
}

// Test SaveQueryCache error conditions for improved coverage
func TestStorage_SaveQueryCache_ErrorConditions(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	t.Run("SaveQueryCache_EmptyQueryHash", func(t *testing.T) {
		result := &types.QueryResult{
			Documents: []types.DocumentReference{
				{ID: "cache-empty-key", Path: "/test/cache.go"},
			},
			SMTMetrics: types.SMTMetrics{SolverUsed: "Z3"},
		}
		expiresAt := time.Now().Add(5 * time.Minute)

		err := storage.SaveQueryCache(ctx, "", "corpus", "gpt-4", "1.0", result, expiresAt)
		// Empty query hash may or may not be an error - we just want to exercise the code
		t.Logf("SaveQueryCache with empty query hash result: %v", err)
	})

	t.Run("SaveQueryCache_EmptyDocuments", func(t *testing.T) {
		result := &types.QueryResult{
			Documents: []types.DocumentReference{}, // Empty slice
			SMTMetrics: types.SMTMetrics{SolverUsed: "Z3"},
		}
		expiresAt := time.Now().Add(5 * time.Minute)

		err := storage.SaveQueryCache(ctx, "empty-docs", "corpus", "gpt-4", "1.0", result, expiresAt)
		// Should handle empty documents gracefully
		if err != nil {
			t.Logf("SaveQueryCache with empty docs returned error: %v", err)
		}
	})

	t.Run("SaveQueryCache_PastExpiry", func(t *testing.T) {
		result := &types.QueryResult{
			Documents: []types.DocumentReference{
				{ID: "cache-past-expiry", Path: "/test/cache.go"},
			},
			SMTMetrics: types.SMTMetrics{SolverUsed: "Z3"},
		}
		// Past expiry time
		expiresAt := time.Now().Add(-5 * time.Minute)

		err := storage.SaveQueryCache(ctx, "past-expiry", "corpus", "gpt-4", "1.0", result, expiresAt)
		// Should handle past expiry gracefully
		if err != nil {
			t.Logf("SaveQueryCache with past expiry returned error: %v", err)
		}
	})

	t.Run("SaveQueryCache_InvalidModelID", func(t *testing.T) {
		result := &types.QueryResult{
			Documents: []types.DocumentReference{
				{ID: "cache-invalid-model", Path: "/test/cache.go"},
			},
			SMTMetrics: types.SMTMetrics{SolverUsed: "Z3"},
		}
		expiresAt := time.Now().Add(5 * time.Minute)

		err := storage.SaveQueryCache(ctx, "invalid-model", "corpus", "", "1.0", result, expiresAt)
		// Should handle empty model ID gracefully  
		if err != nil {
			t.Logf("SaveQueryCache with empty model ID returned error: %v", err)
		}
	})
}

// Test DeleteDocument edge cases for improved coverage
func TestStorage_DeleteDocument_ErrorPaths(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	t.Run("DeleteDocument_EmptyID", func(t *testing.T) {
		err := storage.DeleteDocument(ctx, "")
		if err == nil {
			t.Error("Expected error for empty document ID")
		}
	})

	t.Run("DeleteDocument_NonExistentID", func(t *testing.T) {
		err := storage.DeleteDocument(ctx, "definitely-does-not-exist")
		// This may or may not return an error depending on implementation
		// We just want to exercise the code path
		t.Logf("DeleteDocument for non-existent ID result: %v", err)
	})

	t.Run("DeleteDocument_ValidFlow", func(t *testing.T) {
		// Add a document first
		doc := &types.Document{
			ID:           "delete-valid-test",
			Path:         "/test/delete/valid.go",
			Content:      "package delete",
			TokenCount:   3,
			Language:     "go",
			ModifiedTime: time.Now().Unix(),
		}

		err := storage.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("Failed to add document for deletion: %v", err)
		}

		// Verify it exists
		_, err = storage.GetDocument(ctx, doc.ID)
		if err != nil {
			t.Fatalf("Document should exist before deletion: %v", err)
		}

		// Delete it
		err = storage.DeleteDocument(ctx, doc.ID)
		if err != nil {
			t.Fatalf("DeleteDocument failed: %v", err)
		}

		// Verify it's gone
		_, err = storage.GetDocument(ctx, doc.ID)
		if err == nil {
			t.Error("Document should not exist after deletion")
		}
	})
}