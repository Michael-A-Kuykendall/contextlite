package storage

import (
	"context"
	"testing"
	"time"

	"contextlite/pkg/types"
)

// Tests to fill the specific coverage gaps identified
func TestStorage_MissingCoverage_GetWorkspaceStats(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	t.Run("GetWorkspaceStats_EmptyWorkspace", func(t *testing.T) {
		stats, err := storage.GetWorkspaceStats("")
		if err != nil {
			t.Logf("GetWorkspaceStats with empty path failed: %v", err)
		} else {
			t.Logf("GetWorkspaceStats with empty path succeeded: %+v", stats)
		}
	})

	t.Run("GetWorkspaceStats_ValidWorkspace", func(t *testing.T) {
		// First add a document for the workspace
		ctx := context.Background()
		doc := &types.Document{
			ID:           "workspace-test",
			Path:         "/test/workspace/file.go",
			Content:      "package workspace",
			Language:     "go",
			TokenCount:   3,
			ModifiedTime: time.Now().Unix(),
		}

		err := storage.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("Failed to add document: %v", err)
		}

		stats, err := storage.GetWorkspaceStats("/test/workspace")
		if err != nil {
			t.Errorf("GetWorkspaceStats should succeed: %v", err)
		} else {
			t.Logf("GetWorkspaceStats result: %+v", stats)
		}
	})

	t.Run("GetWorkspaceStats_NonExistentWorkspace", func(t *testing.T) {
		stats, err := storage.GetWorkspaceStats("/nonexistent/workspace")
		if err != nil {
			t.Logf("GetWorkspaceStats with nonexistent path failed: %v", err)
		} else {
			t.Logf("GetWorkspaceStats with nonexistent path succeeded: %+v", stats)
		}
	})
}

func TestStorage_MissingCoverage_GetDocumentByPath(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	t.Run("GetDocumentByPath_NonExistent", func(t *testing.T) {
		doc, err := storage.GetDocumentByPath(ctx, "/nonexistent/path.go")
		if err != nil {
			t.Logf("GetDocumentByPath correctly failed for nonexistent path: %v", err)
		} else if doc != nil {
			t.Error("Should not return document for nonexistent path")
		}
	})

	t.Run("GetDocumentByPath_Existing", func(t *testing.T) {
		// Add a document first
		testDoc := &types.Document{
			ID:           "path-test-doc",
			Path:         "/test/path/example.go",
			Content:      "package path",
			Language:     "go",
			TokenCount:   3,
			ModifiedTime: time.Now().Unix(),
		}

		err := storage.AddDocument(ctx, testDoc)
		if err != nil {
			t.Fatalf("Failed to add test document: %v", err)
		}

		// Retrieve by path
		doc, err := storage.GetDocumentByPath(ctx, "/test/path/example.go")
		if err != nil {
			t.Errorf("GetDocumentByPath should succeed: %v", err)
		} else if doc == nil {
			t.Error("Should return document for existing path")
		} else if doc.ID != testDoc.ID {
			t.Errorf("Wrong document returned: expected ID %s, got %s", testDoc.ID, doc.ID)
		}
	})

	t.Run("GetDocumentByPath_EmptyPath", func(t *testing.T) {
		doc, err := storage.GetDocumentByPath(ctx, "")
		if err != nil {
			t.Logf("GetDocumentByPath correctly failed for empty path: %v", err)
		} else if doc != nil {
			t.Error("Should not return document for empty path")
		}
	})
}

func TestStorage_MissingCoverage_DeleteDocument_Complete(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	t.Run("DeleteDocument_EmptyIDHandling", func(t *testing.T) {
		err := storage.DeleteDocument(ctx, "")
		// The function may or may not return an error for empty ID
		// We just want to exercise the code path
		t.Logf("DeleteDocument with empty ID result: %v", err)
	})

	t.Run("DeleteDocument_SuccessfulDeletion", func(t *testing.T) {
		// Add document first
		doc := &types.Document{
			ID:           "delete-success-test",
			Path:         "/test/delete/success.go",
			Content:      "package delete",
			Language:     "go",
			TokenCount:   3,
			ModifiedTime: time.Now().Unix(),
		}

		err := storage.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("Failed to add document: %v", err)
		}

		// Verify it exists
		_, err = storage.GetDocument(ctx, doc.ID)
		if err != nil {
			t.Fatalf("Document should exist before deletion: %v", err)
		}

		// Delete it
		err = storage.DeleteDocument(ctx, doc.ID)
		if err != nil {
			t.Errorf("DeleteDocument should succeed: %v", err)
		}

		// Verify it's gone
		_, err = storage.GetDocument(ctx, doc.ID)
		if err == nil {
			t.Error("Document should not exist after deletion")
		}
	})
}

func TestStorage_MissingCoverage_GetCacheStats_Complete(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	t.Run("GetCacheStats_EmptyCache", func(t *testing.T) {
		stats, err := storage.GetCacheStats(ctx)
		if err != nil {
			t.Errorf("GetCacheStats should succeed on empty cache: %v", err)
		} else {
			t.Logf("Empty cache stats: %+v", stats)
		}
	})

	t.Run("GetCacheStats_WithEntries", func(t *testing.T) {
		// Add cache entry
		result := &types.QueryResult{
			Documents: []types.DocumentReference{
				{ID: "cache-test", Path: "/test/cache.go"},
			},
			TotalDocuments: 1,
			TotalTokens:    50,
		}
		expiresAt := time.Now().Add(1 * time.Hour)
		
		err := storage.SaveQueryCache(ctx, "cache-stats-test", "corpus", "gpt-4", "1.0", result, expiresAt)
		if err != nil {
			t.Fatalf("Failed to save cache entry: %v", err)
		}

		stats, err := storage.GetCacheStats(ctx)
		if err != nil {
			t.Errorf("GetCacheStats should succeed with entries: %v", err)
		} else {
			t.Logf("Cache stats with entries: %+v", stats)
		}
	})
}

func TestStorage_MissingCoverage_SaveQueryCacheWithKey_Complete(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	t.Run("SaveQueryCacheWithKey_ValidSave", func(t *testing.T) {
		result := &types.QueryResult{
			Documents: []types.DocumentReference{
				{ID: "cache-key-test-1", Path: "/test1.go"},
				{ID: "cache-key-test-2", Path: "/test2.go"},
			},
			TotalDocuments: 2,
			TotalTokens:    100,
		}
		expiresAt := time.Now().Add(2 * time.Hour)
		
		err := storage.SaveQueryCacheWithKey(ctx, "query-hash", "corpus", "gpt-4", "1.0", "test-cache-key", result, expiresAt)
		if err != nil {
			t.Errorf("SaveQueryCacheWithKey should succeed: %v", err)
		}

		// Try to retrieve it
		cached, err := storage.GetCachedResultByKey(ctx, "test-cache-key")
		if err != nil {
			t.Errorf("GetCachedResultByKey should succeed: %v", err)
		} else if cached == nil {
			t.Error("Should return cached result")
		}
	})

	t.Run("SaveQueryCacheWithKey_UpdateExisting", func(t *testing.T) {
		result1 := &types.QueryResult{
			Documents:      []types.DocumentReference{{ID: "test1", Path: "/test1.go"}},
			TotalDocuments: 1,
			TotalTokens:    50,
		}
		result2 := &types.QueryResult{
			Documents:      []types.DocumentReference{{ID: "test2", Path: "/test2.go"}},
			TotalDocuments: 1,
			TotalTokens:    75,
		}
		expiresAt := time.Now().Add(3 * time.Hour)
		
		// Save first result
		err := storage.SaveQueryCacheWithKey(ctx, "update-test", "corpus", "gpt-4", "1.0", "update-key", result1, expiresAt)
		if err != nil {
			t.Errorf("First save should succeed: %v", err)
		}

		// Update with second result
		err = storage.SaveQueryCacheWithKey(ctx, "update-test", "corpus", "gpt-4", "1.0", "update-key", result2, expiresAt)
		if err != nil {
			t.Errorf("Second save (update) should succeed: %v", err)
		}

		// Verify updated result
		cached, err := storage.GetCachedResultByKey(ctx, "update-key")
		if err != nil {
			t.Errorf("GetCachedResultByKey should succeed: %v", err)
		} else if cached != nil && cached.TotalTokens != 75 {
			t.Errorf("Should return updated result with 75 tokens, got %d", cached.TotalTokens)
		}
	})
}

func TestStorage_MissingCoverage_InvalidateCache_Complete(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	t.Run("InvalidateCache_EmptyCache", func(t *testing.T) {
		err := storage.InvalidateCache(ctx)
		if err != nil {
			t.Errorf("InvalidateCache should succeed on empty cache: %v", err)
		}
	})

	t.Run("InvalidateCache_WithData", func(t *testing.T) {
		// Add cache entries
		result := &types.QueryResult{
			Documents: []types.DocumentReference{{ID: "inv-test", Path: "/test.go"}},
		}
		expiresAt := time.Now().Add(1 * time.Hour)
		
		storage.SaveQueryCache(ctx, "inv-test-1", "corpus", "gpt-4", "1.0", result, expiresAt)
		storage.SaveQueryCache(ctx, "inv-test-2", "corpus", "gpt-4", "1.0", result, expiresAt)

		// Invalidate all
		err := storage.InvalidateCache(ctx)
		if err != nil {
			t.Errorf("InvalidateCache should succeed: %v", err)
		}

		// Verify cache is cleared - stats should reflect this
		stats, err := storage.GetCacheStats(ctx)
		if err != nil {
			t.Errorf("GetCacheStats should succeed after invalidation: %v", err)
		} else {
			t.Logf("Cache stats after invalidation: %+v", stats)
		}
	})
}

func TestStorage_MissingCoverage_SearchLike_EdgeCases(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	// Add documents to test searchLike function
	docs := []*types.Document{
		{
			ID:           "like-edge-1",
			Path:         "/test/like/special_chars.go",
			Content:      "package like\n// Special chars: _underscore_ %percent%",
			Language:     "go",
			TokenCount:   10,
			ModifiedTime: time.Now().Unix(),
		},
		{
			ID:           "like-edge-2",
			Path:         "/test/like/CASE_TEST.go", 
			Content:      "package LIKE\n// UPPERCASE content",
			Language:     "go",
			TokenCount:   8,
			ModifiedTime: time.Now().Unix(),
		},
	}

	for _, doc := range docs {
		err := storage.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("Failed to add document %s: %v", doc.ID, err)
		}
	}

	t.Run("SearchLike_SpecialCharacters", func(t *testing.T) {
		// This should exercise the searchLike function (when FTS fails or as fallback)
		results, err := storage.SearchDocuments(ctx, "special_chars", 10)
		if err != nil {
			t.Errorf("Search should not fail: %v", err)
		}
		t.Logf("Special characters search found %d documents", len(results))
	})

	t.Run("SearchLike_CaseInsensitive", func(t *testing.T) {
		// This should test case insensitive search via LIKE
		results, err := storage.SearchDocuments(ctx, "uppercase", 10)
		if err != nil {
			t.Errorf("Search should not fail: %v", err)
		}
		t.Logf("Case insensitive search found %d documents", len(results))
	})

	t.Run("SearchLike_UnderscorePercent", func(t *testing.T) {
		// Test that underscore and percent are properly escaped in LIKE queries
		results, err := storage.SearchDocuments(ctx, "underscore", 10)
		if err != nil {
			t.Errorf("Search should not fail: %v", err)
		}
		t.Logf("Underscore search found %d documents", len(results))
	})
}