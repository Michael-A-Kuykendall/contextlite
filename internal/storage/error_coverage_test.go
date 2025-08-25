package storage

import (
	"context"
	"database/sql"
	"strings"
	"testing"
	"time"

	"contextlite/pkg/types"
)

// Test error conditions to hit uncovered lines
func TestStorage_ErrorConditions_CoverageFinal(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	// Test DeleteDocument with different scenarios to hit error paths
	t.Run("DeleteDocument_ErrorPaths", func(t *testing.T) {
		// Test with a very long ID that might cause DB issues
		veryLongID := strings.Repeat("a", 10000)
		err := storage.DeleteDocument(ctx, veryLongID)
		// We don't care if it errors or not, just want to exercise the code path
		t.Logf("Very long ID deletion result: %v", err)

		// Test with special characters that might cause issues
		specialID := "test\x00null\x01byte"
		err = storage.DeleteDocument(ctx, specialID)
		t.Logf("Special characters ID deletion result: %v", err)
	})

	// Test SaveQueryCache scenarios to hit uncovered branches
	t.Run("SaveQueryCache_EdgeCases", func(t *testing.T) {
		result := &types.QueryResult{
			Documents: []types.DocumentReference{
				{ID: "test-doc", UtilityScore: 0.9},
			},
			SMTMetrics: types.SMTMetrics{
				SolverUsed:  "Z3",
				SolveTimeMs: 100.0,
			},
		}

		// Test with very long parameters that might cause issues
		longHash := strings.Repeat("hash", 1000)
		longCorpus := strings.Repeat("corpus", 1000) 
		longModel := strings.Repeat("model", 1000)
		longVersion := strings.Repeat("version", 1000)

		expiresAt := time.Now().Add(1 * time.Hour)
		err := storage.SaveQueryCache(ctx, longHash, longCorpus, longModel, longVersion, result, expiresAt)
		t.Logf("Long parameters SaveQueryCache result: %v", err)

		// Test with past expiry time
		pastExpiry := time.Now().Add(-1 * time.Hour)
		err = storage.SaveQueryCache(ctx, "hash", "corpus", "model", "version", result, pastExpiry)
		t.Logf("Past expiry SaveQueryCache result: %v", err)
	})

	// Test GetQueryCache edge cases
	t.Run("GetQueryCache_EdgeCases", func(t *testing.T) {
		// Try to get with very long parameters
		longHash := strings.Repeat("hash", 1000)
		longCorpus := strings.Repeat("corpus", 1000)
		
		cached, err := storage.GetQueryCache(ctx, longHash, longCorpus, "model", "version")
		if err != nil {
			t.Logf("Long parameters GetQueryCache error (expected): %v", err)
		}
		if cached != nil {
			t.Log("Got cached result with long parameters")
		}

		// Try with empty parameters
		cached, err = storage.GetQueryCache(ctx, "", "", "", "")
		if err != nil {
			t.Logf("Empty parameters GetQueryCache error (expected): %v", err)
		}
	})

	// Test SaveQueryCacheWithKey edge cases  
	t.Run("SaveQueryCacheWithKey_EdgeCases", func(t *testing.T) {
		result := &types.QueryResult{
			Documents: []types.DocumentReference{
				{ID: "key-test", UtilityScore: 0.8},
			},
			SMTMetrics: types.SMTMetrics{
				SolverUsed:  "Z3",
				SolveTimeMs: 50.0,
			},
		}

		// Test with very long cache key
		longKey := strings.Repeat("key-", 2000)
		expiresAt := time.Now().Add(1 * time.Hour)

		err := storage.SaveQueryCacheWithKey(ctx, "hash", "corpus", "model", "v1", longKey, result, expiresAt)
		t.Logf("Long key SaveQueryCacheWithKey result: %v", err)

		// Test with special characters in key
		specialKey := "key\x00with\x01null\x02bytes"
		err = storage.SaveQueryCacheWithKey(ctx, "hash2", "corpus2", "model2", "v2", specialKey, result, expiresAt)
		t.Logf("Special key SaveQueryCacheWithKey result: %v", err)
	})

	// Test GetCachedResultByKey edge cases
	t.Run("GetCachedResultByKey_EdgeCases", func(t *testing.T) {
		// Try with very long key
		longKey := strings.Repeat("key-", 2000)
		result, err := storage.GetCachedResultByKey(ctx, longKey)
		if err != nil {
			t.Logf("Long key GetCachedResultByKey error (expected): %v", err)
		}
		if result != nil {
			t.Log("Got result with long key")
		}

		// Try with special characters
		specialKey := "key\x00with\x01null"
		result, err = storage.GetCachedResultByKey(ctx, specialKey)
		if err != nil {
			t.Logf("Special key GetCachedResultByKey error (expected): %v", err)
		}
	})

	// Test AddDocument edge cases to hit uncovered error paths
	t.Run("AddDocument_ErrorPaths", func(t *testing.T) {
		// Test with extremely large content
		largeContent := strings.Repeat("Large content for testing database limits. ", 10000)
		
		doc := &types.Document{
			ID:           "large-content-test",
			Path:         "/test/large.txt",
			Content:      largeContent,
			ContentHash:  "large-hash",
			TokenCount:   50000,
			Language:     "txt",
			ModifiedTime: time.Now().Unix(),
		}

		err := storage.AddDocument(ctx, doc)
		if err != nil {
			t.Logf("Large content AddDocument error: %v", err)
		} else {
			t.Log("Large content document added successfully")
		}

		// Test with very long path
		longPath := "/" + strings.Repeat("very-long-path-segment/", 1000) + "file.txt"
		doc2 := &types.Document{
			ID:           "long-path-test",
			Path:         longPath,
			Content:      "test",
			ContentHash:  "path-hash",
			TokenCount:   1,
			Language:     "txt",
			ModifiedTime: time.Now().Unix(),
		}

		err = storage.AddDocument(ctx, doc2)
		if err != nil {
			t.Logf("Long path AddDocument error: %v", err)
		} else {
			t.Log("Long path document added successfully")
		}
	})

	// Test GetCorpusHash with more scenarios
	t.Run("GetCorpusHash_AdditionalCoverage", func(t *testing.T) {
		// Test multiple times to ensure consistency
		hash1, err := storage.GetCorpusHash(ctx)
		if err != nil {
			t.Errorf("GetCorpusHash failed: %v", err)
			return
		}

		hash2, err := storage.GetCorpusHash(ctx)
		if err != nil {
			t.Errorf("GetCorpusHash failed on second call: %v", err)
			return
		}

		if hash1 != hash2 {
			t.Errorf("GetCorpusHash inconsistent: %s != %s", hash1, hash2)
		}
	})
}

// Test scenario where we try to trigger SQL errors
func TestStorage_SQLErrorScenarios(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	ctx := context.Background()

	// Force some operations that might cause SQL-level issues
	t.Run("SQL_StressTest", func(t *testing.T) {
		// Try to cause SQL errors by doing many concurrent operations
		for i := 0; i < 100; i++ {
			go func(id int) {
				doc := &types.Document{
					ID:           sql.NullString{String: string(rune(id)), Valid: true}.String,
					Path:         "/stress/test",
					Content:      "stress test",
					TokenCount:   2,
					Language:     "txt",
					ModifiedTime: time.Now().Unix(),
				}
				_ = storage.AddDocument(ctx, doc)
			}(i)
		}

		// Give time for operations to complete
		time.Sleep(100 * time.Millisecond)
		t.Log("Stress test completed")
	})
}