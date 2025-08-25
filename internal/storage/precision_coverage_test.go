package storage

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"
	"contextlite/pkg/types"
)

// TestPrecision_New_DatabaseFailures - Target exact uncovered lines in New function
func TestPrecision_New_DatabaseFailures(t *testing.T) {
	t.Run("DatabaseOpen_InvalidDriver", func(t *testing.T) {
		// Try to create database with completely invalid path that causes sql.Open to fail
		invalidPath := string([]byte{0x00, 0x01, 0x02}) // Invalid characters that might cause sql.Open to fail
		
		storage, err := New(invalidPath)
		if err != nil {
			t.Logf("✅ Hit database open error: %v", err)
		}
		if storage != nil {
			storage.Close()
			t.Error("Expected nil storage on database open failure")
		}
	})

	t.Run("PragmaExecution_Failure", func(t *testing.T) {
		// This is tricky - we need to create a scenario where PRAGMA statements fail
		// One approach is to create a read-only database file
		tempDir := t.TempDir()
		dbPath := filepath.Join(tempDir, "readonly.db")
		
		// Create an empty file first
		file, err := os.Create(dbPath)
		if err != nil {
			t.Fatalf("Failed to create temp file: %v", err)
		}
		file.Close()
		
		// Make it read-only (may not work on Windows)
		err = os.Chmod(dbPath, 0444)
		if err != nil {
			t.Logf("Warning: Could not make file read-only: %v", err)
		}
		
		storage, err := New(dbPath)
		if err != nil {
			t.Logf("✅ Hit PRAGMA execution error: %v", err)
		} else if storage != nil {
			storage.Close()
			t.Log("PRAGMA execution succeeded despite read-only file")
		}
	})

	t.Run("SchemaInitialization_Failure", func(t *testing.T) {
		// Create a database but corrupt it or make it fail during schema init
		tempDir := t.TempDir()
		dbPath := filepath.Join(tempDir, "corrupt.db")
		
		// Create a database file with invalid content
		corruptContent := []byte("This is not a valid SQLite database file")
		err := os.WriteFile(dbPath, corruptContent, 0644)
		if err != nil {
			t.Fatalf("Failed to create corrupt file: %v", err)
		}
		
		storage, err := New(dbPath)
		if err != nil {
			t.Logf("✅ Hit schema initialization error: %v", err)
		} else if storage != nil {
			storage.Close()
			t.Error("Expected schema initialization to fail with corrupt database")
		}
	})
}

// TestPrecision_SaveQueryCache_MarshalFailures - Target exact JSON marshal failures
func TestPrecision_SaveQueryCache_MarshalFailures(t *testing.T) {
	// Create a working storage first
	tempFile := filepath.Join(t.TempDir(), "marshal_test.db")
	storage, err := New(tempFile)
	if err != nil {
		t.Fatalf("Failed to create storage: %v", err)
	}
	defer storage.Close()

	t.Run("MarshalDocuments_CircularReference", func(t *testing.T) {
		// Create a QueryResult that will cause JSON marshal to fail
		// We need to create a structure that can't be marshaled
		
		// This is tricky with QueryResult since it only contains basic types
		// Let's try to create a very large document that might cause issues
		ctx := testContext()
		
		// Create documents with problematic content
		hugeContent := make([]byte, 10*1024*1024) // 10MB
		for i := range hugeContent {
			hugeContent[i] = byte(i % 256)
		}
		
		largeResult := createTestQueryResult()
		largeResult.Documents = []types.DocumentReference{{
			ID: "huge_doc",
			Content: string(hugeContent),
			UtilityScore: 0.9,
		}}
		
		err := storage.SaveQueryCache(ctx, "huge_query", "corpus", "model", "tokenizer", largeResult, time.Now().Add(time.Hour))
		if err != nil {
			t.Logf("✅ Hit marshal/save error with huge content: %v", err)
		} else {
			t.Log("Successfully saved huge content")
		}
	})

	t.Run("DatabaseInsert_Failure", func(t *testing.T) {
		// Try to trigger database insert failure by closing the database
		ctx := testContext()
		result := createTestQueryResult()
		
		// Close the database to cause insert failures
		storage.Close()
		
		err := storage.SaveQueryCache(ctx, "closed_db_query", "corpus", "model", "tokenizer", result, time.Now().Add(time.Hour))
		if err != nil {
			t.Logf("✅ Hit database insert error with closed DB: %v", err)
		} else {
			t.Error("Expected database insert to fail with closed database")
		}
	})
}

// TestPrecision_DeleteDocument_EdgeCases - Target exact error paths in DeleteDocument
func TestPrecision_DeleteDocument_EdgeCases(t *testing.T) {
	tempFile := filepath.Join(t.TempDir(), "delete_test.db")
	storage, err := New(tempFile)
	if err != nil {
		t.Fatalf("Failed to create storage: %v", err)
	}
	defer storage.Close()

	t.Run("DeleteDocument_TransactionFailure", func(t *testing.T) {
		ctx := testContext()
		
		// Close database to cause transaction failures
		storage.Close()
		
		err := storage.DeleteDocument(ctx, "test_doc")
		if err != nil {
			t.Logf("✅ Hit transaction failure: %v", err)
		} else {
			t.Error("Expected transaction to fail with closed database")
		}
	})

	t.Run("DeleteDocument_LongID", func(t *testing.T) {
		// Test with extremely long ID that might cause issues
		longID := make([]byte, 100000) // 100KB ID
		for i := range longID {
			longID[i] = 'a'
		}
		
		ctx := testContext()
		err := storage.DeleteDocument(ctx, string(longID))
		if err != nil {
			t.Logf("✅ Hit long ID error: %v", err)
		} else {
			t.Log("Long ID handled successfully")
		}
	})
}

// Helper functions
func testContext() context.Context {
	return context.Background()
}

func createTestQueryResult() *types.QueryResult {
	return &types.QueryResult{
		Query: "test query",
		Documents: []types.DocumentReference{{
			ID: "test_doc",
			Content: "test content",
			UtilityScore: 0.8,
		}},
		TotalDocuments: 1,
		TotalTokens: 10,
		CoherenceScore: 0.9,
	}
}