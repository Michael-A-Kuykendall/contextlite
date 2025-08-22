package storage

import (
	"context"
	"testing"
	"time"

	"contextlite/pkg/types"
)

// Tests for wrapper functions that just delegate to other methods
func TestStorage_WrapperFunctions(t *testing.T) {
	storage, cleanup := setupTestStorage(t)
	defer cleanup()

	t.Run("InsertDocument_Wrapper", func(t *testing.T) {
		doc := types.Document{
			ID:           "insert-wrapper-test",
			Path:         "/test/insert/wrapper.go",
			Content:      "package insert",
			Language:     "go",
			TokenCount:   3,
			ModifiedTime: time.Now().Unix(),
		}

		err := storage.InsertDocument(doc)
		if err != nil {
			t.Errorf("InsertDocument should succeed: %v", err)
		}

		// Verify it was inserted by retrieving it
		ctx := context.Background()
		retrieved, err := storage.GetDocument(ctx, doc.ID)
		if err != nil {
			t.Errorf("Should be able to get inserted document: %v", err)
		} else if retrieved.ID != doc.ID {
			t.Errorf("Wrong document retrieved: expected %s, got %s", doc.ID, retrieved.ID)
		}
	})

	t.Run("UpdateDocument_Wrapper", func(t *testing.T) {
		doc := types.Document{
			ID:           "update-wrapper-test",
			Path:         "/test/update/wrapper.go",
			Content:      "package update",
			Language:     "go",
			TokenCount:   3,
			ModifiedTime: time.Now().Unix(),
		}

		err := storage.UpdateDocument(doc)
		if err != nil {
			t.Errorf("UpdateDocument should succeed: %v", err)
		}

		// Verify it was updated/inserted by retrieving it
		ctx := context.Background()
		retrieved, err := storage.GetDocument(ctx, doc.ID)
		if err != nil {
			t.Errorf("Should be able to get updated document: %v", err)
		} else if retrieved.ID != doc.ID {
			t.Errorf("Wrong document retrieved: expected %s, got %s", doc.ID, retrieved.ID)
		}
	})
}