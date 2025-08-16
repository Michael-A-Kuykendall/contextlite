package main

import (
	"context"
	"fmt"
	"log"

	"contextlite/internal/storage"
	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

func main() {
	// Load config
	cfg, err := config.Load("configs/default.yaml")
	if err != nil {
		log.Fatal(err)
	}

	// Initialize storage
	store, err := storage.New(cfg.Storage.DatabasePath)
	if err != nil {
		log.Fatal(err)
	}
	defer store.Close()

	ctx := context.Background()

	// Test direct search
	fmt.Println("=== Testing direct SearchDocuments ===")
	docs, err := store.SearchDocuments(ctx, "neural", 10)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Printf("Found %d documents:\n", len(docs))
	for i, doc := range docs {
		fmt.Printf("  %d. ID: %s, Path: %s, Content: %.50s...\n", i+1, doc.ID, doc.Path, doc.Content)
	}

	// Test with assemble request structure
	fmt.Println("\n=== Testing AssembleRequest logic ===")
	req := &types.AssembleRequest{
		Query:        "neural",
		MaxTokens:    1000,
		MaxDocuments: 3,
		UseSMT:       true,
		UseCache:     true,
	}

	// Check how many candidates we get
	candidates, err := store.SearchDocuments(ctx, req.Query, 200)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Printf("Candidates found: %d\n", len(candidates))

	// Check workspace filtering (empty workspace should match all)
	filtered := candidates
	if req.WorkspacePath != "" {
		fmt.Printf("Filtering by workspace: %s\n", req.WorkspacePath)
		temp := make([]types.Document, 0, len(candidates))
		for _, doc := range candidates {
			if len(doc.Path) >= len(req.WorkspacePath) && doc.Path[:len(req.WorkspacePath)] == req.WorkspacePath {
				temp = append(temp, doc)
			}
		}
		filtered = temp
	}
	fmt.Printf("After workspace filtering: %d\n", len(filtered))

	// Test feature extraction
	fmt.Println("\n=== Testing Feature Extraction ===")
	if len(filtered) > 0 {
		// Import needed for feature extraction
		// We'll test this directly instead of through the pipeline
		fmt.Printf("Would extract features for %d documents\n", len(filtered))
		
		// Let's test the basic pipeline call
		fmt.Println("\n=== Testing Full Pipeline Call ===")
		// Since we can't import the pipeline easily, let's just verify the storage methods work
		
		// Test GetWorkspaceWeights
		weights, err := store.GetWorkspaceWeights(ctx, "")
		if err != nil {
			fmt.Printf("GetWorkspaceWeights error (expected): %v\n", err)
		} else {
			fmt.Printf("GetWorkspaceWeights success: %+v\n", weights)
		}
	}
}
