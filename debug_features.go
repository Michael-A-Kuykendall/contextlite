package main

import (
	"context"
	"fmt"
	"log"

	"contextlite/internal/features"
	"contextlite/internal/storage"
	"contextlite/pkg/config"
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

	// Get documents
	docs, err := store.SearchDocuments(ctx, "neural", 10)
	if err != nil {
		log.Fatal(err)
	}
	
	fmt.Printf("=== Found %d documents ===\n", len(docs))
	for i, doc := range docs {
		fmt.Printf("Doc %d: ID=%s, Path=%s, TokenCount=%d\n", i, doc.ID, doc.Path, doc.TokenCount)
		fmt.Printf("        Content: %.100s...\n", doc.Content)
	}

	if len(docs) == 0 {
		fmt.Println("No documents found, exiting")
		return
	}

	// Test feature extraction
	fmt.Println("\n=== Testing Feature Extraction ===")
	extractor := features.NewFeatureExtractor("", nil)
	
	scoredDocs, err := extractor.ExtractFeatures(ctx, docs, "neural")
	if err != nil {
		log.Fatal("Feature extraction failed:", err)
	}

	fmt.Printf("Extracted features for %d documents:\n", len(scoredDocs))
	for i, scored := range scoredDocs {
		fmt.Printf("Doc %d:\n", i)
		fmt.Printf("  UtilityScore:  %.4f\n", scored.UtilityScore)
		fmt.Printf("  Relevance:     %.4f\n", scored.Features.Relevance)
		fmt.Printf("  Recency:       %.4f\n", scored.Features.Recency)
		fmt.Printf("  Entanglement:  %.4f\n", scored.Features.Entanglement)
		fmt.Printf("  Prior:         %.4f\n", scored.Features.Prior)
		fmt.Printf("  Authority:     %.4f\n", scored.Features.Authority)
		fmt.Printf("  Specificity:   %.4f\n", scored.Features.Specificity)
		fmt.Printf("  Uncertainty:   %.4f\n", scored.Features.Uncertainty)
	}
}
