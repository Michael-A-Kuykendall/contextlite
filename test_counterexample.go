package main

import (
	"context"
	"fmt"
	"log"

	"contextlite/internal/pipeline"
	"contextlite/internal/storage"
	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

func main() {
	// Load config
	cfg, err := config.Load("configs/default.yaml")
	if err != nil {
		log.Fatalf("Failed to load config: %v", err)
	}

	// Initialize storage
	store, err := storage.New(cfg.Storage.DatabasePath)
	if err != nil {
		log.Fatalf("Failed to initialize storage: %v", err)
	}
	defer store.Close()

	// Initialize pipeline
	pipe := pipeline.New(store, cfg)

	fmt.Println("=== Pairwise Counterexample: Max Results = 3 (Unconstrained) ===")
	
	// Test with maxDocuments=3 to allow all documents
	response, err := pipe.AssembleContext(context.Background(), &types.AssembleRequest{
		Query: "security authentication",
		MaxDocuments: 3,
		UseSMT: true,
		UseCache: false,
	})
	
	if err != nil {
		log.Fatalf("Failed to process query: %v", err)
	}

	fmt.Printf("Query: %s\n", response.Query)
	fmt.Printf("Documents found: %d\n", len(response.Documents))
	fmt.Printf("SMT Objective: %d\n", response.SMTMetrics.Objective)
	fmt.Printf("SMT Variables: %d\n", response.SMTMetrics.VariableCount)
	fmt.Printf("SMT Constraints: %d\n", response.SMTMetrics.ConstraintCount)
	fmt.Printf("SMT Solve time: %dms\n", response.SMTMetrics.SMTWallMs)
	
	fmt.Println("\nSelected documents:")
	for i, doc := range response.Documents {
		fmt.Printf("  %d. %s (Utility: %.4f, Relevance: %.4f)\n", i+1, doc.ID, doc.UtilityScore, doc.RelevanceScore)
	}
}
