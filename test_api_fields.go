package main

import (
	"encoding/json"
	"fmt"
	"log"

	"contextlite/internal/pipeline"
	"contextlite/internal/smt"
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

	// Create pipeline
	smtSolver := smt.New(cfg)
	pipe := pipeline.New(store, smtSolver, cfg)

	// Test with SMT enabled
	req := &types.ContextRequest{
		Query:      "authentication systems",
		MaxResults: 3,
		UseSMT:     true,
	}

	result, err := pipe.Process(req)
	if err != nil {
		log.Fatalf("Pipeline failed: %v", err)
	}

	// Print JSON response to verify all fields are present
	jsonData, err := json.MarshalIndent(result, "", "  ")
	if err != nil {
		log.Fatalf("JSON marshal failed: %v", err)
	}

	fmt.Println("Complete API Response:")
	fmt.Println(string(jsonData))

	// Specifically check SMT metrics
	fmt.Println("\nSMT Metrics specifically:")
	smtJson, _ := json.MarshalIndent(result.SMTMetrics, "", "  ")
	fmt.Println(string(smtJson))
}
