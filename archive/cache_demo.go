package main

import (
	"context"
	"fmt"
	"log"
	"time"

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

	query := "security authentication patterns"
	
	fmt.Println("=== Cache Hit/Miss Demonstration ===")
	fmt.Printf("Query: %s\n", query)
	fmt.Println()

	// First query - should be a cache miss
	fmt.Println("--- First query (cache miss expected) ---")
	start := time.Now()
	response1, err := pipe.AssembleContext(context.Background(), &types.AssembleRequest{
		Query: query,
		MaxDocuments: 3,
		Useoptimization: true,
		UseCache: true, // Enable cache
	})
	elapsed1 := time.Since(start)
	
	if err != nil {
		log.Fatalf("Failed to process first query: %v", err)
	}

	fmt.Printf("Documents found: %d\n", len(response1.Documents))
	fmt.Printf("optimization Objective: %d\n", response1.optimizationMetrics.Objective)
	fmt.Printf("optimization Variables: %d\n", response1.optimizationMetrics.VariableCount) 
	fmt.Printf("optimization Constraints: %d\n", response1.optimizationMetrics.ConstraintCount)
	fmt.Printf("optimization Solve time: %dms\n", response1.optimizationMetrics.optimizationWallMs)
	fmt.Printf("Total query time: %dms\n", elapsed1.Milliseconds())
	fmt.Printf("Cache key: %s\n", response1.CacheKey)
	fmt.Println()

	// Second query - should be a cache hit
	fmt.Println("--- Second query (cache hit expected) ---")
	start = time.Now()
	response2, err := pipe.AssembleContext(context.Background(), &types.AssembleRequest{
		Query: query,
		MaxDocuments: 3,
		Useoptimization: true,
		UseCache: true, // Enable cache
	})
	elapsed2 := time.Since(start)
	
	if err != nil {
		log.Fatalf("Failed to process second query: %v", err)
	}

	fmt.Printf("Documents found: %d\n", len(response2.Documents))
	fmt.Printf("optimization Objective: %d\n", response2.optimizationMetrics.Objective)
	fmt.Printf("optimization Variables: %d\n", response2.optimizationMetrics.VariableCount)
	fmt.Printf("optimization Constraints: %d\n", response2.optimizationMetrics.ConstraintCount)
	fmt.Printf("optimization Solve time: %dms\n", response2.optimizationMetrics.optimizationWallMs)
	fmt.Printf("Total query time: %dms\n", elapsed2.Milliseconds())
	fmt.Printf("Cache key: %s\n", response2.CacheKey)
	fmt.Println()

	// Performance comparison
	fmt.Println("--- Performance Comparison ---")
	if elapsed2 < elapsed1 {
		speedup := float64(elapsed1.Microseconds()) / float64(elapsed2.Microseconds())
		fmt.Printf("Cache hit speedup: %.1fx faster (cached in %dμs vs uncached %dμs)\n", 
			speedup, elapsed2.Microseconds(), elapsed1.Microseconds())
	} else {
		fmt.Printf("No significant speedup detected (times: %dμs vs %dμs)\n",
			elapsed2.Microseconds(), elapsed1.Microseconds())
	}

	// Verify same results
	if response1.CacheKey == response2.CacheKey {
		fmt.Println("✓ Cache keys match - same query parameters")
	} else {
		fmt.Printf("✗ Cache key mismatch: %s != %s\n", response1.CacheKey, response2.CacheKey)
	}

	if len(response1.Documents) == len(response2.Documents) {
		fmt.Printf("✓ Same number of documents returned (%d)\n", len(response1.Documents))
	} else {
		fmt.Printf("✗ Document count mismatch: %d != %d\n", len(response1.Documents), len(response2.Documents))
	}
}
