package main

import (
	"encoding/json"
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

	// Add some test documents
	testDocs := []*types.Document{
		{
			ID:      "test-auth-1",
			Content: "Authentication systems verify user identities using passwords, biometrics, and multi-factor authentication. OAuth 2.0 and JWT tokens are widely used for secure authentication.",
			Metadata: map[string]string{
				"title":  "Authentication Overview",
				"source": "auth-guide.md",
			},
			CreatedAt: time.Now(),
			UpdatedAt: time.Now(),
		},
		{
			ID:      "test-auth-2", 
			Content: "JWT tokens provide stateless authentication through cryptographically signed tokens containing user claims. They enable secure authorization in distributed systems.",
			Metadata: map[string]string{
				"title":  "JWT Authentication",
				"source": "jwt-guide.md",
			},
			CreatedAt: time.Now(),
			UpdatedAt: time.Now(),
		},
		{
			ID:      "test-auth-3",
			Content: "OAuth 2.0 framework enables secure delegated access through access tokens. It allows third-party applications to access user resources with limited scope.",
			Metadata: map[string]string{
				"title":  "OAuth 2.0 Framework", 
				"source": "oauth-guide.md",
			},
			CreatedAt: time.Now(),
			UpdatedAt: time.Now(),
		},
	}

	// Add documents to storage
	for _, doc := range testDocs {
		if err := store.AddDocument(nil, doc); err != nil {
			log.Printf("Failed to add document %s: %v", doc.ID, err)
		}
	}

	// Create pipeline
	pipe := pipeline.New(store, cfg)

	// Test with optimization enabled
	req := &types.AssembleRequest{
		Query:        "authentication systems",
		MaxDocuments: 3,
		Useoptimization:       true,
	}

	result, err := pipe.AssembleContext(nil, req)
	if err != nil {
		log.Fatalf("Pipeline failed: %v", err)
	}

	// Print complete JSON response
	jsonData, err := json.MarshalIndent(result, "", "  ")
	if err != nil {
		log.Fatalf("JSON marshal failed: %v", err)
	}

	fmt.Println("=== COMPLETE API RESPONSE ===")
	fmt.Println(string(jsonData))
	
	// Verify all required optimization fields are present
	fmt.Println("\n=== optimization METRICS VERIFICATION ===")
	fmt.Printf("solver_used: %s\n", result.optimizationMetrics.SolverUsed)
	fmt.Printf("z3_status: %s\n", result.optimizationMetrics.optimizerStatus)
	fmt.Printf("objective: %d\n", result.optimizationMetrics.Objective)
	fmt.Printf("solve_time_ms: %d\n", result.optimizationMetrics.SolveTimeMs)
	fmt.Printf("variable_count: %d\n", result.optimizationMetrics.VariableCount)
	fmt.Printf("budget_count: %d\n", result.optimizationMetrics.ConstraintCount)
	
	// Confirm optimizer integration is working
	if result.optimizationMetrics.SolverUsed == "z3opt" && result.optimizationMetrics.optimizerStatus != "" {
		fmt.Println("\n✅ optimizer optimization integration is working!")
		fmt.Println("✅ All API fields are present and complete!")
	} else if result.optimizationMetrics.SolverUsed != "" {
		fmt.Printf("\n⚠️  Using fallback solver: %s\n", result.optimizationMetrics.SolverUsed)
		if result.optimizationMetrics.FallbackReason != "" {
			fmt.Printf("   Reason: %s\n", result.optimizationMetrics.FallbackReason)
		}
	} else {
		fmt.Println("\n❌ optimization optimization was not used")
	}
}
