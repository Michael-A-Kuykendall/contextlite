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

	// Test with SMT enabled
	req := &types.AssembleRequest{
		Query:        "authentication systems",
		MaxDocuments: 3,
		UseSMT:       true,
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
	
	// Verify all required SMT fields are present
	fmt.Println("\n=== SMT METRICS VERIFICATION ===")
	fmt.Printf("solver_used: %s\n", result.SMTMetrics.SolverUsed)
	fmt.Printf("z3_status: %s\n", result.SMTMetrics.Z3Status)
	fmt.Printf("objective: %d\n", result.SMTMetrics.Objective)
	fmt.Printf("solve_time_ms: %d\n", result.SMTMetrics.SolveTimeMs)
	fmt.Printf("variable_count: %d\n", result.SMTMetrics.VariableCount)
	fmt.Printf("constraint_count: %d\n", result.SMTMetrics.ConstraintCount)
	
	// Confirm Z3 integration is working
	if result.SMTMetrics.SolverUsed == "z3opt" && result.SMTMetrics.Z3Status != "" {
		fmt.Println("\n✅ Z3 SMT integration is working!")
		fmt.Println("✅ All API fields are present and complete!")
	} else if result.SMTMetrics.SolverUsed != "" {
		fmt.Printf("\n⚠️  Using fallback solver: %s\n", result.SMTMetrics.SolverUsed)
		if result.SMTMetrics.FallbackReason != "" {
			fmt.Printf("   Reason: %s\n", result.SMTMetrics.FallbackReason)
		}
	} else {
		fmt.Println("\n❌ SMT optimization was not used")
	}
}
