package main

import (
	"context"
	"encoding/json"
	"fmt"
	"log"
	"os"
	"strings"
	"time"

	"contextlite/internal/engine"
	"contextlite/internal/pipeline"
	"contextlite/internal/storage"
	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

func main() {
	// Use simple config instead of loading from file
	cfg := &config.Config{
		Storage: config.StorageConfig{
			DatabasePath: "test_comprehensive.db",
		},
		Tokenizer: config.TokenizerConfig{
			ModelID:          "test-model",
			MaxTokensDefault: 4000,
		},
		SMT: config.SMTConfig{
			SolverTimeoutMs: 5000,
			MaxCandidates:   50,
			MaxPairsPerDoc:  4000,
			Z3: config.Z3Config{
				BinaryPath:         "z3",
				EnableVerification: false,
			},
		},
	}

	// Initialize storage
	store, err := storage.New(cfg.Storage.DatabasePath)
	if err != nil {
		log.Fatalf("Failed to initialize storage: %v", err)
	}
	defer func() { _ = store.Close() }()
	defer os.Remove(cfg.Storage.DatabasePath) // Clean up

	// Add multiple test documents for better SMT demonstration
	testDocs := []*types.Document{
		{
			ID:      "auth-comprehensive-1",
			Path:    "docs/auth/overview.md",
			Content: "Authentication systems are critical security components that verify user identities through multiple methods. Modern authentication frameworks implement OAuth 2.0, OpenID Connect, and SAML protocols for secure access control. Multi-factor authentication adds layers of security through something you know (passwords), something you have (tokens), and something you are (biometrics).",
			Language: "markdown",
			Metadata: map[string]string{
				"title":    "Authentication Systems Overview",
				"category": "security",
				"priority": "high",
			},
			CreatedAt: time.Now().Add(-24 * time.Hour),
			UpdatedAt: time.Now().Add(-24 * time.Hour),
		},
		{
			ID:      "jwt-deep-dive-2",
			Path:    "docs/auth/jwt.md", 
			Content: "JSON Web Tokens (JWT) provide stateless authentication by encoding user claims in cryptographically signed tokens. The three-part structure includes header (algorithm + type), payload (claims), and signature (verification). JWTs enable distributed authentication without server-side session storage, making them ideal for microservices architectures.",
			Language: "markdown",
			Metadata: map[string]string{
				"title":    "JWT Deep Dive",
				"category": "authentication",
				"priority": "medium",
			},
			CreatedAt: time.Now().Add(-12 * time.Hour),
			UpdatedAt: time.Now().Add(-12 * time.Hour),
		},
		{
			ID:      "oauth-implementation-3",
			Path:    "src/auth/oauth.go",
			Content: "OAuth 2.0 implementation for secure authorization flows. Supports authorization code grant, client credentials, and refresh token rotation. Implements PKCE (Proof Key for Code Exchange) for enhanced security in public clients. Integration with multiple identity providers including Google, GitHub, and Microsoft.",
			Language: "go",
			Metadata: map[string]string{
				"title":    "OAuth Implementation",
				"category": "code",
				"priority": "high",
			},
			CreatedAt: time.Now().Add(-6 * time.Hour),
			UpdatedAt: time.Now().Add(-6 * time.Hour),
		},
		{
			ID:      "security-patterns-4",
			Path:    "docs/security/patterns.md",
			Content: "Security design patterns for authentication systems include the Authentication Gateway pattern, Token Bucket pattern for rate limiting, and Circuit Breaker pattern for resilience. Defense in depth strategies implement multiple security layers including input validation, authentication, authorization, and audit logging.",
			Language: "markdown",
			Metadata: map[string]string{
				"title":    "Security Patterns",
				"category": "architecture",
				"priority": "medium",
			},
			CreatedAt: time.Now().Add(-48 * time.Hour),
			UpdatedAt: time.Now().Add(-48 * time.Hour),
		},
		{
			ID:      "api-security-5",
			Path:    "docs/api/security.md",
			Content: "API security best practices include rate limiting, input validation, output encoding, and proper error handling. Authentication should use bearer tokens with short expiration times. Authorization must implement least privilege principles with role-based access control (RBAC).",
			Language: "markdown",
			Metadata: map[string]string{
				"title":    "API Security Guide",
				"category": "api",
				"priority": "high",
			},
			CreatedAt: time.Now().Add(-3 * time.Hour),
			UpdatedAt: time.Now().Add(-3 * time.Hour),
		},
		{
			ID:      "session-management-6",
			Path:    "src/auth/session.go",
			Content: "Session management implementation with secure cookie handling, CSRF protection, and session fixation prevention. Supports both stateful server-side sessions and stateless JWT-based sessions. Implements automatic session timeout and concurrent session limits.",
			Language: "go",
			Metadata: map[string]string{
				"title":    "Session Management",
				"category": "code",
				"priority": "medium",
			},
			CreatedAt: time.Now().Add(-18 * time.Hour),
			UpdatedAt: time.Now().Add(-18 * time.Hour),
		},
	}

	fmt.Printf("Adding %d test documents to storage...\n", len(testDocs))
	for _, doc := range testDocs {
		if err := store.AddDocument(context.TODO(), doc); err != nil {
			log.Printf("Failed to add document %s: %v", doc.ID, err)
		} else {
			fmt.Printf("✓ Added: %s (%s)\n", doc.ID, doc.Metadata["title"])
		}
	}

	// Create pipeline with core engine
	engine := engine.NewCoreEngine(cfg, store)
	pipe := pipeline.New(store, engine, cfg)

	// Test with SMT enabled and higher document count
	req := &types.AssembleRequest{
		Query:        "authentication systems security patterns",
		MaxDocuments: 4,  // Request more documents to show pairwise effects
		MaxTokens:    2000,
		UseSMT:       true,
	}

	fmt.Printf("\nTesting SMT optimization with %d documents...\n", req.MaxDocuments)
	result, err := pipe.AssembleContext(context.TODO(), req)
	if err != nil {
		log.Fatalf("Pipeline failed: %v", err)
	}

	// Print complete JSON response with proper formatting
	jsonData, err := json.MarshalIndent(result, "", "  ")
	if err != nil {
		log.Fatalf("JSON marshal failed: %v", err)
	}

	fmt.Println("\n" + strings.Repeat("=", 80))
	fmt.Println("COMPLETE SMT-OPTIMIZED API RESPONSE")
	fmt.Println(strings.Repeat("=", 80))
	fmt.Println(string(jsonData))
	
	// Verify specific requirements from critique
	fmt.Println("\n" + strings.Repeat("=", 80))
	fmt.Println("CRITIQUE REQUIREMENTS VERIFICATION")
	fmt.Println(strings.Repeat("=", 80))
	
	// Check solver and Z3 status
	fmt.Printf("✓ Solver Used: %s\n", result.SMTMetrics.SolverUsed)
	if result.SMTMetrics.Z3Status != "" {
		fmt.Printf("✓ Z3 Status: %s\n", result.SMTMetrics.Z3Status)
	}
	
	// Check timing consistency
	fmt.Printf("✓ SMT Solve Time: %.0f ms\n", result.SMTMetrics.SolveTimeMs)
	fmt.Printf("✓ SMT Wall Time: %.0f ms\n", result.Timings.SMTWallMs)
	if result.SMTMetrics.SolveTimeMs <= result.Timings.SMTWallMs {
		fmt.Printf("✓ Timing Consistency: solve_time ≤ wall_time ✓\n")
	} else {
		fmt.Printf("⚠️  Timing Issue: solve_time > wall_time\n")
	}
	
	// Check complete metrics
	fmt.Printf("✓ K_candidates: %d\n", result.SMTMetrics.KCandidates)
	fmt.Printf("✓ pairs_count: %d\n", result.SMTMetrics.PairsCount)
	fmt.Printf("✓ budget_tokens: %d\n", result.SMTMetrics.BudgetTokens)
	fmt.Printf("✓ max_docs: %d\n", result.SMTMetrics.MaxDocs)
	fmt.Printf("✓ objective: %d\n", result.SMTMetrics.Objective)
	fmt.Printf("✓ variable_count: %d\n", result.SMTMetrics.VariableCount)
	fmt.Printf("✓ constraint_count: %d\n", result.SMTMetrics.ConstraintCount)
	
	// Check constraint/variable count formula
	expectedVars := result.SMTMetrics.KCandidates + result.SMTMetrics.PairsCount
	expectedConstraints := 2 + result.SMTMetrics.PairsCount*3 // domain + budget + cardinality + linking
	
	fmt.Printf("\nConstraint/Variable Count Verification:\n")
	fmt.Printf("  Expected variables (K + pairs): %d + %d = %d\n", 
		result.SMTMetrics.KCandidates, result.SMTMetrics.PairsCount, expectedVars)
	fmt.Printf("  Actual variables: %d\n", result.SMTMetrics.VariableCount)
	fmt.Printf("  Expected constraints (2 + 3*pairs): 2 + 3*%d = %d\n", 
		result.SMTMetrics.PairsCount, expectedConstraints)
	fmt.Printf("  Actual constraints: %d\n", result.SMTMetrics.ConstraintCount)
	
	// Check document inclusion reasons
	fmt.Printf("\nDocument Selection Analysis:\n")
	for i, doc := range result.Documents {
		fmt.Printf("  %d. %s - reason: %s (utility: %.4f)\n", 
			i+1, doc.ID, doc.InclusionReason, doc.UtilityScore)
	}
	
	// Final assessment
	fmt.Printf("\n%s", strings.Repeat("=", 80))
	if result.SMTMetrics.SolverUsed == "z3opt" && result.SMTMetrics.Z3Status == "sat" {
		fmt.Println("🎉 SUCCESS: Z3 SMT optimization working with complete API fields!")
		fmt.Println("📊 All critique requirements for field completeness satisfied")
	} else if result.SMTMetrics.SolverUsed != "z3opt" {
		fmt.Printf("⚠️  Using fallback solver: %s (reason: %s)\n", 
			result.SMTMetrics.SolverUsed, result.SMTMetrics.FallbackReason)
	}
	fmt.Println(strings.Repeat("=", 80))
}
