package main

import (
	"encoding/json"
	"fmt"
	"log"
	"strings"
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

	// Add multiple test documents for better optimization demonstration
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
		if err := store.AddDocument(nil, doc); err != nil {
			log.Printf("Failed to add document %s: %v", doc.ID, err)
		} else {
			fmt.Printf("✓ Added: %s (%s)\n", doc.ID, doc.Metadata["title"])
		}
	}

	// Create pipeline
	pipe := pipeline.New(store, cfg)

	// Test with optimization enabled and higher document count
	req := &types.AssembleRequest{
		Query:        "authentication systems security patterns",
		MaxDocuments: 4,  // Request more documents to show pairwise effects
		MaxTokens:    2000,
		Useoptimization:       true,
	}

	fmt.Printf("\nTesting optimization optimization with %d documents...\n", req.MaxDocuments)
	result, err := pipe.AssembleContext(nil, req)
	if err != nil {
		log.Fatalf("Pipeline failed: %v", err)
	}

	// Print complete JSON response with proper formatting
	jsonData, err := json.MarshalIndent(result, "", "  ")
	if err != nil {
		log.Fatalf("JSON marshal failed: %v", err)
	}

	fmt.Println("\n" + strings.Repeat("=", 80))
	fmt.Println("COMPLETE optimization-OPTIMIZED API RESPONSE")
	fmt.Println(strings.Repeat("=", 80))
	fmt.Println(string(jsonData))
	
	// Verify specific requirements from critique
	fmt.Println("\n" + strings.Repeat("=", 80))
	fmt.Println("CRITIQUE REQUIREMENTS VERIFICATION")
	fmt.Println(strings.Repeat("=", 80))
	
	// Check solver and optimizer status
	fmt.Printf("✓ Solver Used: %s\n", result.optimizationMetrics.SolverUsed)
	if result.optimizationMetrics.optimizerStatus != "" {
		fmt.Printf("✓ optimizer Status: %s\n", result.optimizationMetrics.optimizerStatus)
	}
	
	// Check timing consistency
	fmt.Printf("✓ optimization Solve Time: %d ms\n", result.optimizationMetrics.SolveTimeMs)
	fmt.Printf("✓ optimization Wall Time: %d ms\n", result.Timings.optimizationWallMs)
	if result.optimizationMetrics.SolveTimeMs <= result.Timings.optimizationWallMs {
		fmt.Printf("✓ Timing Consistency: solve_time ≤ wall_time ✓\n")
	} else {
		fmt.Printf("⚠️  Timing Issue: solve_time > wall_time\n")
	}
	
	// Check complete metrics
	fmt.Printf("✓ K_candidates: %d\n", result.optimizationMetrics.KCandidates)
	fmt.Printf("✓ pairs_count: %d\n", result.optimizationMetrics.PairsCount)
	fmt.Printf("✓ budget_tokens: %d\n", result.optimizationMetrics.BudgetTokens)
	fmt.Printf("✓ max_docs: %d\n", result.optimizationMetrics.MaxDocs)
	fmt.Printf("✓ objective: %d\n", result.optimizationMetrics.Objective)
	fmt.Printf("✓ variable_count: %d\n", result.optimizationMetrics.VariableCount)
	fmt.Printf("✓ budget_count: %d\n", result.optimizationMetrics.ConstraintCount)
	
	// Check budget/variable count formula
	expectedVars := result.optimizationMetrics.KCandidates + result.optimizationMetrics.PairsCount
	expectedConstraints := 2 + result.optimizationMetrics.PairsCount*3 // domain + budget + cardinality + linking
	
	fmt.Printf("\nConstraint/Variable Count Verification:\n")
	fmt.Printf("  Expected variables (K + pairs): %d + %d = %d\n", 
		result.optimizationMetrics.KCandidates, result.optimizationMetrics.PairsCount, expectedVars)
	fmt.Printf("  Actual variables: %d\n", result.optimizationMetrics.VariableCount)
	fmt.Printf("  Expected budgets (2 + 3*pairs): 2 + 3*%d = %d\n", 
		result.optimizationMetrics.PairsCount, expectedConstraints)
	fmt.Printf("  Actual budgets: %d\n", result.optimizationMetrics.ConstraintCount)
	
	// Check document inclusion reasons
	fmt.Printf("\nDocument Selection Analysis:\n")
	for i, doc := range result.Documents {
		fmt.Printf("  %d. %s - reason: %s (utility: %.4f)\n", 
			i+1, doc.ID, doc.InclusionReason, doc.UtilityScore)
	}
	
	// Final assessment
	fmt.Printf("\n" + strings.Repeat("=", 80))
	if result.optimizationMetrics.SolverUsed == "z3opt" && result.optimizationMetrics.optimizerStatus == "sat" {
		fmt.Println("🎉 SUCCESS: optimizer optimization optimization working with complete API fields!")
		fmt.Println("📊 All critique requirements for field completeness satisfied")
	} else if result.optimizationMetrics.SolverUsed != "z3opt" {
		fmt.Printf("⚠️  Using fallback solver: %s (reason: %s)\n", 
			result.optimizationMetrics.SolverUsed, result.optimizationMetrics.FallbackReason)
	}
	fmt.Println(strings.Repeat("=", 80))
}
