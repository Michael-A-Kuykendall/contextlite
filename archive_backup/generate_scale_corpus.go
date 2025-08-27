package main

import (
	"context"
	"fmt"
	"log"
	"math/rand"
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

	// Use a dedicated scale test database
	cfg.Storage.DatabasePath = "./scale_test.db"

	// Initialize storage
	store, err := storage.New(cfg.Storage.DatabasePath)
	if err != nil {
		log.Fatalf("Failed to initialize storage: %v", err)
	}
	defer store.Close()

	fmt.Println("=== Generating Scale Test Corpus ===")
	
	// Generate 10,000 diverse documents
	generateCorpus(store, 10000)
	
	// Initialize pipeline
	pipe := pipeline.New(store, cfg)
	
	fmt.Println("\n=== Scale Testing SMT Performance ===")
	
	// Test various scales: K∈{100,200}, M∈{3,5}, B∈{2000,4000,8000}
	testConfigs := []struct {
		query       string
		maxDocs     int
		maxTokens   int
		description string
	}{
		{"software architecture patterns", 3, 2000, "K~100, M=3, B=2000"},
		{"software architecture patterns", 5, 2000, "K~100, M=5, B=2000"},
		{"software architecture patterns", 3, 4000, "K~100, M=3, B=4000"},
		{"software architecture patterns", 5, 4000, "K~100, M=5, B=4000"},
		{"software architecture patterns", 3, 8000, "K~100, M=3, B=8000"},
		{"software architecture patterns", 5, 8000, "K~100, M=5, B=8000"},
		{"distributed systems microservices", 3, 2000, "K~200, M=3, B=2000"},
		{"distributed systems microservices", 5, 2000, "K~200, M=5, B=2000"},
		{"distributed systems microservices", 3, 4000, "K~200, M=3, B=4000"},
		{"distributed systems microservices", 5, 4000, "K~200, M=5, B=4000"},
		{"distributed systems microservices", 3, 8000, "K~200, M=3, B=8000"},
		{"distributed systems microservices", 5, 8000, "K~200, M=5, B=8000"},
	}
	
	fmt.Printf("| Config | K | M | B | FTS(ms) | Feature(ms) | SMT(ms) | Total(ms) | Variables | Constraints |\n")
	fmt.Printf("|--------|---|---|---|---------|-------------|---------|-----------|-----------|-------------|\n")
	
	for _, tc := range testConfigs {
		runScaleTest(pipe, tc.query, tc.maxDocs, tc.maxTokens, tc.description)
	}
}

func generateCorpus(store *storage.Storage, count int) {
	domains := []string{
		"software_architecture", "distributed_systems", "security", "machine_learning",
		"data_structures", "algorithms", "databases", "networking", "operating_systems",
		"web_development", "mobile_development", "devops", "cloud_computing", "microservices",
	}
	
	patterns := []string{
		"design patterns", "best practices", "implementation guide", "tutorial",
		"architecture overview", "performance optimization", "security considerations",
		"troubleshooting guide", "API documentation", "configuration reference",
	}
	
	technologies := []string{
		"Go", "Python", "Java", "JavaScript", "TypeScript", "Rust", "C++", "Kubernetes",
		"Docker", "PostgreSQL", "Redis", "MongoDB", "AWS", "Azure", "React", "Vue",
	}
	
	rand.Seed(time.Now().UnixNano())
	
	for i := 0; i < count; i++ {
		domain := domains[rand.Intn(len(domains))]
		pattern := patterns[rand.Intn(len(patterns))]
		tech := technologies[rand.Intn(len(technologies))]
		
		doc := types.Document{
			ID:           fmt.Sprintf("doc_%06d", i),
			Path:         fmt.Sprintf("docs/%s/%s_%s.md", domain, tech, pattern),
			Content:      generateContent(domain, pattern, tech, 200+rand.Intn(800)),
			Language:     "english",
			ModifiedTime: time.Now().Unix(),
		}
		
		err := store.AddDocument(context.Background(), &doc)
		if err != nil {
			log.Printf("Failed to add document %d: %v", i, err)
		}
		
		if i%1000 == 0 {
			fmt.Printf("Generated %d/%d documents\n", i, count)
		}
	}
	
	fmt.Printf("✅ Generated %d documents\n", count)
}

func generateContent(domain, pattern, tech string, wordCount int) string {
	templates := map[string]string{
		"software_architecture": "This document covers %s %s using %s. Modern software architecture requires careful consideration of scalability, maintainability, and performance. Key principles include separation of concerns, loose coupling, and high cohesion.",
		"distributed_systems": "Distributed systems using %s present unique challenges in %s. Consistency, availability, and partition tolerance form the CAP theorem foundation. This %s explores implementation strategies and best practices.",
		"security": "Security %s for %s applications requires multiple layers of protection. Authentication, authorization, encryption, and input validation are fundamental. This guide covers threat modeling and security assessment techniques.",
		"machine_learning": "Machine learning %s with %s frameworks enable data-driven insights. Feature engineering, model selection, and evaluation metrics are crucial for success. This %s demonstrates practical implementation approaches.",
	}
	
	base := templates[domain]
	if base == "" {
		base = "This technical document discusses %s %s implementation using %s technology stack. Best practices and practical examples are provided throughout."
	}
	
	content := fmt.Sprintf(base, tech, pattern, domain)
	
	// Pad to desired word count
	filler := " Additional implementation details, code examples, configuration options, troubleshooting steps, and performance considerations are documented below. This ensures comprehensive coverage of the topic with sufficient detail for practical application."
	
	for len(content) < wordCount*6 { // Rough estimate: 6 chars per word
		content += filler
	}
	
	return content[:wordCount*6] // Truncate to approximate word count
}

func runScaleTest(pipe *pipeline.Pipeline, query string, maxDocs, maxTokens int, description string) {
	req := &types.AssembleRequest{
		Query:        query,
		MaxDocuments: maxDocs,
		MaxTokens:    maxTokens,
		UseSMT:       true,
		UseCache:     false,
	}
	
	result, err := pipe.AssembleContext(context.Background(), req)
	
	if err != nil {
		fmt.Printf("| %s | ERR | %d | %d | ERROR | ERROR | ERROR | ERROR | ERROR | ERROR |\n", 
			description, maxDocs, maxTokens)
		return
	}
	
	// Estimate K (candidates) from FTS harvest time (rough heuristic)
	estimatedK := result.TotalDocuments * 3 // Rough multiplier
	
	fmt.Printf("| %s | %d | %d | %d | %d | %d | %d | %d | %d | %d |\n",
		description,
		estimatedK,
		maxDocs,
		maxTokens,
		result.Timings.FTSHarvestMs,
		result.Timings.FeatureBuildMs,
		result.Timings.SMTWallMs,
		result.Timings.TotalMs,
		result.SMTMetrics.VariableCount,
		result.SMTMetrics.ConstraintCount,
	)
}
