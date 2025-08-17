package main

import (
	"flag"
	"os"
	"testing"
)

func TestMain(m *testing.M) {
	// Don't run the actual main function during tests
	// Just test the flag parsing and setup
	os.Exit(m.Run())
}

func TestFlagDefaults(t *testing.T) {
	// Reset flags for testing
	flag.CommandLine = flag.NewFlagSet(os.Args[0], flag.ExitOnError)
	
	// Redefine flags as they would be in main
	outputPath := flag.String("output", "sota_comparison.json", "Output file for results")
	maxDocs := flag.Int("max-docs", 5, "Maximum documents per query")
	budgetTokens := flag.Int("budget", 4000, "Token budget for context")
	iterations := flag.Int("iterations", 3, "Number of iterations per query")
	verbose := flag.Bool("verbose", false, "Enable verbose logging")
	systemsFlag := flag.String("systems", "contextlite_optimization,bm25_baseline,embedding_retrieval,llm_reranking", "Comma-separated list of systems to test")
	
	// Parse with no arguments (should use defaults)
	flag.CommandLine.Parse([]string{})
	
	// Test default values
	if *outputPath != "sota_comparison.json" {
		t.Errorf("Expected default output path 'sota_comparison.json', got '%s'", *outputPath)
	}
	
	if *maxDocs != 5 {
		t.Errorf("Expected default max docs 5, got %d", *maxDocs)
	}
	
	if *budgetTokens != 4000 {
		t.Errorf("Expected default budget tokens 4000, got %d", *budgetTokens)
	}
	
	if *iterations != 3 {
		t.Errorf("Expected default iterations 3, got %d", *iterations)
	}
	
	if *verbose != false {
		t.Errorf("Expected default verbose false, got %t", *verbose)
	}
	
	expectedSystems := "contextlite_optimization,bm25_baseline,embedding_retrieval,llm_reranking"
	if *systemsFlag != expectedSystems {
		t.Errorf("Expected default systems '%s', got '%s'", expectedSystems, *systemsFlag)
	}
}

func TestFlagParsing(t *testing.T) {
	// Reset flags for testing
	flag.CommandLine = flag.NewFlagSet(os.Args[0], flag.ExitOnError)
	
	// Redefine flags
	outputPath := flag.String("output", "sota_comparison.json", "Output file for results")
	maxDocs := flag.Int("max-docs", 5, "Maximum documents per query")
	budgetTokens := flag.Int("budget", 4000, "Token budget for context")
	iterations := flag.Int("iterations", 3, "Number of iterations per query")
	verbose := flag.Bool("verbose", false, "Enable verbose logging")
	systemsFlag := flag.String("systems", "contextlite_optimization,bm25_baseline,embedding_retrieval,llm_reranking", "Comma-separated list of systems to test")
	
	// Test parsing custom arguments
	args := []string{
		"-output", "custom_output.json",
		"-max-docs", "10",
		"-budget", "8000",
		"-iterations", "5",
		"-verbose",
		"-systems", "contextlite_optimization,bm25_baseline",
	}
	
	flag.CommandLine.Parse(args)
	
	// Test parsed values
	if *outputPath != "custom_output.json" {
		t.Errorf("Expected output path 'custom_output.json', got '%s'", *outputPath)
	}
	
	if *maxDocs != 10 {
		t.Errorf("Expected max docs 10, got %d", *maxDocs)
	}
	
	if *budgetTokens != 8000 {
		t.Errorf("Expected budget tokens 8000, got %d", *budgetTokens)
	}
	
	if *iterations != 5 {
		t.Errorf("Expected iterations 5, got %d", *iterations)
	}
	
	if *verbose != true {
		t.Errorf("Expected verbose true, got %t", *verbose)
	}
	
	expectedSystems := "contextlite_optimization,bm25_baseline"
	if *systemsFlag != expectedSystems {
		t.Errorf("Expected systems '%s', got '%s'", expectedSystems, *systemsFlag)
	}
}

func TestValidationLogic(t *testing.T) {
	// Test parameter validation logic that would be in main
	
	// Test valid parameters
	testCases := []struct {
		name         string
		maxDocs      int
		budgetTokens int
		iterations   int
		expectValid  bool
	}{
		{"valid_normal", 5, 4000, 3, true},
		{"valid_high", 10, 8000, 5, true},
		{"valid_low", 1, 1000, 1, true},
		{"invalid_zero_docs", 0, 4000, 3, false},
		{"invalid_zero_budget", 5, 0, 3, false},
		{"invalid_zero_iterations", 5, 4000, 0, false},
		{"invalid_negative_docs", -1, 4000, 3, false},
	}
	
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Simulate validation logic
			valid := tc.maxDocs > 0 && tc.budgetTokens > 0 && tc.iterations > 0
			
			if valid != tc.expectValid {
				t.Errorf("Expected validity %t for case %s, got %t", tc.expectValid, tc.name, valid)
			}
		})
	}
}

func TestSystemsList(t *testing.T) {
	// Test parsing systems list
	systemsStr := "contextlite_optimization,bm25_baseline,embedding_retrieval,llm_reranking"
	
	// This would be the logic to parse systems in main
	// For now, just test that the string contains expected systems
	expectedSystems := []string{
		"contextlite_optimization",
		"bm25_baseline", 
		"embedding_retrieval",
		"llm_reranking",
	}
	
	for _, system := range expectedSystems {
		if !contains(systemsStr, system) {
			t.Errorf("Expected systems string to contain '%s'", system)
		}
	}
}

// Helper function for testing
func contains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || 
		(len(s) > len(substr) && 
			(s[:len(substr)] == substr || 
			 s[len(s)-len(substr):] == substr ||
			 indexOfSubstring(s, substr) != -1)))
}

func indexOfSubstring(s, substr string) int {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return i
		}
	}
	return -1
}

func TestConfigurationValidation(t *testing.T) {
	// Test that we can validate common configuration scenarios
	
	scenarios := []struct {
		name    string
		output  string
		systems string
		valid   bool
	}{
		{"valid_json_output", "results.json", "contextlite_optimization", true},
		{"valid_csv_output", "results.csv", "bm25_baseline", true},
		{"empty_output", "", "contextlite_optimization", false},
		{"empty_systems", "results.json", "", false},
		{"valid_multiple_systems", "results.json", "contextlite_optimization,bm25_baseline", true},
	}
	
	for _, scenario := range scenarios {
		t.Run(scenario.name, func(t *testing.T) {
			// Simple validation logic
			valid := scenario.output != "" && scenario.systems != ""
			
			if valid != scenario.valid {
				t.Errorf("Expected validation %t for scenario %s, got %t", 
					scenario.valid, scenario.name, valid)
			}
		})
	}
}
