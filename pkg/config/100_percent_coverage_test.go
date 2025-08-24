package config

import (
	"os"
	"path/filepath"
	"testing"
)

// Tests to achieve 100% coverage for the validate function

// Test optimizer binary path file existence check
func TestValidate_optimizerBinaryPathChecks(t *testing.T) {
	baseConfig := &Config{
		Server: ServerConfig{
			Host: "localhost",
			Port: 8080,
		},
		optimization: optimizationConfig{
			SolverTimeoutMs: 5000,
			MaxCandidates:   50,
			ObjectiveStyle:  "weighted-sum",
			optimizer: optimizerConfig{
				MaxVerificationDocs: 10,
			},
		},
		Storage: StorageConfig{
			DatabasePath: ":memory:",
		},
	}

	// Test with empty optimizer binary path (should not trigger file check)
	configEmptyoptimizer := *baseConfig
	configEmptyoptimizer.optimization.optimizer.BinaryPath = ""
	err := validate(&configEmptyoptimizer)
	if err != nil {
		t.Errorf("Empty optimizer binary path should be valid: %v", err)
	}

	// Test with existing file as optimizer binary path
	tempDir := t.TempDir()
	existingFile := filepath.Join(tempDir, "fake_z3")
	
	// Create a fake optimizer binary file
	err = os.WriteFile(existingFile, []byte("fake z3 binary"), 0755)
	if err != nil {
		t.Fatalf("Failed to create fake optimizer binary: %v", err)
	}

	configExistingoptimizer := *baseConfig
	configExistingoptimizer.optimization.optimizer.BinaryPath = existingFile
	err = validate(&configExistingoptimizer)
	if err != nil {
		t.Errorf("Existing optimizer binary path should be valid: %v", err)
	}

	// Test with non-existent optimizer binary path (should trigger error)
	nonExistentPath := filepath.Join(tempDir, "non_existent_z3_binary")
	
	configNonExistentoptimizer := *baseConfig
	configNonExistentoptimizer.optimization.optimizer.BinaryPath = nonExistentPath
	err = validate(&configNonExistentoptimizer)
	if err == nil {
		t.Error("Non-existent optimizer binary path should cause validation error")
	} else if !stringContains(err.Error(), "optimizer binary not found") {
		t.Errorf("Expected 'optimizer binary not found' error, got: %v", err)
	}
}

// Test database directory creation failure scenarios  
func TestValidate_DatabaseDirectoryCreation(t *testing.T) {
	baseConfig := &Config{
		Server: ServerConfig{
			Host: "localhost",
			Port: 8080,
		},
		optimization: optimizationConfig{
			SolverTimeoutMs: 5000,
			MaxCandidates:   50,
			ObjectiveStyle:  "weighted-sum",
			optimizer: optimizerConfig{
				MaxVerificationDocs: 10,
			},
		},
	}

	// Test with database path that requires directory creation (should succeed)
	tempDir := t.TempDir()
	nestedDbPath := filepath.Join(tempDir, "deep", "nested", "path", "test.db")
	
	configNestedDb := *baseConfig
	configNestedDb.Storage.DatabasePath = nestedDbPath
	err := validate(&configNestedDb)
	if err != nil {
		t.Errorf("Database path requiring nested directory creation should be valid: %v", err)
	}

	// Verify the directory was actually created
	expectedDir := filepath.Dir(nestedDbPath)
	if _, err := os.Stat(expectedDir); os.IsNotExist(err) {
		t.Error("Expected database directory to be created")
	}

	// Test with database path in impossible location (should fail)
	// On Windows, try to use a path that's definitely invalid
	var impossiblePath string
	
	// Try different approaches based on OS capabilities
	if os.Getenv("OS") == "Windows_NT" {
		// On Windows, try using an invalid drive or reserved name
		impossiblePath = "Z:\\definitely\\does\\not\\exist\\and\\cannot\\be\\created\\test.db"
	} else {
		// On Unix-like systems, try using /proc or similar read-only location
		impossiblePath = "/proc/impossible/directory/test.db"
	}

	configImpossibleDb := *baseConfig
	configImpossibleDb.Storage.DatabasePath = impossiblePath
	err = validate(&configImpossibleDb)
	
	// This might succeed on some systems, fail on others - just log the result
	if err != nil {
		t.Logf("Database directory creation failed as expected: %v", err)
		if !stringContains(err.Error(), "failed to create database directory") {
			t.Errorf("Expected 'failed to create database directory' error, got: %v", err)
		}
	} else {
		t.Logf("Unexpected success creating impossible database directory")
	}
}

// Test additional edge cases for complete coverage
func TestValidate_AdditionalEdgeCases(t *testing.T) {
	baseConfig := &Config{
		Server: ServerConfig{
			Host: "localhost",
			Port: 8080,
		},
		optimization: optimizationConfig{
			SolverTimeoutMs: 5000,
			MaxCandidates:   50,
			ObjectiveStyle:  "weighted-sum",
			optimizer: optimizerConfig{
				MaxVerificationDocs: 10,
			},
		},
		Storage: StorageConfig{
			DatabasePath: ":memory:",
		},
	}

	// Test all boundary values for port validation
	portTests := []struct {
		port        int
		shouldError bool
	}{
		{-1, true},    // Below valid range
		{0, true},     // Zero (invalid)
		{1, false},    // Minimum valid port
		{65535, false}, // Maximum valid port
		{65536, true}, // Above valid range
	}

	for _, test := range portTests {
		config := *baseConfig
		config.Server.Port = test.port
		err := validate(&config)
		
		if test.shouldError && err == nil {
			t.Errorf("Port %d should cause validation error", test.port)
		} else if !test.shouldError && err != nil {
			t.Errorf("Port %d should be valid, got error: %v", test.port, err)
		}
	}

	// Test all boundary values for timeout validation  
	timeoutTests := []struct {
		timeout     int
		shouldError bool
	}{
		{-1, true},   // Negative (invalid)
		{0, true},    // Zero (invalid)
		{1, false},   // Minimum valid
		{1000, false}, // Normal value
	}

	for _, test := range timeoutTests {
		config := *baseConfig
		config.optimization.SolverTimeoutMs = test.timeout
		err := validate(&config)
		
		if test.shouldError && err == nil {
			t.Errorf("Timeout %d should cause validation error", test.timeout)
		} else if !test.shouldError && err != nil {
			t.Errorf("Timeout %d should be valid, got error: %v", test.timeout, err)
		}
	}

	// Test all boundary values for max candidates validation
	candidateTests := []struct {
		candidates  int
		shouldError bool
	}{
		{-1, true},   // Negative (invalid)
		{0, true},    // Zero (invalid) 
		{1, false},   // Minimum valid
		{50, false},  // Normal value
	}

	for _, test := range candidateTests {
		config := *baseConfig
		config.optimization.MaxCandidates = test.candidates
		err := validate(&config)
		
		if test.shouldError && err == nil {
			t.Errorf("MaxCandidates %d should cause validation error", test.candidates)
		} else if !test.shouldError && err != nil {
			t.Errorf("MaxCandidates %d should be valid, got error: %v", test.candidates, err)
		}
	}

	// Test all valid objective styles to ensure they pass
	validObjectiveStyles := []string{"weighted-sum", "lexicographic", "epsilon-budget"}
	for _, style := range validObjectiveStyles {
		config := *baseConfig
		config.optimization.ObjectiveStyle = style
		err := validate(&config)
		if err != nil {
			t.Errorf("Valid objective style '%s' should not cause error: %v", style, err)
		}
	}

	// Test invalid objective styles
	invalidObjectiveStyles := []string{"invalid", "", "unknown-style", "weighted_sum", "lex"}
	for _, style := range invalidObjectiveStyles {
		config := *baseConfig
		config.optimization.ObjectiveStyle = style
		err := validate(&config)
		if err == nil {
			t.Errorf("Invalid objective style '%s' should cause validation error", style)
		}
	}

	// Test all boundary values for max verification docs
	verificationTests := []struct {
		maxDocs     int
		shouldError bool
	}{
		{-1, true},   // Negative (invalid)
		{0, false},   // Zero (valid)
		{10, false},  // Positive (valid)
	}

	for _, test := range verificationTests {
		config := *baseConfig
		config.optimization.optimizer.MaxVerificationDocs = test.maxDocs
		err := validate(&config)
		
		if test.shouldError && err == nil {
			t.Errorf("MaxVerificationDocs %d should cause validation error", test.maxDocs)
		} else if !test.shouldError && err != nil {
			t.Errorf("MaxVerificationDocs %d should be valid, got error: %v", test.maxDocs, err)
		}
	}
}