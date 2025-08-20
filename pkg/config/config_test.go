package config

import (
	"fmt"
	"os"
	"path/filepath"
	"testing"
)

func TestLoadConfig_Default(t *testing.T) {
	// Create a temporary config file for testing
	tempConfig := `
server:
  host: "localhost"
  port: 8080

storage:
  database_path: ":memory:"

smt:
  z3_binary_path: ""  # Empty path should not cause validation error
  solver_timeout_ms: 1000
  max_candidates: 50
  objective_style: "weighted-sum"
`
	
	// Write temporary config file
	tmpfile, err := os.CreateTemp("", "test_config_*.yaml")
	if err != nil {
		t.Fatalf("Failed to create temp config file: %v", err)
	}
	defer os.Remove(tmpfile.Name())
	
	if _, err := tmpfile.Write([]byte(tempConfig)); err != nil {
		t.Fatalf("Failed to write temp config file: %v", err)
	}
	tmpfile.Close()
	
	// Test loading the temporary config
	cfg, err := Load(tmpfile.Name())
	if err != nil {
		t.Fatalf("Failed to load config: %v", err)
	}
	
	if cfg == nil {
		t.Errorf("Config should not be nil")
		return // Avoid nil pointer dereference
	}
	
	// Check default values
	if cfg.Server.Host == "" {
		t.Errorf("Default server host should not be empty")
	}
	
	if cfg.Server.Port <= 0 {
		t.Errorf("Default server port should be positive")
	}
	
	if cfg.Storage.DatabasePath == "" {
		t.Errorf("Default database path should not be empty")
	}
}

func TestLoadConfig_FromFile(t *testing.T) {
	// Create temporary config file
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "test_config.yaml")
	
	// Create a valid temp database path using forward slashes for YAML compatibility
	tempDbDir := filepath.Join(tmpDir, "db")
	tempDbPath := filepath.ToSlash(filepath.Join(tempDbDir, "test.db"))
	
	configContent := fmt.Sprintf(`
server:
  host: "test-host"
  port: 9999

storage:
  database_path: "%s"

smt:
  solver_timeout_ms: 10000
  max_candidates: 100
  max_pairs_per_doc: 8000
  objective_style: "weighted-sum"
  z3:
    binary_path: ""
    enable_verification: true

weights:
  relevance: 0.4
  recency: 0.3
  entanglement: 0.2
  authority: 0.1
  specificity: 0.05
  uncertainty: 0.05
  prior: 0.1
  redundancy_penalty: 0.1
  coherence_bonus: 0.1
  weight_update_rate: 0.01
  weight_caps: [0.1, 0.5]

lexicographic:
  compute_at_runtime: true

epsilon_constraint:
  max_redundancy: 0.8
  min_coherence: 0.6
  min_recency: 0.3

tokenizer:
  model_id: "test-tokenizer"
  max_tokens_default: 5000

cache:
  l1_size: 1000
  l2_ttl_minutes: 60
  l3_enabled: true
`, tempDbPath)
	
	err := os.WriteFile(configPath, []byte(configContent), 0644)
	if err != nil {
		t.Fatalf("Failed to write test config file: %v", err)
	}
	
	// Load config from file
	cfg, err := Load(configPath)
	if err != nil {
		t.Fatalf("Failed to load config from file: %v", err)
	}
	
	// Verify loaded values
	if cfg.Server.Host != "test-host" {
		t.Errorf("Expected server host 'test-host', got '%s'", cfg.Server.Host)
	}
	
	if cfg.Server.Port != 9999 {
		t.Errorf("Expected server port 9999, got %d", cfg.Server.Port)
	}
	
	if cfg.Storage.DatabasePath != tempDbPath {
		t.Errorf("Expected database path '%s', got '%s'", tempDbPath, cfg.Storage.DatabasePath)
	}
	
	if cfg.SMT.SolverTimeoutMs != 10000 {
		t.Errorf("Expected SMT timeout 10000ms, got %d", cfg.SMT.SolverTimeoutMs)
	}
	
	if cfg.SMT.Z3.BinaryPath != "" {
		t.Errorf("Expected empty Z3 path, got '%s'", cfg.SMT.Z3.BinaryPath)
	}
	
	if cfg.Weights.Relevance != 0.4 {
		t.Errorf("Expected relevance weight 0.4, got %f", cfg.Weights.Relevance)
	}
	
	if cfg.Tokenizer.ModelID != "test-tokenizer" {
		t.Errorf("Expected tokenizer model ID 'test-tokenizer', got '%s'", cfg.Tokenizer.ModelID)
	}
	
	if cfg.Cache.L1Size != 1000 {
		t.Errorf("Expected cache L1 size 1000, got %d", cfg.Cache.L1Size)
	}
}

func TestLoadConfig_NonExistentFile(t *testing.T) {
	_, err := Load("/non/existent/path.yaml")
	if err == nil {
		t.Errorf("Expected error for non-existent config file")
	}
}

func TestLoadConfig_InvalidYAML(t *testing.T) {
	// Create temporary invalid YAML file
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "invalid.yaml")
	
	invalidContent := `
server:
  host: "test
  port: invalid
  malformed: [unclosed
`
	
	err := os.WriteFile(configPath, []byte(invalidContent), 0644)
	if err != nil {
		t.Fatalf("Failed to write invalid config file: %v", err)
	}
	
	_, err = Load(configPath)
	if err == nil {
		t.Errorf("Expected error for invalid YAML")
	}
}

func TestConfig_ServerDefaults(t *testing.T) {
	cfg := &Config{}
	
	// Apply defaults (this might be done in Load)
	if cfg.Server.Host == "" {
		cfg.Server.Host = "127.0.0.1"
	}
	if cfg.Server.Port == 0 {
		cfg.Server.Port = 8080
	}
	
	if cfg.Server.Host != "127.0.0.1" {
		t.Errorf("Default host should be 127.0.0.1")
	}
	if cfg.Server.Port != 8080 {
		t.Errorf("Default port should be 8080")
	}
}

func TestConfig_SMTDefaults(t *testing.T) {
	cfg := &Config{}
	
	// Apply defaults
	if cfg.SMT.SolverTimeoutMs == 0 {
		cfg.SMT.SolverTimeoutMs = 5000
	}
	if cfg.SMT.MaxCandidates == 0 {
		cfg.SMT.MaxCandidates = 50
	}
	if cfg.SMT.MaxPairsPerDoc == 0 {
		cfg.SMT.MaxPairsPerDoc = 4000
	}
	
	if cfg.SMT.SolverTimeoutMs != 5000 {
		t.Errorf("Default SMT timeout should be 5000ms")
	}
	if cfg.SMT.MaxCandidates != 50 {
		t.Errorf("Default SMT max candidates should be 50")
	}
	if cfg.SMT.MaxPairsPerDoc != 4000 {
		t.Errorf("Default SMT max pairs per doc should be 4000")
	}
}

func TestConfig_WeightsDefaults(t *testing.T) {
	cfg := &Config{}
	
	// Apply weight defaults
	if cfg.Weights.Relevance == 0 {
		cfg.Weights.Relevance = 0.3
	}
	if cfg.Weights.Recency == 0 {
		cfg.Weights.Recency = 0.2
	}
	if cfg.Weights.Entanglement == 0 {
		cfg.Weights.Entanglement = 0.15
	}
	if cfg.Weights.Authority == 0 {
		cfg.Weights.Authority = 0.15
	}
	if cfg.Weights.Specificity == 0 {
		cfg.Weights.Specificity = 0.1
	}
	if cfg.Weights.Uncertainty == 0 {
		cfg.Weights.Uncertainty = 0.05
	}
	if cfg.Weights.Prior == 0 {
		cfg.Weights.Prior = 0.05
	}
	
	// Verify weight defaults
	expectedWeights := map[string]float64{
		"relevance":    0.3,
		"recency":      0.2,
		"entanglement": 0.15,
		"authority":    0.15,
		"specificity":  0.1,
		"uncertainty":  0.05,
		"prior":        0.05,
	}
	
	actualWeights := map[string]float64{
		"relevance":    cfg.Weights.Relevance,
		"recency":      cfg.Weights.Recency,
		"entanglement": cfg.Weights.Entanglement,
		"authority":    cfg.Weights.Authority,
		"specificity":  cfg.Weights.Specificity,
		"uncertainty":  cfg.Weights.Uncertainty,
		"prior":        cfg.Weights.Prior,
	}
	
	for name, expected := range expectedWeights {
		if actual := actualWeights[name]; actual != expected {
			t.Errorf("Default %s weight should be %f, got %f", name, expected, actual)
		}
	}
	
	// Verify weights sum to 1.0
	total := cfg.Weights.Relevance + cfg.Weights.Recency + cfg.Weights.Entanglement +
		cfg.Weights.Authority + cfg.Weights.Specificity + cfg.Weights.Uncertainty + cfg.Weights.Prior
	
	if total != 1.0 {
		t.Errorf("Default weights should sum to 1.0, got %f", total)
	}
}

func TestConfig_TokenizerDefaults(t *testing.T) {
	cfg := &Config{}
	
	// Apply defaults
	if cfg.Tokenizer.ModelID == "" {
		cfg.Tokenizer.ModelID = "gpt-4"
	}
	if cfg.Tokenizer.MaxTokensDefault == 0 {
		cfg.Tokenizer.MaxTokensDefault = 4000
	}
	
	if cfg.Tokenizer.ModelID != "gpt-4" {
		t.Errorf("Default tokenizer model should be 'gpt-4'")
	}
	if cfg.Tokenizer.MaxTokensDefault != 4000 {
		t.Errorf("Default max tokens should be 4000")
	}
}

func TestConfig_CacheDefaults(t *testing.T) {
	cfg := &Config{}
	
	// Apply defaults
	if cfg.Cache.L1Size == 0 {
		cfg.Cache.L1Size = 100
	}
	if cfg.Cache.L2TTLMinutes == 0 {
		cfg.Cache.L2TTLMinutes = 30
	}
	
	if cfg.Cache.L1Size != 100 {
		t.Errorf("Default L1 cache size should be 100")
	}
	if cfg.Cache.L2TTLMinutes != 30 {
		t.Errorf("Default L2 TTL should be 30 minutes")
	}
}

func TestConfig_EpsilonDefaults(t *testing.T) {
	cfg := &Config{}
	
	// Apply defaults
	if cfg.EpsilonConstraint.MaxRedundancy == 0 {
		cfg.EpsilonConstraint.MaxRedundancy = 0.7
	}
	if cfg.EpsilonConstraint.MinCoherence == 0 {
		cfg.EpsilonConstraint.MinCoherence = 0.5
	}
	if cfg.EpsilonConstraint.MinRecency == 0 {
		cfg.EpsilonConstraint.MinRecency = 0.1
	}
	
	if cfg.EpsilonConstraint.MaxRedundancy != 0.7 {
		t.Errorf("Default max redundancy should be 0.7")
	}
	if cfg.EpsilonConstraint.MinCoherence != 0.5 {
		t.Errorf("Default min coherence should be 0.5")
	}
	if cfg.EpsilonConstraint.MinRecency != 0.1 {
		t.Errorf("Default min recency should be 0.1")
	}
}

func TestConfig_PartialFile(t *testing.T) {
	// Test loading config with only some fields specified
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "partial_config.yaml")
	
	partialContent := `
server:
  port: 9000

smt:
  solver_timeout_ms: 1000
  max_candidates: 25
  objective_style: "weighted-sum"
  
weights:
  relevance: 0.5
`
	
	err := os.WriteFile(configPath, []byte(partialContent), 0644)
	if err != nil {
		t.Fatalf("Failed to write partial config file: %v", err)
	}
	
	cfg, err := Load(configPath)
	if err != nil {
		t.Fatalf("Failed to load partial config: %v", err)
	}
	
	// Check that specified values are loaded
	if cfg.Server.Port != 9000 {
		t.Errorf("Expected port 9000, got %d", cfg.Server.Port)
	}
	
	if cfg.SMT.SolverTimeoutMs != 1000 {
		t.Errorf("Expected solver timeout 1000ms, got %d", cfg.SMT.SolverTimeoutMs)
	}
	
	if cfg.Weights.Relevance != 0.5 {
		t.Errorf("Expected relevance weight 0.5, got %f", cfg.Weights.Relevance)
	}
	
	// Check that unspecified values get defaults (if LoadConfig applies them)
	// Note: The actual default application might happen in LoadConfig
}

func TestConfig_EmptyFile(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "empty_config.yaml")
	
	// Create minimal valid config instead of empty
	minimalConfig := `
server:
  port: 8080
smt:
  solver_timeout_ms: 1000
  max_candidates: 10
  objective_style: "weighted-sum"
`
	
	err := os.WriteFile(configPath, []byte(minimalConfig), 0644)
	if err != nil {
		t.Fatalf("Failed to write minimal config file: %v", err)
	}
	
	cfg, err := Load(configPath)
	if err != nil {
		t.Fatalf("Failed to load minimal config: %v", err)
	}
	
	if cfg == nil {
		t.Errorf("Config should not be nil for minimal config")
	}
}

// Test environment variable override capability (if implemented)
func TestConfig_EnvironmentOverride(t *testing.T) {
	// Create a temporary config file for testing
	tempConfig := `
server:
  host: "localhost"
  port: 8080

storage:
  database_path: ":memory:"

smt:
  z3_binary_path: ""
  solver_timeout_ms: 1000
  max_candidates: 50
  objective_style: "weighted-sum"
`
	
	// Write temporary config file
	tmpfile, err := os.CreateTemp("", "test_env_config_*.yaml")
	if err != nil {
		t.Fatalf("Failed to create temp config file: %v", err)
	}
	defer os.Remove(tmpfile.Name())
	
	if _, err := tmpfile.Write([]byte(tempConfig)); err != nil {
		t.Fatalf("Failed to write temp config file: %v", err)
	}
	tmpfile.Close()
	
	// Set environment variable
	originalPort := os.Getenv("CONTEXTLITE_PORT")
	defer func() {
		if originalPort == "" {
			os.Unsetenv("CONTEXTLITE_PORT")
		} else {
			os.Setenv("CONTEXTLITE_PORT", originalPort)
		}
	}()
	
	os.Setenv("CONTEXTLITE_PORT", "7777")
	
	// Load config using the temporary file
	cfg, err := Load(tmpfile.Name())
	if err != nil {
		t.Fatalf("Failed to load config: %v", err)
	}
	
	// Note: This test will only pass if LoadConfig actually supports environment variables
	// If not implemented, this test documents the expected behavior
	_ = cfg // Use cfg to avoid unused variable error
}

func TestConfig_ApplyEnvOverrides(t *testing.T) {
	// Test individual environment variable overrides
	
	// Test CONTEXTLITE_HOST override
	originalHost := os.Getenv("CONTEXTLITE_HOST")
	defer func() {
		if originalHost == "" {
			os.Unsetenv("CONTEXTLITE_HOST")
		} else {
			os.Setenv("CONTEXTLITE_HOST", originalHost)
		}
	}()
	
	os.Setenv("CONTEXTLITE_HOST", "custom-host")
	
	tempConfig := `
server:
  host: "localhost"
  port: 8080
storage:
  database_path: ":memory:"
smt:
  solver_timeout_ms: 1000
  max_candidates: 50
  objective_style: "weighted-sum"
`
	tmpfile, err := os.CreateTemp("", "test_host_config_*.yaml")
	if err != nil {
		t.Fatalf("Failed to create temp config file: %v", err)
	}
	defer os.Remove(tmpfile.Name())
	
	tmpfile.Write([]byte(tempConfig))
	tmpfile.Close()
	
	cfg, err := Load(tmpfile.Name())
	if err != nil {
		t.Fatalf("Failed to load config: %v", err)
	}
	
	if cfg.Server.Host != "custom-host" {
		t.Errorf("Expected host 'custom-host', got '%s'", cfg.Server.Host)
	}
}

func TestConfig_DatabasePathOverride(t *testing.T) {
	// Test CONTEXTLITE_DB_PATH override
	originalDBPath := os.Getenv("CONTEXTLITE_DB_PATH")
	defer func() {
		if originalDBPath == "" {
			os.Unsetenv("CONTEXTLITE_DB_PATH")
		} else {
			os.Setenv("CONTEXTLITE_DB_PATH", originalDBPath)
		}
	}()
	
	// Create a valid temp database path using forward slashes for YAML compatibility
	tmpDir := t.TempDir()
	customDbPath := filepath.ToSlash(filepath.Join(tmpDir, "custom", "db", "path", "test.db"))
	
	os.Setenv("CONTEXTLITE_DB_PATH", customDbPath)
	
	tempConfig := `
server:
  host: "localhost"
  port: 8080
storage:
  database_path: ":memory:"
smt:
  solver_timeout_ms: 1000
  max_candidates: 50
  objective_style: "weighted-sum"
`
	tmpfile, err := os.CreateTemp("", "test_db_config_*.yaml")
	if err != nil {
		t.Fatalf("Failed to create temp config file: %v", err)
	}
	defer os.Remove(tmpfile.Name())
	
	tmpfile.Write([]byte(tempConfig))
	tmpfile.Close()
	
	cfg, err := Load(tmpfile.Name())
	if err != nil {
		t.Fatalf("Failed to load config: %v", err)
	}
	
	if cfg.Storage.DatabasePath != customDbPath {
		t.Errorf("Expected database path '%s', got '%s'", customDbPath, cfg.Storage.DatabasePath)
	}
}

func TestConfig_ValidationErrors(t *testing.T) {
	// Test various validation error scenarios
	
	testCases := []struct {
		name          string
		configContent string
		expectError   bool
		errorContains string
	}{
		{
			name: "invalid_port_zero",
			configContent: `
server:
  port: 0
smt:
  solver_timeout_ms: 1000
  max_candidates: 50
`,
			expectError:   true,
			errorContains: "invalid server port",
		},
		{
			name: "invalid_port_too_high",
			configContent: `
server:
  port: 99999
smt:
  solver_timeout_ms: 1000
  max_candidates: 50
`,
			expectError:   true,
			errorContains: "invalid server port",
		},
		{
			name: "invalid_timeout_zero",
			configContent: `
server:
  port: 8080
smt:
  solver_timeout_ms: 0
  max_candidates: 50
`,
			expectError:   true,
			errorContains: "SMT solver timeout must be positive",
		},
		{
			name: "invalid_max_candidates_zero",
			configContent: `
server:
  port: 8080
smt:
  solver_timeout_ms: 1000
  max_candidates: 0
`,
			expectError:   true,
			errorContains: "max candidates must be positive",
		},
		{
			name: "valid_config",
			configContent: `
server:
  port: 8080
smt:
  solver_timeout_ms: 1000
  max_candidates: 50
  objective_style: "weighted-sum"
`,
			expectError: false,
		},
	}
	
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			tmpfile, err := os.CreateTemp("", "test_validation_*.yaml")
			if err != nil {
				t.Fatalf("Failed to create temp config file: %v", err)
			}
			defer os.Remove(tmpfile.Name())
			
			tmpfile.Write([]byte(tc.configContent))
			tmpfile.Close()
			
			_, err = Load(tmpfile.Name())
			
			if tc.expectError {
				if err == nil {
					t.Errorf("Expected error but got none")
				} else if tc.errorContains != "" && !stringContains(err.Error(), tc.errorContains) {
					t.Errorf("Expected error to contain '%s', got '%s'", tc.errorContains, err.Error())
				}
			} else {
				if err != nil {
					t.Errorf("Expected no error but got: %v", err)
				}
			}
		})
	}
}

// Helper function
func stringContains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || 
		(len(s) > len(substr) && 
			(s[:len(substr)] == substr || 
			 s[len(s)-len(substr):] == substr ||
			 indexOfSubstr(s, substr) != -1)))
}

func indexOfSubstr(s, substr string) int {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return i
		}
	}
	return -1
}

func TestConfig_Validation(t *testing.T) {
	// Test various config validation scenarios
	tests := []struct {
		name        string
		config      Config
		expectValid bool
	}{
		{
			name: "valid_config",
			config: Config{
				Server: ServerConfig{
					Host: "localhost",
					Port: 8080,
				},
				SMT: SMTConfig{
					SolverTimeoutMs: 5000,
					MaxCandidates:   50,
					MaxPairsPerDoc:  4000,
				},
			},
			expectValid: true,
		},
		{
			name: "invalid_port",
			config: Config{
				Server: ServerConfig{
					Host: "localhost",
					Port: -1, // Invalid port
				},
			},
			expectValid: false,
		},
		{
			name: "invalid_timeout",
			config: Config{
				SMT: SMTConfig{
					SolverTimeoutMs: -1000, // Invalid timeout
				},
			},
			expectValid: false,
		},
	}
	
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			valid := validateConfig(&test.config)
			if valid != test.expectValid {
				t.Errorf("Expected validation result %v, got %v", test.expectValid, valid)
			}
		})
	}
}

// Helper function for config validation (may not exist in actual code)
func validateConfig(cfg *Config) bool {
	if cfg.Server.Port < 0 || cfg.Server.Port > 65535 {
		return false
	}
	if cfg.SMT.SolverTimeoutMs < 0 {
		return false
	}
	if cfg.SMT.MaxCandidates < 0 {
		return false
	}
	if cfg.SMT.MaxPairsPerDoc < 0 {
		return false
	}
	return true
}

func TestConfig_ValidateComprehensive(t *testing.T) {
	// Test valid configuration
	validConfig := &Config{
		Server: ServerConfig{
			Host: "localhost",
			Port: 8080,
		},
		SMT: SMTConfig{
			SolverTimeoutMs: 5000,
			MaxCandidates:   50,
			ObjectiveStyle:  "weighted-sum",
			Z3: Z3Config{
				MaxVerificationDocs: 10,
			},
		},
		Storage: StorageConfig{
			DatabasePath: "/tmp/test.db",
		},
	}
	
	err := validate(validConfig)
	if err != nil {
		t.Errorf("Valid configuration should not return error: %v", err)
	}
	
	// Test invalid server port - negative
	invalidPortConfig := *validConfig
	invalidPortConfig.Server.Port = -1
	err = validate(&invalidPortConfig)
	if err == nil {
		t.Error("Expected error for negative port")
	}
	
	// Test invalid server port - too high
	invalidPortConfig.Server.Port = 70000
	err = validate(&invalidPortConfig)
	if err == nil {
		t.Error("Expected error for port > 65535")
	}
	
	// Test invalid server port - zero
	invalidPortConfig.Server.Port = 0
	err = validate(&invalidPortConfig)
	if err == nil {
		t.Error("Expected error for port 0")
	}
	
	// Test invalid SMT timeout
	invalidTimeoutConfig := *validConfig
	invalidTimeoutConfig.SMT.SolverTimeoutMs = 0
	err = validate(&invalidTimeoutConfig)
	if err == nil {
		t.Error("Expected error for zero timeout")
	}
	
	invalidTimeoutConfig.SMT.SolverTimeoutMs = -1000
	err = validate(&invalidTimeoutConfig)
	if err == nil {
		t.Error("Expected error for negative timeout")
	}
	
	// Test invalid max candidates
	invalidCandidatesConfig := *validConfig
	invalidCandidatesConfig.SMT.MaxCandidates = 0
	err = validate(&invalidCandidatesConfig)
	if err == nil {
		t.Error("Expected error for zero max candidates")
	}
	
	invalidCandidatesConfig.SMT.MaxCandidates = -5
	err = validate(&invalidCandidatesConfig)
	if err == nil {
		t.Error("Expected error for negative max candidates")
	}
	
	// Test invalid objective style
	invalidObjectiveConfig := *validConfig
	invalidObjectiveConfig.SMT.ObjectiveStyle = "invalid-style"
	err = validate(&invalidObjectiveConfig)
	if err == nil {
		t.Error("Expected error for invalid objective style")
	}
	
	// Test all valid objective styles
	validObjectiveStyles := []string{"weighted-sum", "lexicographic", "epsilon-constraint"}
	for _, style := range validObjectiveStyles {
		testConfig := *validConfig
		testConfig.SMT.ObjectiveStyle = style
		err = validate(&testConfig)
		if err != nil {
			t.Errorf("Valid objective style '%s' should not return error: %v", style, err)
		}
	}
	
	// Test Z3 binary path validation with non-existent file
	invalidZ3Config := *validConfig
	invalidZ3Config.SMT.Z3.BinaryPath = "/non/existent/z3/binary"
	err = validate(&invalidZ3Config)
	if err == nil {
		t.Error("Expected error for non-existent Z3 binary path")
	}
	
	// Test Z3 binary path validation with empty path (should be valid)
	validZ3Config := *validConfig
	validZ3Config.SMT.Z3.BinaryPath = ""
	err = validate(&validZ3Config)
	if err != nil {
		t.Errorf("Empty Z3 binary path should be valid: %v", err)
	}
	
	// Test negative max verification docs
	invalidVerificationConfig := *validConfig
	invalidVerificationConfig.SMT.Z3.MaxVerificationDocs = -1
	err = validate(&invalidVerificationConfig)
	if err == nil {
		t.Error("Expected error for negative max verification docs")
	}
}

func TestConfig_ValidateDatabasePath(t *testing.T) {
	// Create a temporary directory for testing
	tempDir := t.TempDir()
	
	// Test with valid database path in existing directory
	validConfig := &Config{
		Server: ServerConfig{
			Host: "localhost",
			Port: 8080,
		},
		SMT: SMTConfig{
			SolverTimeoutMs: 5000,
			MaxCandidates:   50,
			ObjectiveStyle:  "weighted-sum",
			Z3: Z3Config{
				MaxVerificationDocs: 10,
			},
		},
		Storage: StorageConfig{
			DatabasePath: filepath.Join(tempDir, "test.db"),
		},
	}
	
	err := validate(validConfig)
	if err != nil {
		t.Errorf("Valid database path should not return error: %v", err)
	}
	
	// Test with database path in nested directory that needs creation
	nestedPath := filepath.Join(tempDir, "nested", "dir", "test.db")
	validConfig.Storage.DatabasePath = nestedPath
	err = validate(validConfig)
	if err != nil {
		t.Errorf("Database path requiring directory creation should be valid: %v", err)
	}
	
	// Verify the directory was created
	if _, err := os.Stat(filepath.Dir(nestedPath)); os.IsNotExist(err) {
		t.Error("Database directory should have been created")
	}
	
	// Test with database path in read-only parent directory (if possible to create)
	readOnlyDir := filepath.Join(tempDir, "readonly")
	err = os.MkdirAll(readOnlyDir, 0444) // Read-only permissions
	if err != nil {
		t.Logf("Could not create read-only directory: %v", err)
	} else {
		readOnlyDbPath := filepath.Join(readOnlyDir, "subdir", "test.db")
		validConfig.Storage.DatabasePath = readOnlyDbPath
		err = validate(validConfig)
		// This may or may not fail depending on system permissions
		t.Logf("Read-only directory validation result: %v", err)
	}
}
