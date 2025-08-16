package config

import (
	"fmt"
	"os"
	"path/filepath"

	"gopkg.in/yaml.v3"
)

// Config represents the application configuration
type Config struct {
	Server   ServerConfig   `yaml:"server"`
	Storage  StorageConfig  `yaml:"storage"`
	SMT      SMTConfig      `yaml:"smt"`
	Weights  WeightsConfig  `yaml:"weights"`
	Lexicographic LexConfig `yaml:"lexicographic"`
	EpsilonConstraint EpsilonConfig `yaml:"epsilon_constraint"`
	Tokenizer TokenizerConfig `yaml:"tokenizer"`
	Cache     CacheConfig    `yaml:"cache"`
	Logging   LoggingConfig  `yaml:"logging"`
}

type ServerConfig struct {
	Port        int    `yaml:"port"`
	Host        string `yaml:"host"`
	CORSEnabled bool   `yaml:"cors_enabled"`
	AuthToken   string `yaml:"auth_token"`
}

type StorageConfig struct {
	DatabasePath string `yaml:"database_path"`
	CacheSizeMB  int    `yaml:"cache_size_mb"`
}

type SMTConfig struct {
	SolverTimeoutMs  int     `yaml:"solver_timeout_ms"`
	MaxOptGap        float64 `yaml:"max_opt_gap"`
	MaxCandidates    int     `yaml:"max_candidates"`
	MaxPairsPerDoc   int     `yaml:"max_pairs_per_doc"`
	IntegerScaling   int     `yaml:"integer_scaling"`
	ObjectiveStyle   string  `yaml:"objective_style"`
}

type WeightsConfig struct {
	Relevance         float64   `yaml:"relevance"`
	Recency          float64   `yaml:"recency"`
	Entanglement     float64   `yaml:"entanglement"`
	Prior            float64   `yaml:"prior"`
	Authority        float64   `yaml:"authority"`
	Specificity      float64   `yaml:"specificity"`
	Uncertainty      float64   `yaml:"uncertainty"`
	RedundancyPenalty float64  `yaml:"redundancy_penalty"`
	CoherenceBonus   float64   `yaml:"coherence_bonus"`
	WeightUpdateRate float64   `yaml:"weight_update_rate"`
	WeightCaps       [2]float64 `yaml:"weight_caps"`
}

type LexConfig struct {
	ComputeAtRuntime bool `yaml:"compute_at_runtime"`
}

type EpsilonConfig struct {
	MaxRedundancy float64 `yaml:"max_redundancy"`
	MinCoherence  float64 `yaml:"min_coherence"`
	MinRecency    float64 `yaml:"min_recency"`
}

type TokenizerConfig struct {
	ModelID           string `yaml:"model_id"`
	MaxTokensDefault  int    `yaml:"max_tokens_default"`
}

type CacheConfig struct {
	L1Size       int  `yaml:"l1_size"`
	L2TTLMinutes int  `yaml:"l2_ttl_minutes"`
	L3Enabled    bool `yaml:"l3_enabled"`
}

type LoggingConfig struct {
	Level             string `yaml:"level"`
	IncludeTimings    bool   `yaml:"include_timings"`
	IncludeSMTMetrics bool   `yaml:"include_smt_metrics"`
}

// Load loads configuration from file with environment variable overrides
func Load(configPath string) (*Config, error) {
	// Set default config path if not provided
	if configPath == "" {
		configPath = "configs/default.yaml"
	}

	// Read config file
	data, err := os.ReadFile(configPath)
	if err != nil {
		return nil, fmt.Errorf("failed to read config file %s: %w", configPath, err)
	}

	// Parse YAML
	var config Config
	if err := yaml.Unmarshal(data, &config); err != nil {
		return nil, fmt.Errorf("failed to parse config file %s: %w", configPath, err)
	}

	// Apply environment variable overrides
	applyEnvOverrides(&config)

	// Validate configuration
	if err := validate(&config); err != nil {
		return nil, fmt.Errorf("invalid configuration: %w", err)
	}

	return &config, nil
}

// applyEnvOverrides applies environment variable overrides to config
func applyEnvOverrides(config *Config) {
	if port := os.Getenv("CONTEXTLITE_PORT"); port != "" {
		// Parse port, but for now just leave as is - would need strconv
	}
	if host := os.Getenv("CONTEXTLITE_HOST"); host != "" {
		config.Server.Host = host
	}
	if dbPath := os.Getenv("CONTEXTLITE_DB_PATH"); dbPath != "" {
		config.Storage.DatabasePath = dbPath
	}
	if token := os.Getenv("CONTEXTLITE_AUTH_TOKEN"); token != "" {
		config.Server.AuthToken = token
	}
}

// validate validates the configuration
func validate(config *Config) error {
	if config.Server.Port <= 0 || config.Server.Port > 65535 {
		return fmt.Errorf("invalid server port: %d", config.Server.Port)
	}

	if config.SMT.SolverTimeoutMs <= 0 {
		return fmt.Errorf("SMT solver timeout must be positive")
	}

	if config.SMT.MaxCandidates <= 0 {
		return fmt.Errorf("max candidates must be positive")
	}

	validObjectiveStyles := map[string]bool{
		"weighted-sum":      true,
		"lexicographic":     true,
		"epsilon-constraint": true,
	}
	if !validObjectiveStyles[config.SMT.ObjectiveStyle] {
		return fmt.Errorf("invalid objective style: %s", config.SMT.ObjectiveStyle)
	}

	// Ensure database directory exists
	dbDir := filepath.Dir(config.Storage.DatabasePath)
	if err := os.MkdirAll(dbDir, 0755); err != nil {
		return fmt.Errorf("failed to create database directory: %w", err)
	}

	return nil
}
