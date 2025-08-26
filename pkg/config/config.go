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
	optimization      optimizationConfig      `yaml:"optimization"`
	Weights  WeightsConfig  `yaml:"weights"`
	Lexicographic LexConfig `yaml:"lexicographic"`
	EpsilonConstraint EpsilonConfig `yaml:"epsilon_budget"`
	Tokenizer TokenizerConfig `yaml:"tokenizer"`
	Cache     CacheConfig    `yaml:"cache"`
	Logging   LoggingConfig  `yaml:"logging"`
	Cluster   ClusterConfig  `yaml:"cluster"`
}

type ServerConfig struct {
	Port         int                    `yaml:"port"`
	Host         string                 `yaml:"host"`
	CORSEnabled  bool                   `yaml:"cors_enabled"`
	AuthToken    string                 `yaml:"auth_token"`
	RateLimiting RateLimitingConfig     `yaml:"rate_limiting"`
}

type RateLimitingConfig struct {
	Enabled           bool           `yaml:"enabled"`
	RequestsPerMinute int            `yaml:"requests_per_minute"`
	Burst             int            `yaml:"burst"`
	EndpointSpecific  map[string]int `yaml:"endpoint_specific"`
}

type StorageConfig struct {
	DatabasePath string `yaml:"database_path"`
	CacheSizeMB  int    `yaml:"cache_size_mb"`
}

type optimizationConfig struct {
	SolverTimeoutMs  int     `yaml:"solver_timeout_ms"`
	MaxOptGap        float64 `yaml:"max_opt_gap"`
	MaxCandidates    int     `yaml:"max_candidates"`
	MaxPairsPerDoc   int     `yaml:"max_pairs_per_doc"`
	IntegerScaling   int     `yaml:"integer_scaling"`
	ObjectiveStyle   string  `yaml:"objective_style"`
	optimizer               optimizerConfig `yaml:"z3"`
}

type optimizerConfig struct {
	BinaryPath       string `yaml:"binary_path"`
	EnableVerification bool `yaml:"enable_verification"`
	MaxVerificationDocs int `yaml:"max_verification_docs"`
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
	IncludeoptimizationMetrics bool   `yaml:"include_optimization_metrics"`
}

// ClusterConfig defines clustering and multi-project support settings
type ClusterConfig struct {
	Enabled         bool                              `yaml:"enabled"`
	NodeID          string                            `yaml:"node_id"`
	Discovery       DiscoveryConfig                   `yaml:"discovery"`
	Affinity        AffinityConfig                    `yaml:"affinity"`
	LoadBalancing   LoadBalancingConfig               `yaml:"load_balancing"`
	ResourceLimits  map[string]WorkspaceResourceLimits `yaml:"resource_limits"`
	HealthCheck     HealthCheckConfig                 `yaml:"health_check"`
}

// DiscoveryConfig defines how nodes discover each other
type DiscoveryConfig struct {
	Method      string   `yaml:"method"`       // "static", "consul", "etcd", "k8s"
	Endpoints   []string `yaml:"endpoints"`    // Discovery service endpoints
	ServiceName string   `yaml:"service_name"` // Service name for discovery
	TTLSeconds  int      `yaml:"ttl_seconds"`  // Registration TTL
	Tags        []string `yaml:"tags"`         // Service tags for discovery
}

// AffinityConfig defines project affinity and routing rules
type AffinityConfig struct {
	WorkspaceRouting bool                           `yaml:"workspace_routing"`
	StickySessions   bool                           `yaml:"sticky_sessions"`
	Rules            map[string]WorkspaceAffinityRule `yaml:"rules"`
	DefaultTier      string                         `yaml:"default_tier"` // "low", "medium", "high"
}

// WorkspaceAffinityRule defines routing rules for a specific workspace
type WorkspaceAffinityRule struct {
	PreferredNodes []string `yaml:"preferred_nodes"`
	AvoidNodes     []string `yaml:"avoid_nodes"`
	ResourceTier   string   `yaml:"resource_tier"`
	StickySession  bool     `yaml:"sticky_session"`
	Locality       string   `yaml:"locality"`
}

// LoadBalancingConfig defines load balancing strategy
type LoadBalancingConfig struct {
	Strategy              string  `yaml:"strategy"`                // "round_robin", "least_connections", "resource_based", "workspace_hash"
	HealthCheckInterval   int     `yaml:"health_check_interval"`   // Seconds
	UnhealthyThreshold    int     `yaml:"unhealthy_threshold"`     // Failed checks before marking unhealthy
	HealthyThreshold      int     `yaml:"healthy_threshold"`       // Successful checks before marking healthy
	MaxLoadFactor         float64 `yaml:"max_load_factor"`         // 0.0 - 1.0
	EnableCircuitBreaker  bool    `yaml:"enable_circuit_breaker"`
}

// WorkspaceResourceLimits defines resource budgets for a workspace
type WorkspaceResourceLimits struct {
	MaxConcurrentRequests int   `yaml:"max_concurrent_requests"`
	MaxTokensPerMinute   int   `yaml:"max_tokens_per_minute"`
	MaxDocumentsPerQuery int   `yaml:"max_documents_per_query"`
	MaxMemoryMB         int64 `yaml:"max_memory_mb"`
	MaxStorageMB        int64 `yaml:"max_storage_mb"`
	Priority            int   `yaml:"priority"` // 1-10, higher = more priority
}

// HealthCheckConfig defines cluster health checking behavior
type HealthCheckConfig struct {
	Interval           int    `yaml:"interval"`            // Seconds between health checks
	Timeout            int    `yaml:"timeout"`             // Health check timeout in seconds
	UnhealthyThreshold int    `yaml:"unhealthy_threshold"` // Failed checks before unhealthy
	HealthyThreshold   int    `yaml:"healthy_threshold"`   // Successful checks before healthy
	Endpoint           string `yaml:"endpoint"`            // Health check endpoint path
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

	if config.optimization.SolverTimeoutMs <= 0 {
		return fmt.Errorf("optimization system timeout must be positive")
	}

	if config.optimization.MaxCandidates <= 0 {
		return fmt.Errorf("max candidates must be positive")
	}

	validObjectiveStyles := map[string]bool{
		"weighted-sum":      true,
		"lexicographic":     true,
		"epsilon-budget": true,
	}
	if !validObjectiveStyles[config.optimization.ObjectiveStyle] {
		return fmt.Errorf("invalid objective style: %s", config.optimization.ObjectiveStyle)
	}

	// Validate optimizer configuration
	if config.optimization.optimizer.BinaryPath != "" {
		if _, err := os.Stat(config.optimization.optimizer.BinaryPath); err != nil {
			return fmt.Errorf("optimizer binary not found at path: %s", config.optimization.optimizer.BinaryPath)
		}
	}

	if config.optimization.optimizer.MaxVerificationDocs < 0 {
		return fmt.Errorf("max verification docs must be non-negative")
	}

	// Ensure database directory exists
	dbDir := filepath.Dir(config.Storage.DatabasePath)
	if err := os.MkdirAll(dbDir, 0755); err != nil {
		return fmt.Errorf("failed to create database directory: %w", err)
	}

	return nil
}
