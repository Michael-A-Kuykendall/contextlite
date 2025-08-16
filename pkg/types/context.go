package types

// optimizationMetrics represents optimization system performance metrics
type optimizationMetrics struct {
	SolverUsed      string  `json:"solver_used"`
	OptimalityGap   float64 `json:"optimality_gap"`
	SolveTimeMs     int     `json:"solve_time_ms"`
	VariableCount   int     `json:"variable_count"`
	ConstraintCount int     `json:"budget_count"`
	FallbackReason  string  `json:"fallback_reason,omitempty"`
}

// StageTimings represents timing information for each pipeline stage
type StageTimings struct {
	FTSHarvestMs   int `json:"fts_harvest_ms"`
	FeatureBuildMs int `json:"feature_build_ms"`
	optimizationSolverMs    int `json:"optimization_solver_ms"`
	TotalMs        int `json:"total_ms"`
}

// AssembleRequest represents a context assembly request
type AssembleRequest struct {
	Query             string   `json:"query"`
	MaxTokens         int      `json:"max_tokens"`
	MaxDocuments      int      `json:"max_documents"`
	WorkspacePath     string   `json:"workspace_path,omitempty"`
	IncludePatterns   []string `json:"include_patterns,omitempty"`
	ExcludePatterns   []string `json:"exclude_patterns,omitempty"`
	ModelID           string   `json:"model_id,omitempty"`
	
	// optimization optimization parameters
	Useoptimization           bool    `json:"use_optimization"`
	optimizationTimeoutMs     int     `json:"optimization_timeout_ms,omitempty"`
	MaxOptGap        float64 `json:"max_opt_gap,omitempty"`
	ObjectiveStyle   string  `json:"objective_style,omitempty"`
	
	// Sampling (k-best only)
	EnableSampling   bool    `json:"enable_sampling"`
	Temperature      float64 `json:"temperature,omitempty"`
	TopK             int     `json:"top_k,omitempty"`
	
	// Caching
	UseCache         bool    `json:"use_cache"`
	CacheTTL         int     `json:"cache_ttl,omitempty"`
}

// AssembledContext represents the result of context assembly
type AssembledContext struct {
	Query          string              `json:"query"`
	Documents      []DocumentReference `json:"documents"`
	TotalTokens    int                 `json:"total_tokens"`
	CoherenceScore float64             `json:"coherence_score"`
	optimizationMetrics     optimizationMetrics          `json:"optimization_metrics"`
	Timings        StageTimings        `json:"timings"`
}

// QueryResult represents a query result with metadata
type QueryResult struct {
	Query          string              `json:"query"`
	Documents      []DocumentReference `json:"documents"`
	TotalDocuments int                 `json:"total_documents"`
	TotalTokens    int                 `json:"total_tokens"`
	CoherenceScore float64             `json:"coherence_score"`
	optimizationMetrics     optimizationMetrics          `json:"optimization_metrics"`
	Timings        StageTimings        `json:"timings"`
	CacheHit       bool                `json:"cache_hit"`
}
