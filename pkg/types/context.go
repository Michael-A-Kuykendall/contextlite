package types

// optimizationMetrics represents optimization system performance metrics
type optimizationMetrics struct {
	SolverUsed      string  `json:"solver_used"`
	optimizerStatus        string  `json:"z3_status,omitempty"`
	Objective       int64   `json:"objective,omitempty"`
	SolveTimeUs     int64   `json:"solve_time_us"`      // Pure solver time in microseconds
	SolveTimeMs     float64 `json:"solve_time_ms"`      // Pure solver time in milliseconds (float)
	optimizationWallUs       int64   `json:"optimization_wall_us"`        // Total wall-clock time for optimization (includes I/O + parsing)
	optimizationWallMs       float64 `json:"optimization_wall_ms"`        // Total wall-clock time in milliseconds (float)
	VariableCount   int     `json:"variable_count"`
	ConstraintCount int     `json:"budget_count"`
	KCandidates     int     `json:"K_candidates"`
	PairsCount      int     `json:"pairs_count"`
	BudgetTokens    int     `json:"budget_tokens"`
	MaxDocs         int     `json:"max_docs"`
	FallbackReason  string  `json:"fallback_reason,omitempty"`
}

// StageTimings represents timing information for each pipeline stage
type StageTimings struct {
	// Microsecond precision timings (primary values)
	FTSHarvestUs   int64   `json:"fts_harvest_us"`
	FeatureBuildUs int64   `json:"feature_build_us"`
	optimizationSolverUs    int64   `json:"optimization_solver_us"`    // Pure solver time
	optimizationWallUs      int64   `json:"optimization_wall_us"`      // Total wall-clock time for optimization (includes I/O + parsing)
	TotalUs        int64   `json:"total_us"`
	
	// Float millisecond convenience fields (derived from microseconds)
	FTSHarvestMs   float64 `json:"fts_harvest_ms"`
	FeatureBuildMs float64 `json:"feature_build_ms"`
	optimizationSolverMs    float64 `json:"optimization_solver_ms"`
	optimizationWallMs      float64 `json:"optimization_wall_ms"`
	TotalMs        float64 `json:"total_ms"`
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
	CacheKey       string              `json:"cache_key_fingerprint"`
}
