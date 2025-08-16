package types

// SMTMetrics represents SMT solver performance metrics
type SMTMetrics struct {
	SolverUsed      string  `json:"solver_used"`
	Z3Status        string  `json:"z3_status,omitempty"`
	Objective       int64   `json:"objective,omitempty"`
	SolveTimeMs     int     `json:"solve_time_ms"`
	SMTWallMs       int     `json:"smt_wall_ms"`        // Total wall-clock time for SMT (includes I/O + parsing)
	VariableCount   int     `json:"variable_count"`
	ConstraintCount int     `json:"constraint_count"`
	KCandidates     int     `json:"K_candidates"`
	PairsCount      int     `json:"pairs_count"`
	BudgetTokens    int     `json:"budget_tokens"`
	MaxDocs         int     `json:"max_docs"`
	FallbackReason  string  `json:"fallback_reason,omitempty"`
}

// StageTimings represents timing information for each pipeline stage
type StageTimings struct {
	FTSHarvestMs   int `json:"fts_harvest_ms"`
	FeatureBuildMs int `json:"feature_build_ms"`
	SMTWallMs      int `json:"smt_wall_ms"`    // Total wall-clock time for SMT (includes I/O + parsing)
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
	
	// SMT optimization parameters
	UseSMT           bool    `json:"use_smt"`
	SMTTimeoutMs     int     `json:"smt_timeout_ms,omitempty"`
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
	SMTMetrics     SMTMetrics          `json:"smt_metrics"`
	Timings        StageTimings        `json:"timings"`
}

// QueryResult represents a query result with metadata
type QueryResult struct {
	Query          string              `json:"query"`
	Documents      []DocumentReference `json:"documents"`
	TotalDocuments int                 `json:"total_documents"`
	TotalTokens    int                 `json:"total_tokens"`
	CoherenceScore float64             `json:"coherence_score"`
	SMTMetrics     SMTMetrics          `json:"smt_metrics"`
	Timings        StageTimings        `json:"timings"`
	CacheHit       bool                `json:"cache_hit"`
	CacheKey       string              `json:"cache_key_fingerprint"`
}
