/*
 * ContextLite - SMT-Optimized AI Context Engine
 * Copyright (c) 2025 Michael A. Kuykendall
 * 
 * Patent Pending - Provisional Patent Filed
 * US Provisional Patent Application No. [PENDING]
 * 
 * This software contains proprietary algorithms protected by patent law.
 * Unauthorized reverse engineering or algorithm extraction is prohibited.
 * 
 * Licensed under Dual License:
 * - MIT License for open source use
 * - Commercial License for business use
 * 
 * See LICENSE-MIT.md and LICENSE-COMMERCIAL.md for terms.
 */

package types

import (
	"context"
	"time"
)

// FeatureExtractor defines the interface for extracting 7-dimensional features
// This abstracts the proprietary SMT optimization algorithms
type FeatureExtractor interface {
	// ExtractFeatures calculates 7D feature vector for a document given a query
	ExtractFeatures(doc Document, query string) FeatureVector
	
	// ExtractBatch processes multiple documents efficiently
	ExtractBatch(docs []Document, query string) []FeatureVector
	
	// UpdateWeights adapts feature weights based on user feedback
	UpdateWeights(feedback UserFeedback) error
	
	// GetWeights returns current feature weights for workspace
	GetWeights(workspacePath string) FeatureWeights
	
	// SetWeights explicitly sets feature weights
	SetWeights(workspacePath string, weights FeatureWeights) error
}

// SMTSolver defines the interface for mathematical optimization
// This abstracts the patent-pending SMT formulation algorithms
type SMTSolver interface {
	// OptimizeSelection performs mathematical optimization of document selection
	OptimizeSelection(docs []ScoredDocument, constraints SelectionConstraints) ([]int, error)
	
	// SetStrategy configures optimization strategy (weighted-sum, lexicographic, etc.)
	SetStrategy(strategy OptimizationStrategy) error
	
	// SetTimeout configures solver timeout
	SetTimeout(timeout time.Duration) error
	
	// GetStats returns solver performance statistics
	GetStats() SolverStats
}

// ContextEngine defines the complete context assembly interface
// This is the main public API that combines all private algorithms
type ContextEngine interface {
	// AssembleContext performs end-to-end context assembly
	AssembleContext(ctx context.Context, request ContextRequest) (*ContextResult, error)
	
	// IndexDocument adds or updates a document in the workspace
	IndexDocument(doc Document) error
	
	// RemoveDocument removes a document from the workspace
	RemoveDocument(docID string) error
	
	// GetStats returns engine performance and usage statistics
	GetStats() (*EngineStats, error)
	
	// UpdateConfig applies new configuration settings
	UpdateConfig(config EngineConfig) error
	
	// Close performs cleanup and resource deallocation
	Close() error
}

// StorageInterface defines persistent storage operations
// This interface is already well-defined and will remain public
type StorageInterface interface {
	// Document operations
	InsertDocument(doc Document) error
	UpdateDocument(doc Document) error
	GetDocument(ctx context.Context, id string) (*Document, error)
	GetDocumentByPath(ctx context.Context, path string) (*Document, error)
	DeleteDocument(ctx context.Context, id string) error
	AddDocument(ctx context.Context, doc *Document) error  // Legacy method for compatibility
	
	// Search operations
	SearchDocuments(ctx context.Context, query string, limit int) ([]Document, error)
	
	// Workspace operations
	GetWorkspaceStats(workspacePath string) (*WorkspaceStats, error)
	GetWorkspaceWeights(ctx context.Context, workspacePath string) (*WorkspaceWeights, error)
	SaveWorkspaceWeights(workspacePath string, weights FeatureWeights) error
	
	// Cache operations
	GetCorpusHash(ctx context.Context) (string, error)
	GetQueryCache(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion string) (*QueryResult, error)
	SaveQueryCacheWithKey(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion, cacheKey string, result *QueryResult, expiresAt time.Time) error
	GetCachedResultByKey(ctx context.Context, cacheKey string) (*QueryResult, error)
	InvalidateCache(ctx context.Context) error
	GetCacheStats(ctx context.Context) (*CacheStats, error)
	GetStorageStats(ctx context.Context) (map[string]interface{}, error)
	
	// Cleanup operations
	Close() error
}

// UserFeedback represents user selection patterns for learning
// Note: This interface extends the existing UserFeedback type in quantum.go
type UserFeedbackInterface interface {
	GetQuery() string
	GetAcceptedDocs() []string
	GetRejectedDocs() []string
	GetWorkspacePath() string
	GetTimestamp() int64
}

// FeatureWeights represents the 7-dimensional weight configuration
type FeatureWeights struct {
	Relevance    float64 `json:"relevance"`     // Query matching strength
	Recency      float64 `json:"recency"`       // Time-based decay
	Entanglement float64 `json:"entanglement"`  // Cross-document concept density
	Prior        float64 `json:"prior"`         // Historical selection patterns
	Authority    float64 `json:"authority"`     // Document importance
	Specificity  float64 `json:"specificity"`   // Query-document topic alignment
	Uncertainty  float64 `json:"uncertainty"`   // Confidence variance (subtracted)
}

// SelectionConstraints defines limits for optimization
type SelectionConstraints struct {
	MaxTokens      int     `json:"max_tokens"`
	MaxDocuments   int     `json:"max_documents"`
	MinRelevance   float64 `json:"min_relevance"`
	DiversityThreshold float64 `json:"diversity_threshold"`
}

// OptimizationStrategy defines the SMT solving approach
type OptimizationStrategy string

const (
	StrategyWeightedSum    OptimizationStrategy = "weighted-sum"
	StrategyLexicographic  OptimizationStrategy = "lexicographic"
	StrategyEpsilonConstraint OptimizationStrategy = "epsilon-constraint"
)

// SolverStats provides SMT solver performance metrics
type SolverStats struct {
	TotalSolves       int64         `json:"total_solves"`
	AverageSolveTime  time.Duration `json:"average_solve_time"`
	TimeoutCount      int64         `json:"timeout_count"`
	OptimalityGap     float64       `json:"optimality_gap"`
	LastSolveTime     time.Duration `json:"last_solve_time"`
}

// EngineConfig provides runtime configuration for the context engine
type EngineConfig struct {
	// Feature extraction settings
	FeatureWeights      FeatureWeights       `json:"feature_weights"`
	
	// SMT solver settings
	OptimizationStrategy OptimizationStrategy `json:"optimization_strategy"`
	SolverTimeout       time.Duration        `json:"solver_timeout"`
	MaxOptimalityGap    float64             `json:"max_optimality_gap"`
	
	// Performance settings
	MaxCandidates       int                 `json:"max_candidates"`
	ConcurrentWorkers   int                 `json:"concurrent_workers"`
	
	// Caching settings
	CacheEnabled        bool                `json:"cache_enabled"`
	CacheSize          int                 `json:"cache_size"`
	CacheTTL           time.Duration       `json:"cache_ttl"`
}

// EngineStats provides comprehensive engine performance metrics
type EngineStats struct {
	// Query statistics
	TotalQueries       int64         `json:"total_queries"`
	AverageQueryTime   time.Duration `json:"average_query_time"`
	CacheHitRate      float64       `json:"cache_hit_rate"`
	
	// Document statistics
	TotalDocuments     int64         `json:"total_documents"`
	IndexedWorkspaces  int           `json:"indexed_workspaces"`
	
	// Feature extraction statistics
	FeatureExtractionTime time.Duration `json:"feature_extraction_time"`
	
	// SMT solver statistics
	SolverStats        SolverStats   `json:"solver_stats"`
	
	// Memory usage
	MemoryUsageMB     float64       `json:"memory_usage_mb"`
	
	// License information
	LicenseTier       string        `json:"license_tier"`
	LicenseValid      bool          `json:"license_valid"`
}

// CacheStats provides cache performance metrics
type CacheStats struct {
	Hits     int64   `json:"hits"`
	Misses   int64   `json:"misses"`
	HitRate  float64 `json:"hit_rate"`
	L1Size   int     `json:"l1_size"`
	L2Size   int     `json:"l2_size"`
}

// WorkspaceStats provides workspace-specific metrics
type WorkspaceStats struct {
	Path              string    `json:"path"`
	DocumentCount     int       `json:"document_count"`
	TotalTokens       int64     `json:"total_tokens"`
	LastIndexed       time.Time `json:"last_indexed"`
	Languages         []string  `json:"languages"`
	AverageFileSize   int64     `json:"average_file_size"`
}

// SMTResult represents the result of SMT optimization
type SMTResult struct {
	SelectedDocs    []int  `json:"selected_docs"`     // Indices of selected documents
	SolverUsed      string `json:"solver_used"`       // SMT solver used (z3, cvc4, etc.)
	Z3Status        string `json:"z3_status"`         // Solver status (satisfied, unsat, etc.)
	Objective       float64 `json:"objective"`        // Objective function value
	SolveTimeUs     int64  `json:"solve_time_us"`     // Solver time in microseconds
	VariableCount   int    `json:"variable_count"`    // Number of SMT variables
	ConstraintCount int    `json:"constraint_count"`  // Number of SMT constraints
	KCandidates     int    `json:"k_candidates"`      // Number of candidate documents
	PairsCount      int    `json:"pairs_count"`       // Number of pairwise constraints
	BudgetTokens    int    `json:"budget_tokens"`     // Token budget constraint
	MaxDocs         int    `json:"max_docs"`          // Maximum documents constraint
	FallbackReason  string `json:"fallback_reason"`   // Reason for fallback (if any)
}

// FeatureGate defines license-based feature access control
type FeatureGate interface {
	// IsEnabled checks if a feature is enabled for current license
	IsEnabled(feature string) bool
	
	// RequireFeature returns error if feature not available
	RequireFeature(feature string) error
	
	// RequireProfessional ensures Professional+ license
	RequireProfessional() error
	
	// RequireEnterprise ensures Enterprise license
	RequireEnterprise() error
	
	// GetTier returns current license tier
	GetTier() string
}

// ContextRequest represents a request for context assembly
type ContextRequest struct {
	Query         string `json:"query"`
	MaxTokens     int    `json:"max_tokens"`
	MaxDocuments  int    `json:"max_documents"`
	WorkspacePath string `json:"workspace_path,omitempty"`
}

// ContextResult represents the result of context assembly
type ContextResult struct {
	Context        string                 `json:"context"`
	Documents      []DocumentReference    `json:"documents"`  // Uses existing type
	TotalTokens    int                   `json:"total_tokens"`
	ProcessingTime time.Duration         `json:"processing_time"`
	CacheHit       bool                  `json:"cache_hit"`
	Message        string                `json:"message,omitempty"`
	CoherenceScore float64               `json:"coherence_score,omitempty"`
	SMTMetrics     *SMTResult            `json:"smt_metrics,omitempty"`
}

// DocumentReference represents a reference to a selected document
// Note: This interface uses the existing DocumentReference type in document.go
type DocumentReferenceInterface interface {
	GetID() string
	GetPath() string
	GetContent() string
	GetLanguage() string
	GetUtilityScore() float64
	GetRelevanceScore() float64
	GetRecencyScore() float64
	GetInclusionReason() string
}
