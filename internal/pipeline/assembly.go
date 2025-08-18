package pipeline

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"time"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// CacheParts contains all components for building a cache key
type CacheParts struct {
	QueryHash           string `json:"query_hash"`
	CorpusHash          string `json:"corpus_hash"`
	ModelID             string `json:"model_id"`
	TokenizerVersion    string `json:"tokenizer_version"`
	TokenizerVocabHash  string `json:"tokenizer_vocab_hash"`
	WeightsHash         string `json:"weights_hash"`
	ConceptDFVersion    string `json:"concept_df_version"`
	MaxTokens           int    `json:"max_tokens"`
	MaxDocuments        int    `json:"max_documents"`
	ObjectiveStyle      string `json:"objective_style"`
}

// BuildCacheKey creates a deterministic cache key from parts
func BuildCacheKey(parts CacheParts) string {
	jsonData, _ := json.Marshal(parts)
	hash := sha256.Sum256(jsonData)
	return hex.EncodeToString(hash[:])
}

// Pipeline provides the main context assembly pipeline
// This is now a thin wrapper that delegates to the engine
type Pipeline struct {
	storage types.StorageInterface
	engine  types.ContextEngine
	config  *config.Config
}

// New creates a new pipeline instance
func New(storage types.StorageInterface, engine types.ContextEngine, config *config.Config) *Pipeline {
	return &Pipeline{
		storage: storage,
		engine:  engine,
		config:  config,
	}
}

// Getter methods for testing
func (p *Pipeline) Storage() types.StorageInterface {
	return p.storage
}

func (p *Pipeline) Config() *config.Config {
	return p.config
}

// AssembleContext performs the complete context assembly pipeline
// This now simply delegates to the engine and handles type conversion
func (p *Pipeline) AssembleContext(ctx context.Context, req *types.AssembleRequest) (*types.QueryResult, error) {
	// Check cache first if enabled
	var cacheKey string
	if req.UseCache {
		cacheKey = p.buildCacheKey(ctx, req)
		if cached, err := p.getCachedResultByKey(ctx, cacheKey); err == nil && cached != nil {
			cached.CacheHit = true
			cached.CacheKey = cacheKey
			return cached, nil
		}
	}

	// Convert AssembleRequest to ContextRequest for the engine
	contextReq := types.ContextRequest{
		Query:         req.Query,
		MaxTokens:     req.MaxTokens,
		MaxDocuments:  req.MaxDocuments,
		WorkspacePath: req.WorkspacePath,
	}
	
	// Delegate ALL the work to the engine
	startTime := time.Now()
	result, err := p.engine.AssembleContext(ctx, contextReq)
	if err != nil {
		return nil, err
	}
	
	// Convert ContextResult to QueryResult for backward compatibility
	queryResult := &types.QueryResult{
		Query:          req.Query,
		Documents:      result.Documents,
		TotalDocuments: len(result.Documents),
		TotalTokens:    result.TotalTokens,
		CoherenceScore: result.CoherenceScore,
		CacheHit:       result.CacheHit,
		CacheKey:       cacheKey,
	}
	
	// Convert optimizationResult to optimizationMetrics if present
	if result.optimizationMetrics != nil {
		queryResult.optimizationMetrics = types.optimizationMetrics{
			SolverUsed:      result.optimizationMetrics.SolverUsed,
			optimizerStatus:        result.optimizationMetrics.optimizerStatus,
			Objective:       int64(result.optimizationMetrics.Objective),
			SolveTimeUs:     result.optimizationMetrics.SolveTimeUs,
			SolveTimeMs:     float64(result.optimizationMetrics.SolveTimeUs) / 1000.0,
			VariableCount:   result.optimizationMetrics.VariableCount,
			ConstraintCount: result.optimizationMetrics.ConstraintCount,
			KCandidates:     result.optimizationMetrics.KCandidates,
			PairsCount:      result.optimizationMetrics.PairsCount,
			BudgetTokens:    result.optimizationMetrics.BudgetTokens,
			MaxDocs:         result.optimizationMetrics.MaxDocs,
			FallbackReason:  result.optimizationMetrics.FallbackReason,
		}
	}
	
	// Add timing information
	totalTime := time.Since(startTime)
	queryResult.Timings = types.StageTimings{
		TotalUs: totalTime.Microseconds(),
		TotalMs: float64(totalTime.Microseconds()) / 1000.0,
		// Other timing fields come from the engine if it provides them
	}
	
	// Cache result if enabled and high quality
	if req.UseCache && queryResult.CoherenceScore > 0.5 {
		p.cacheResult(ctx, req, queryResult)
	}
	
	return queryResult, nil
}

// IndexDocument delegates to the engine
func (p *Pipeline) IndexDocument(doc types.Document) error {
	return p.engine.IndexDocument(doc)
}

// RemoveDocument delegates to the engine
func (p *Pipeline) RemoveDocument(docID string) error {
	return p.engine.RemoveDocument(docID)
}

// GetEngineStats delegates to the engine
func (p *Pipeline) GetEngineStats() (*types.EngineStats, error) {
	return p.engine.GetStats()
}

// UpdateEngineConfig delegates to the engine
func (p *Pipeline) UpdateEngineConfig(config types.EngineConfig) error {
	return p.engine.UpdateConfig(config)
}

// Close performs cleanup
func (p *Pipeline) Close() error {
	if err := p.engine.Close(); err != nil {
		return err
	}
	if p.storage != nil {
		return p.storage.Close()
	}
	return nil
}

// Cache management helpers (these stay in pipeline as they're not core to engine)

// buildCacheKey generates a deterministic cache key for the request
func (p *Pipeline) buildCacheKey(ctx context.Context, req *types.AssembleRequest) string {
	// Get corpus hash
	corpusHash, _ := p.storage.GetCorpusHash(ctx)
	
	// Build query hash
	queryHash := p.hashQuery(req)
	
	// Get tokenizer version from config
	tokenizerVersion := "v1.0"
	if p.config != nil && p.config.Tokenizer.ModelID != "" {
		tokenizerVersion = p.config.Tokenizer.ModelID + "-v1.0"
	}
	
	// Compute weights hash from workspace weights
	weightsHash := "default"
	if req.WorkspacePath != "" {
		if weights, err := p.storage.GetWorkspaceWeights(ctx, req.WorkspacePath); err == nil {
			weightsData, _ := json.Marshal(weights)
			hash := sha256.Sum256(weightsData)
			weightsHash = hex.EncodeToString(hash[:8]) // First 8 bytes
		}
	}
	
	// Build cache parts
	parts := CacheParts{
		QueryHash:           queryHash,
		CorpusHash:          corpusHash,
		ModelID:             req.ModelID,
		TokenizerVersion:    tokenizerVersion,
		TokenizerVocabHash:  "vocab-" + tokenizerVersion,
		WeightsHash:         weightsHash,
		ConceptDFVersion:    "concepts-v1.0",
		MaxTokens:           req.MaxTokens,
		MaxDocuments:        req.MaxDocuments,
		ObjectiveStyle:      req.ObjectiveStyle,
	}
	
	return BuildCacheKey(parts)
}

// getCachedResultByKey retrieves cached result by cache key
func (p *Pipeline) getCachedResultByKey(ctx context.Context, cacheKey string) (*types.QueryResult, error) {
	return p.storage.GetCachedResultByKey(ctx, cacheKey)
}

// cacheResult saves query result to cache
func (p *Pipeline) cacheResult(ctx context.Context, req *types.AssembleRequest, result *types.QueryResult) {
	queryHash := p.hashQuery(req)
	corpusHash, err := p.storage.GetCorpusHash(ctx)
	if err != nil {
		return
	}
	
	modelID := req.ModelID
	if modelID == "" && p.config != nil {
		modelID = p.config.Tokenizer.ModelID
	}
	
	tokenizerVersion := "1.0"
	
	// Cache for configured TTL
	ttl := time.Duration(req.CacheTTL) * time.Minute
	if ttl <= 0 && p.config != nil {
		ttl = time.Duration(p.config.Cache.L2TTLMinutes) * time.Minute
	}
	if ttl <= 0 {
		ttl = 24 * time.Hour // Default 24 hours
	}
	expiresAt := time.Now().Add(ttl)
	
	// Use the new method with cache key
	cacheKey := result.CacheKey
	p.storage.SaveQueryCacheWithKey(ctx, queryHash, corpusHash, modelID, tokenizerVersion, cacheKey, result, expiresAt)
}

// hashQuery generates a hash for the query request
func (p *Pipeline) hashQuery(req *types.AssembleRequest) string {
	// Create deterministic hash of query parameters
	data := struct {
		Query           string   `json:"query"`
		MaxTokens       int      `json:"max_tokens"`
		MaxDocuments    int      `json:"max_documents"`
		WorkspacePath   string   `json:"workspace_path"`
		IncludePatterns []string `json:"include_patterns"`
		ExcludePatterns []string `json:"exclude_patterns"`
		ObjectiveStyle  string   `json:"objective_style"`
	}{
		Query:           req.Query,
		MaxTokens:       req.MaxTokens,
		MaxDocuments:    req.MaxDocuments,
		WorkspacePath:   req.WorkspacePath,
		IncludePatterns: req.IncludePatterns,
		ExcludePatterns: req.ExcludePatterns,
		ObjectiveStyle:  req.ObjectiveStyle,
	}
	
	jsonData, _ := json.Marshal(data)
	hash := sha256.Sum256(jsonData)
	return hex.EncodeToString(hash[:])
}
