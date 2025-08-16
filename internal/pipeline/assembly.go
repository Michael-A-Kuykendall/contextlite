package pipeline

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"time"

	"contextlite/internal/features"
	"contextlite/internal/smt"
	"contextlite/internal/storage"
	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// Pipeline provides the main context assembly pipeline
type Pipeline struct {
	storage *storage.Storage
	config  *config.Config
}

// New creates a new pipeline instance
func New(storage *storage.Storage, config *config.Config) *Pipeline {
	return &Pipeline{
		storage: storage,
		config:  config,
	}
}

// AssembleContext performs the complete context assembly pipeline
func (p *Pipeline) AssembleContext(ctx context.Context, req *types.AssembleRequest) (*types.QueryResult, error) {
	startTime := time.Now()
	var timings types.StageTimings
	
	// Check cache first if enabled
	if req.UseCache {
		if cached, err := p.getCachedResult(ctx, req); err == nil && cached != nil {
			cached.CacheHit = true
			return cached, nil
		}
	}
	
	// Stage 1: FTS Harvest - search for candidate documents
	ftsStart := time.Now()
	candidates, err := p.harvestCandidates(ctx, req)
	if err != nil {
		return nil, fmt.Errorf("failed to harvest candidates: %w", err)
	}
	timings.FTSHarvestMs = int(time.Since(ftsStart).Milliseconds())
	
	if len(candidates) == 0 {
		return &types.QueryResult{
			Query:      req.Query,
			Documents:  []types.DocumentReference{},
			Timings:    timings,
			CacheHit:   false,
		}, nil
	}
	
	// Stage 2: Feature Extraction - compute 7D features
	featureStart := time.Now()
	scoredDocs, err := p.extractFeatures(ctx, candidates, req)
	if err != nil {
		return nil, fmt.Errorf("failed to extract features: %w", err)
	}
	timings.FeatureBuildMs = int(time.Since(featureStart).Milliseconds())
	
	// Stage 3: SMT Optimization - select optimal document set
	smtStart := time.Now()
	smtResult, err := p.optimizeSelection(ctx, scoredDocs, req)
	if err != nil {
		return nil, fmt.Errorf("failed to optimize selection: %w", err)
	}
	timings.SMTSolverMs = int(time.Since(smtStart).Milliseconds())
	
	// Stage 4: Assemble final result
	result := p.assembleResult(req, scoredDocs, smtResult, timings)
	result.Timings.TotalMs = int(time.Since(startTime).Milliseconds())
	
	// Cache result if enabled and high quality
	if req.UseCache && result.CoherenceScore > 0.5 {
		p.cacheResult(ctx, req, result)
	}
	
	return result, nil
}

// harvestCandidates performs FTS search to get candidate documents
func (p *Pipeline) harvestCandidates(ctx context.Context, req *types.AssembleRequest) ([]types.Document, error) {
	// Determine search limit (more candidates = better optimization but slower)
	searchLimit := p.config.SMT.MaxCandidates
	if searchLimit <= 0 {
		searchLimit = 200
	}
	
	// Perform FTS search
	docs, err := p.storage.SearchDocuments(ctx, req.Query, searchLimit)
	if err != nil {
		return nil, err
	}
	
	// Filter by workspace path if specified
	if req.WorkspacePath != "" {
		filtered := make([]types.Document, 0, len(docs))
		for _, doc := range docs {
			if p.matchesWorkspace(doc.Path, req.WorkspacePath) {
				filtered = append(filtered, doc)
			}
		}
		docs = filtered
	}
	
	// Apply include/exclude patterns
	docs = p.applyPatternFilters(docs, req.IncludePatterns, req.ExcludePatterns)
	
	return docs, nil
}

// extractFeatures computes 7D features for all candidate documents
func (p *Pipeline) extractFeatures(ctx context.Context, docs []types.Document, req *types.AssembleRequest) ([]types.ScoredDocument, error) {
	// Get workspace-specific normalization stats
	normStats, err := p.getNormalizationStats(ctx, req.WorkspacePath)
	if err != nil {
		// Continue without normalization if stats unavailable
		normStats = nil
	}
	
	// Create feature extractor
	extractor := features.NewFeatureExtractor(req.WorkspacePath, normStats)
	
	// Extract features
	return extractor.ExtractFeatures(ctx, docs, req.Query)
}

// optimizeSelection performs SMT-based document selection
func (p *Pipeline) optimizeSelection(ctx context.Context, scoredDocs []types.ScoredDocument, req *types.AssembleRequest) (*smt.SMTResult, error) {
	// Get workspace-specific weights
	weights, err := p.getWorkspaceWeights(ctx, req.WorkspacePath)
	if err != nil {
		// Use default weights if workspace weights unavailable
		weights = p.getDefaultWeights()
	}
	
	// Create SMT solver config
	smtConfig := smt.SMTConfig{
		TimeoutMs:      req.SMTTimeoutMs,
		MaxOptGap:      req.MaxOptGap,
		MaxCandidates:  p.config.SMT.MaxCandidates,
		MaxPairsPerDoc: p.config.SMT.MaxPairsPerDoc,
		IntegerScaling: p.config.SMT.IntegerScaling,
		ObjectiveStyle: req.ObjectiveStyle,
		Weights:        *weights,
	}
	
	// Apply defaults for missing request parameters
	if smtConfig.TimeoutMs <= 0 {
		smtConfig.TimeoutMs = p.config.SMT.SolverTimeoutMs
	}
	if smtConfig.MaxOptGap <= 0 {
		smtConfig.MaxOptGap = p.config.SMT.MaxOptGap
	}
	if smtConfig.ObjectiveStyle == "" {
		smtConfig.ObjectiveStyle = p.config.SMT.ObjectiveStyle
	}
	
	// Create solver and optimize
	solver := smt.NewSMTSolver(smtConfig)
	return solver.OptimizeSelection(ctx, scoredDocs, req.MaxTokens, req.MaxDocuments)
}

// assembleResult creates the final query result
func (p *Pipeline) assembleResult(req *types.AssembleRequest, 
	scoredDocs []types.ScoredDocument, 
	smtResult *smt.SMTResult, 
	timings types.StageTimings) *types.QueryResult {
	
	// Build document references for selected documents
	var docRefs []types.DocumentReference
	totalTokens := 0
	
	for _, idx := range smtResult.SelectedDocs {
		if idx >= 0 && idx < len(scoredDocs) {
			doc := scoredDocs[idx]
			totalTokens += doc.Document.TokenCount
			
			docRefs = append(docRefs, types.DocumentReference{
				ID:              doc.Document.ID,
				Path:            doc.Document.Path,
				Content:         doc.Document.Content,
				Language:        doc.Document.Language,
				UtilityScore:    doc.UtilityScore,
				RelevanceScore:  doc.Features.Relevance,
				RecencyScore:    doc.Features.Recency,
				DiversityScore:  1.0 - doc.Features.Uncertainty, // Approximation
				InclusionReason: "smt-optimized",
			})
		}
	}
	
	// Compute coherence score
	coherenceScore := p.computeCoherenceScore(scoredDocs, smtResult.SelectedDocs)
	
	// Build SMT metrics
	smtMetrics := types.SMTMetrics{
		SolverUsed:      smtResult.SolverUsed,
		OptimalityGap:   smtResult.OptimalityGap,
		SolveTimeMs:     smtResult.SolveTimeMs,
		VariableCount:   smtResult.VariableCount,
		ConstraintCount: smtResult.ConstraintCount,
		FallbackReason:  smtResult.FallbackReason,
	}
	
	return &types.QueryResult{
		Query:          req.Query,
		Documents:      docRefs,
		TotalDocuments: len(docRefs),
		TotalTokens:    totalTokens,
		CoherenceScore: coherenceScore,
		SMTMetrics:     smtMetrics,
		Timings:        timings,
		CacheHit:       false,
	}
}

// getCachedResult checks for cached query results
func (p *Pipeline) getCachedResult(ctx context.Context, req *types.AssembleRequest) (*types.QueryResult, error) {
	// Generate cache key
	queryHash := p.hashQuery(req)
	corpusHash, err := p.storage.GetCorpusHash(ctx)
	if err != nil {
		return nil, err
	}
	
	modelID := req.ModelID
	if modelID == "" {
		modelID = p.config.Tokenizer.ModelID
	}
	
	tokenizerVersion := "1.0" // TODO: Get actual tokenizer version
	
	return p.storage.GetQueryCache(ctx, queryHash, corpusHash, modelID, tokenizerVersion)
}

// cacheResult saves query result to cache
func (p *Pipeline) cacheResult(ctx context.Context, req *types.AssembleRequest, result *types.QueryResult) {
	queryHash := p.hashQuery(req)
	corpusHash, err := p.storage.GetCorpusHash(ctx)
	if err != nil {
		return
	}
	
	modelID := req.ModelID
	if modelID == "" {
		modelID = p.config.Tokenizer.ModelID
	}
	
	tokenizerVersion := "1.0"
	
	// Cache for configured TTL
	ttl := time.Duration(req.CacheTTL) * time.Minute
	if ttl <= 0 {
		ttl = time.Duration(p.config.Cache.L2TTLMinutes) * time.Minute
	}
	expiresAt := time.Now().Add(ttl)
	
	p.storage.SaveQueryCache(ctx, queryHash, corpusHash, modelID, tokenizerVersion, result, expiresAt)
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

// Helper functions

func (p *Pipeline) matchesWorkspace(docPath, workspacePath string) bool {
	if workspacePath == "" {
		return true
	}
	// Simple prefix matching - could be enhanced
	return len(docPath) >= len(workspacePath) && docPath[:len(workspacePath)] == workspacePath
}

func (p *Pipeline) applyPatternFilters(docs []types.Document, include, exclude []string) []types.Document {
	// TODO: Implement glob pattern matching
	// For now, just return all docs
	return docs
}

func (p *Pipeline) getNormalizationStats(ctx context.Context, workspacePath string) (*types.NormalizationStats, error) {
	weights, err := p.storage.GetWorkspaceWeights(ctx, workspacePath)
	if err != nil {
		return nil, err
	}
	
	if weights.NormalizationStats == "" {
		return nil, fmt.Errorf("no normalization stats available")
	}
	
	var stats types.NormalizationStats
	err = json.Unmarshal([]byte(weights.NormalizationStats), &stats)
	return &stats, err
}

func (p *Pipeline) getWorkspaceWeights(ctx context.Context, workspacePath string) (*smt.WeightConfig, error) {
	weights, err := p.storage.GetWorkspaceWeights(ctx, workspacePath)
	if err != nil {
		return p.getDefaultWeights(), nil // Use defaults if not found
	}
	
	return &smt.WeightConfig{
		Relevance:         weights.RelevanceWeight,
		Recency:          weights.RecencyWeight,
		Entanglement:     weights.EntanglementWeight,
		Prior:            0.15, // Not stored separately yet
		Authority:        0.10, // Not stored separately yet
		Specificity:      0.05, // Not stored separately yet
		Uncertainty:      0.05, // Not stored separately yet
		RedundancyPenalty: weights.RedundancyPenalty,
		CoherenceBonus:   0.2,  // Default
	}, nil
}

func (p *Pipeline) getDefaultWeights() *smt.WeightConfig {
	return &smt.WeightConfig{
		Relevance:         p.config.Weights.Relevance,
		Recency:          p.config.Weights.Recency,
		Entanglement:     p.config.Weights.Entanglement,
		Prior:            p.config.Weights.Prior,
		Authority:        p.config.Weights.Authority,
		Specificity:      p.config.Weights.Specificity,
		Uncertainty:      p.config.Weights.Uncertainty,
		RedundancyPenalty: p.config.Weights.RedundancyPenalty,
		CoherenceBonus:   p.config.Weights.CoherenceBonus,
	}
}

func (p *Pipeline) computeCoherenceScore(scoredDocs []types.ScoredDocument, selected []int) float64 {
	if len(selected) <= 1 {
		return 1.0
	}
	
	// Simple coherence approximation based on feature similarity
	totalCoherence := 0.0
	pairs := 0
	
	for i := 0; i < len(selected); i++ {
		for j := i + 1; j < len(selected); j++ {
			if selected[i] < len(scoredDocs) && selected[j] < len(scoredDocs) {
				doc1 := scoredDocs[selected[i]]
				doc2 := scoredDocs[selected[j]]
				
				// Compute feature vector similarity
				similarity := p.featureSimilarity(doc1.Features, doc2.Features)
				totalCoherence += similarity
				pairs++
			}
		}
	}
	
	if pairs > 0 {
		return totalCoherence / float64(pairs)
	}
	return 0.5
}

func (p *Pipeline) featureSimilarity(f1, f2 types.FeatureVector) float64 {
	// Compute cosine similarity of feature vectors
	vec1 := []float64{f1.Relevance, f1.Recency, f1.Entanglement, f1.Prior, f1.Authority, f1.Specificity, f1.Uncertainty}
	vec2 := []float64{f2.Relevance, f2.Recency, f2.Entanglement, f2.Prior, f2.Authority, f2.Specificity, f2.Uncertainty}
	
	dotProduct := 0.0
	norm1 := 0.0
	norm2 := 0.0
	
	for i := 0; i < len(vec1); i++ {
		dotProduct += vec1[i] * vec2[i]
		norm1 += vec1[i] * vec1[i]
		norm2 += vec2[i] * vec2[i]
	}
	
	if norm1 == 0 || norm2 == 0 {
		return 0.0
	}
	
	return dotProduct / (norm1 * norm2)
}
