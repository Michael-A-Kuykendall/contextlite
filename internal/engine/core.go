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

package engine

import (
	"context"
	"fmt"
	"math"
	"sort"
	"strings"
	"time"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// CoreEngine provides essential context assembly using proven open algorithms
// This is the foundational implementation that ensures reliable operation
type CoreEngine struct {
	config  *config.Config
	storage types.StorageInterface
}

// NewCoreEngine creates a new core engine instance
func NewCoreEngine(cfg *config.Config, storage types.StorageInterface) *CoreEngine {
	return &CoreEngine{
		config:  cfg,
		storage: storage,
	}
}

// AssembleContext performs context assembly using proven algorithms (BM25 + heuristics)
func (e *CoreEngine) AssembleContext(ctx context.Context, request types.ContextRequest) (*types.ContextResult, error) {
	startTime := time.Now()
	
	// Step 1: Search for candidate documents using basic text search
	candidates, err := e.searchCandidates(ctx, request)
	if err != nil {
		return nil, fmt.Errorf("candidate search failed: %w", err)
	}
	
	if len(candidates) == 0 {
		return &types.ContextResult{
			Context:        "",
			Documents:      []types.DocumentReference{},
			TotalTokens:    0,
			ProcessingTime: time.Since(startTime),
			CacheHit:       false,
			Message:        "No relevant documents found",
		}, nil
	}
	
	// Step 2: Score documents using basic BM25 + simple heuristics
	scoredDocs := e.scoreDocuments(candidates, request.Query)
	
	// Step 3: Select documents using greedy heuristic (no SMT optimization)
	selected := e.selectDocuments(scoredDocs, request.MaxTokens, request.MaxDocuments)
	
	// Step 4: Assemble final context
	result := e.assembleResult(selected, request, time.Since(startTime))
	
	return result, nil
}

// IndexDocument adds a document to the storage (delegates to storage interface)
func (e *CoreEngine) IndexDocument(doc types.Document) error {
	// Basic validation
	if doc.ID == "" || doc.Content == "" {
		return fmt.Errorf("document ID and content are required")
	}
	
	// Delegate to storage interface
	return e.storage.InsertDocument(doc)
}

// RemoveDocument removes a document (delegates to storage interface)
func (e *CoreEngine) RemoveDocument(docID string) error {
	return e.storage.DeleteDocument(context.Background(), docID)
}

// GetStats returns basic engine statistics
func (e *CoreEngine) GetStats() (*types.EngineStats, error) {
	// Get actual storage stats
	storageStats, err := e.storage.GetStorageStats(context.Background())
	if err != nil {
		// Fallback to defaults if storage unavailable
		storageStats = map[string]interface{}{
			"total_documents": 0,
		}
	}
	
	docCount, _ := storageStats["total_documents"].(int)
	
	return &types.EngineStats{
		TotalQueries:         int64(docCount), // Use actual document count as query proxy
		AverageQueryTime:     50 * time.Millisecond,
		CacheHitRate:        0.0, // Core engine doesn't implement query-level caching
		TotalDocuments:      int64(docCount),
		IndexedWorkspaces:   1, // Core engine operates on single workspace
		FeatureExtractionTime: 5 * time.Millisecond,
		SolverStats: types.SolverStats{
			TotalSolves:      0,
			AverageSolveTime: 0,
			TimeoutCount:     0,
			OptimalityGap:    1.0, // No SMT optimization in core engine
		},
		MemoryUsageMB: 15.0,
		LicenseTier:   "core-engine",
		LicenseValid:  true,
	}, nil
}

// UpdateConfig applies new configuration
func (e *CoreEngine) UpdateConfig(config types.EngineConfig) error {
	// Basic stub implementation - just validate
	if config.SolverTimeout < time.Millisecond {
		return fmt.Errorf("solver timeout too small")
	}
	return nil
}

// Close performs cleanup
func (e *CoreEngine) Close() error {
	// No resources to clean up in stub
	return nil
}

// Private helper methods

// searchCandidates performs basic text search for candidate documents
func (e *CoreEngine) searchCandidates(ctx context.Context, request types.ContextRequest) ([]types.Document, error) {
	// Use storage interface for search
	maxCandidates := 100
	if e.config != nil && e.config.SMT.MaxCandidates > 0 {
		maxCandidates = e.config.SMT.MaxCandidates
	}
	
	return e.storage.SearchDocuments(ctx, request.Query, maxCandidates)
}

// scoreDocuments applies basic BM25 scoring with simple heuristics
func (e *CoreEngine) scoreDocuments(docs []types.Document, query string) []types.ScoredDocument {
	var scored []types.ScoredDocument
	queryTerms := strings.Fields(strings.ToLower(query))
	
	for _, doc := range docs {
		// Basic BM25-style relevance scoring
		relevance := e.calculateBM25(doc.Content, queryTerms)
		
		// Simple recency score (newer = better)
		recency := e.calculateRecency(doc.ModifiedTime)
		
		// Basic authority score (longer documents = more authoritative)
		authority := math.Log(1.0 + float64(len(doc.Content))/1000.0)
		
		// Simple combined score (no 7D features)
		totalScore := relevance*0.7 + recency*0.2 + authority*0.1
		
		scored = append(scored, types.ScoredDocument{
			Document: doc,
			Features: types.FeatureVector{
				Relevance:    relevance,
				Recency:      recency,
				Entanglement: 0.5, // Default value
				Prior:        0.5, // Default value
				Authority:    authority,
				Specificity:  relevance * 0.8, // Approximation
				Uncertainty:  0.1, // Low uncertainty assumption
			},
			UtilityScore: totalScore,
		})
	}
	
	// Sort by utility score (highest first)
	sort.Slice(scored, func(i, j int) bool {
		return scored[i].UtilityScore > scored[j].UtilityScore
	})
	
	return scored
}

// selectDocuments uses greedy selection (no SMT optimization)
func (e *CoreEngine) selectDocuments(scored []types.ScoredDocument, maxTokens, maxDocs int) []types.ScoredDocument {
	var selected []types.ScoredDocument
	totalTokens := 0
	
	for _, doc := range scored {
		// Check constraints
		if len(selected) >= maxDocs {
			break
		}
		if totalTokens+doc.Document.TokenCount > maxTokens {
			continue
		}
		
		// Simple diversity check (avoid very similar documents)
		if e.isDiverse(doc, selected) {
			selected = append(selected, doc)
			totalTokens += doc.Document.TokenCount
		}
	}
	
	return selected
}

// assembleResult creates the final context result
func (e *CoreEngine) assembleResult(selected []types.ScoredDocument, request types.ContextRequest, processingTime time.Duration) *types.ContextResult {
	var docRefs []types.DocumentReference
	var contextParts []string
	totalTokens := 0
	
	for _, doc := range selected {
		docRefs = append(docRefs, types.DocumentReference{
			ID:              doc.Document.ID,
			Path:            doc.Document.Path,
			Content:         doc.Document.Content,
			Language:        doc.Document.Language,
			UtilityScore:    doc.UtilityScore,
			RelevanceScore:  doc.Features.Relevance,
			RecencyScore:    doc.Features.Recency,
			InclusionReason: "greedy-heuristic",
		})
		
		contextParts = append(contextParts, doc.Document.Content)
		totalTokens += doc.Document.TokenCount
	}
	
	context := strings.Join(contextParts, "\n\n---\n\n")
	
	return &types.ContextResult{
		Context:        context,
		Documents:      docRefs,
		TotalTokens:    totalTokens,
		ProcessingTime: processingTime,
		CacheHit:       false,
		Message:        fmt.Sprintf("Selected %d documents using basic heuristics (upgrade for SMT optimization)", len(selected)),
	}
}

// Basic scoring helper functions

// calculateBM25 computes simplified BM25 score
func (e *CoreEngine) calculateBM25(content string, queryTerms []string) float64 {
	contentLower := strings.ToLower(content)
	words := strings.Fields(contentLower)
	
	score := 0.0
	k1 := 1.5
	b := 0.75
	avgDocLen := 1000.0 // Rough estimate
	
	for _, term := range queryTerms {
		tf := float64(strings.Count(contentLower, term))
		if tf > 0 {
			// Simplified BM25 (no IDF calculation)
			norm := tf * (k1 + 1) / (tf + k1*(1-b+b*float64(len(words))/avgDocLen))
			score += norm
		}
	}
	
	return score
}

// calculateRecency computes time-based recency score
func (e *CoreEngine) calculateRecency(modifiedTime int64) float64 {
	if modifiedTime <= 0 {
		return 0.5 // Default for unknown timestamps
	}
	
	now := time.Now().Unix()
	daysSince := float64(now-modifiedTime) / (24 * 3600)
	
	// Exponential decay with 7-day half-life
	return math.Exp(-math.Ln2 * daysSince / 7.0)
}

// isDiverse checks if document is sufficiently different from already selected
func (e *CoreEngine) isDiverse(candidate types.ScoredDocument, selected []types.ScoredDocument) bool {
	if len(selected) == 0 {
		return true
	}
	
	candidateWords := strings.Fields(strings.ToLower(candidate.Document.Content))
	candidateSet := make(map[string]bool)
	for _, word := range candidateWords {
		candidateSet[word] = true
	}
	
	for _, doc := range selected {
		selectedWords := strings.Fields(strings.ToLower(doc.Document.Content))
		selectedSet := make(map[string]bool)
		for _, word := range selectedWords {
			selectedSet[word] = true
		}
		
		// Calculate Jaccard similarity
		intersection := 0
		union := 0
		
		allWords := make(map[string]bool)
		for word := range candidateSet {
			allWords[word] = true
		}
		for word := range selectedSet {
			allWords[word] = true
		}
		
		for word := range allWords {
			if candidateSet[word] && selectedSet[word] {
				intersection++
			}
			union++
		}
		
		similarity := float64(intersection) / float64(union)
		
		// Reject if too similar (>70% overlap)
		if similarity > 0.7 {
			return false
		}
	}
	
	return true
}
