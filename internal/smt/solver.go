package optimization

import (
	"context"
	"fmt"
	"math"
	"sort"

	"contextlite/internal/features"
	"contextlite/internal/solve"
	"contextlite/internal/timing"
	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// optimizationSolver provides Advanced context selection using optimizer
type optimizationSolver struct {
	config      *config.Config
	z3Optimizer *solve.optimizerOptimizer
	verifier    *solve.BruteForceVerifier
}

// optimizationResult represents the result of optimization optimization
type optimizationResult struct {
	SelectedDocs    []int               `json:"selected_docs"`
	ObjectiveValue  float64             `json:"objective_value"`
	Objective       int                 `json:"objective"`        // Integer objective from optimizer
	SolveTimeUs     int64               `json:"solve_time_us"`    // Pure solver time in microseconds
	SolveTimeMs     int                 `json:"solve_time_ms"`    // Legacy compatibility
	VariableCount   int                 `json:"variable_count"`
	ConstraintCount int                 `json:"budget_count"`
	KCandidates     int                 `json:"K_candidates"`
	PairsCount      int                 `json:"pairs_count"`
	BudgetTokens    int                 `json:"budget_tokens"`
	MaxDocs         int                 `json:"max_docs"`
	SolverUsed      string              `json:"solver_used"`
	optimizerStatus        string              `json:"z3_status,omitempty"`      // optimizer result: sat/unsat/unknown/timeout
	FallbackReason  string              `json:"fallback_reason,omitempty"`
	TimedOut        bool                `json:"timed_out"`
	Verified        bool                `json:"verified,omitempty"`
}

// NewoptimizationSolver creates a new optimization system
func NewoptimizationSolver(cfg *config.Config) (*optimizationSolver, error) {
	// Verify optimizer is available if configured
	if cfg.optimization.optimizer.BinaryPath != "" {
		if err := solve.CheckoptimizerAvailable(cfg.optimization.optimizer.BinaryPath); err != nil {
			return nil, fmt.Errorf("optimizer not available: %w", err)
		}
	}

	solver := &optimizationSolver{
		config:      cfg,
		z3Optimizer: solve.NewoptimizerOptimizer(cfg.optimization.optimizer.BinaryPath, cfg.optimization.SolverTimeoutMs),
		verifier:    solve.NewBruteForceVerifier(),
	}
	
	return solver, nil
}

// OptimizeSelection performs Advanced document selection using optimizer
func (s *optimizationSolver) OptimizeSelection(ctx context.Context, 
	scoredDocs []types.ScoredDocument, 
	maxTokens int, 
	maxDocs int) (*optimizationResult, error) {
	
	// Limit candidates to keep optimization model manageable
	candidates := scoredDocs
	if len(candidates) > s.config.optimization.MaxCandidates {
		candidates = s.selectTopCandidates(scoredDocs, s.config.optimization.MaxCandidates)
	}
	
	// Compute pairwise similarities for top-M neighbors
	simComputer := features.NewSimilarityComputer(s.config.optimization.MaxPairsPerDoc)
	pairs := simComputer.ComputePairwiseScores(candidates)
	
	// Convert to optimizer format
	z3Pairs := s.convertPairsForoptimizer(pairs)
	
	// Try optimizer optimization first
	z3Result, err := s.z3Optimizer.OptimizeDocumentSelection(ctx, candidates, z3Pairs, maxTokens, maxDocs)
	
	var result *optimizationResult
	if err != nil || z3Result.Status != "sat" {
		// Fallback to appropriate algorithm based on ObjectiveStyle
		fallbackTimer := timing.Start()
		fallbackReason := fmt.Sprintf("optimizer failed: %v", err)
		if z3Result != nil {
			if z3Result.TimedOut {
				fallbackReason = "optimizer timeout"
			} else if z3Result.Status == "unsat" {
				fallbackReason = "Problem unsatisfiable"
			}
		}
		
		// Dispatch to appropriate solver based on ObjectiveStyle
		var solverErr error
		switch s.config.optimization.ObjectiveStyle {
		case "weighted-sum":
			result, solverErr = s.solveWeightedSum(candidates, pairs, maxTokens, maxDocs)
		case "lexicographic":
			result, solverErr = s.solveLexicographic(candidates, pairs, maxTokens, maxDocs)
		case "epsilon-budget":
			result, solverErr = s.solveEpsilonConstraint(candidates, pairs, maxTokens, maxDocs)
		case "greedy-weighted":
			result, solverErr = s.greedyWeightedSelection(candidates, pairs, maxTokens, maxDocs, "greedy-weighted")
		case "greedy-constrained":
			result, solverErr = s.greedyConstrainedSelection(candidates, pairs, maxTokens, maxDocs)
		default:
			// Default to MMR fallback for unknown styles
			result = s.fallbackMMR(candidates, pairs, maxTokens, maxDocs)
			solverErr = nil
		}
		
		// If solver failed, use MMR fallback
		if solverErr != nil {
			result = s.fallbackMMR(candidates, pairs, maxTokens, maxDocs)
		}
		
		fallbackUs := fallbackTimer.Us()
		result.FallbackReason = fallbackReason
		result.SolveTimeUs = fallbackUs
		result.SolveTimeMs = int(float64(fallbackUs) / 1_000.0)
	} else {
		// optimizer succeeded
		result = &optimizationResult{
			SelectedDocs:    z3Result.SelectedDocs,
			ObjectiveValue:  float64(z3Result.ObjectiveValue) / 10000.0, // Unscaled for compatibility
			Objective:       z3Result.ObjectiveValue,                    // Integer objective from optimizer
			SolveTimeUs:     z3Result.SolveTimeUs,
			SolveTimeMs:     int(float64(z3Result.SolveTimeUs) / 1_000.0),
			VariableCount:   z3Result.VariableCount,
			ConstraintCount: z3Result.ConstraintCount,
			KCandidates:     len(candidates),
			PairsCount:      len(pairs),
			BudgetTokens:    maxTokens,
			MaxDocs:         maxDocs,
			SolverUsed:      "z3opt",
			optimizerStatus:        z3Result.Status,
			TimedOut:        z3Result.TimedOut,
		}
		
		// Optional verification for small problems
		if s.config.optimization.optimizer.EnableVerification && len(candidates) <= s.config.optimization.optimizer.MaxVerificationDocs {
			if verification, err := s.verifier.VerifyOptimality(candidates, z3Pairs, maxTokens, maxDocs, z3Result); err == nil {
				result.Verified = verification.IsOptimal
			}
		}
	}
	
	return result, nil
}

// convertPairsForoptimizer converts feature pairs to optimizer format
func (s *optimizationSolver) convertPairsForoptimizer(pairs []features.DocumentPair) []solve.DocumentPair {
	z3Pairs := make([]solve.DocumentPair, len(pairs))
	for i, pair := range pairs {
		z3Pairs[i] = solve.DocumentPair{
			DocI:             pair.DocI,
			DocJ:             pair.DocJ,
			Similarity:       pair.Similarity,
			RedundancyPenalty: s.config.Weights.RedundancyPenalty * pair.Redundancy,
			CoherenceBonus:   s.config.Weights.CoherenceBonus * pair.Coherence,
		}
	}
	return z3Pairs
}

// solveWeightedSum implements weighted-sum scalarization (LEGACY FALLBACK)
func (s *optimizationSolver) solveWeightedSum(docs []types.ScoredDocument, 
	pairs []features.DocumentPair, 
	maxTokens, maxDocs int) (*optimizationResult, error) {
	
	// Legacy greedy implementation for backwards compatibility
	// Primary optimization now uses optimizer in OptimizeSelection()
	
	return s.greedyWeightedSelection(docs, pairs, maxTokens, maxDocs, "weighted-sum")
}

// solveLexicographic implements lexicographic optimization
func (s *optimizationSolver) solveLexicographic(docs []types.ScoredDocument,
	pairs []features.DocumentPair,
	maxTokens, maxDocs int) (*optimizationResult, error) {
	
	// Compute tier multipliers for strict dominance
	multipliers := s.computeTierMultipliers()
	
	// Create lexicographic utility scores
	for i := range docs {
		features := docs[i].Features
		docs[i].UtilityScore = 
			multipliers[0]*features.Relevance +
			multipliers[1]*features.Recency +
			multipliers[2]*features.Entanglement +
			multipliers[3]*features.Prior +
			multipliers[4]*features.Authority +
			multipliers[5]*features.Specificity +
			multipliers[6]*(1.0-features.Uncertainty)
	}
	
	return s.greedyWeightedSelection(docs, pairs, maxTokens, maxDocs, "lexicographic")
}

// solveEpsilonConstraint implements ε-budget method
func (s *optimizationSolver) solveEpsilonConstraint(docs []types.ScoredDocument,
	pairs []features.DocumentPair,
	maxTokens, maxDocs int) (*optimizationResult, error) {
	
	// Primary objective: maximize relevance
	// Constraints: limit redundancy, ensure coherence
	
	return s.greedyConstrainedSelection(docs, pairs, maxTokens, maxDocs)
}

// greedyWeightedSelection implements MMR-style greedy selection
func (s *optimizationSolver) greedyWeightedSelection(docs []types.ScoredDocument,
	pairs []features.DocumentPair,
	maxTokens, maxDocs int, 
	method string) (*optimizationResult, error) {
	
	var selected []int
	totalTokens := 0
	usedIndices := make(map[int]bool)
	
	// Build pairwise similarity lookup
	similarity := make(map[string]float64)
	for _, pair := range pairs {
		key := fmt.Sprintf("%d-%d", pair.DocI, pair.DocJ)
		similarity[key] = pair.Similarity
		// Add reverse direction
		key = fmt.Sprintf("%d-%d", pair.DocJ, pair.DocI)
		similarity[key] = pair.Similarity
	}
	
	// Greedy selection with diversification
	for len(selected) < maxDocs {
		bestIdx := -1
		bestScore := -math.Inf(1)
		
		for i, doc := range docs {
			if usedIndices[i] {
				continue
			}
			
			// Check token budget
			if totalTokens+doc.Document.TokenCount > maxTokens {
				continue
			}
			
			// Base utility score
			score := doc.UtilityScore
			
			// Apply diversification penalty
			diversityPenalty := 0.0
			for _, selectedIdx := range selected {
				key := fmt.Sprintf("%d-%d", i, selectedIdx)
				if sim, exists := similarity[key]; exists {
					diversityPenalty += s.config.Weights.RedundancyPenalty * sim
				}
			}
			
			// Apply coherence bonus
			coherenceBonus := 0.0
			for _, selectedIdx := range selected {
				key := fmt.Sprintf("%d-%d", i, selectedIdx)
				if sim, exists := similarity[key]; exists {
					// Use concept overlap for coherence (approximated by similarity)
					coherenceBonus += s.config.Weights.CoherenceBonus * sim
				}
			}
			
			finalScore := score - diversityPenalty + coherenceBonus
			
			if finalScore > bestScore {
				bestScore = finalScore
				bestIdx = i
			}
		}
		
		if bestIdx == -1 {
			break // No more valid documents
		}
		
		selected = append(selected, bestIdx)
		totalTokens += docs[bestIdx].Document.TokenCount
		usedIndices[bestIdx] = true
	}
	
	return &optimizationResult{
		SelectedDocs:    selected,
		ObjectiveValue:  s.computeObjectiveValue(docs, selected, pairs),
		Objective:       0,  // No integer objective for fallback
		SolveTimeMs:     0,
		VariableCount:   0,  // No optimization variables for fallback
		ConstraintCount: 0,  // No optimization budgets for fallback
		KCandidates:     len(docs),
		PairsCount:      len(pairs),
		BudgetTokens:    maxTokens,
		MaxDocs:         maxDocs,
		SolverUsed:      method,
		FallbackReason:  "z3_not_available",
	}, nil
}

// greedyConstrainedSelection implements ε-budget greedy selection
func (s *optimizationSolver) greedyConstrainedSelection(docs []types.ScoredDocument,
	pairs []features.DocumentPair,
	maxTokens, maxDocs int) (*optimizationResult, error) {
	
	// Sort by relevance (primary objective)
	relevanceSorted := make([]int, len(docs))
	for i := range relevanceSorted {
		relevanceSorted[i] = i
	}
	
	sort.Slice(relevanceSorted, func(i, j int) bool {
		return docs[relevanceSorted[i]].Features.Relevance > docs[relevanceSorted[j]].Features.Relevance
	})
	
	var selected []int
	totalTokens := 0
	totalRedundancy := 0.0
	totalCoherence := 0.0
	
	// Build similarity lookup
	similarity := make(map[string]float64)
	for _, pair := range pairs {
		key := fmt.Sprintf("%d-%d", pair.DocI, pair.DocJ)
		similarity[key] = pair.Redundancy
	}
	
	// Greedy selection with budget checking
	for _, idx := range relevanceSorted {
		if len(selected) >= maxDocs {
			break
		}
		
		doc := docs[idx]
		if totalTokens+doc.Document.TokenCount > maxTokens {
			continue
		}
		
		// Check budget violations
		newRedundancy := totalRedundancy
		newCoherence := totalCoherence
		
		for _, selectedIdx := range selected {
			key := fmt.Sprintf("%d-%d", idx, selectedIdx)
			if sim, exists := similarity[key]; exists {
				newRedundancy += sim
				newCoherence += sim // Approximation
			}
		}
		
		// ε-budget thresholds (from config)
		maxRedundancy := 0.4 * float64(len(selected)+1) // Per-pair average
		
		if newRedundancy <= maxRedundancy {
			selected = append(selected, idx)
			totalTokens += doc.Document.TokenCount
			totalRedundancy = newRedundancy
			totalCoherence = newCoherence
		}
	}
	
	return &optimizationResult{
		SelectedDocs:    selected,
		ObjectiveValue:  s.computeObjectiveValue(docs, selected, pairs),
		Objective:       0,  // No integer objective for fallback
		SolveTimeMs:     0,
		VariableCount:   0,  // No optimization variables for fallback
		ConstraintCount: 0,  // No optimization budgets for fallback
		KCandidates:     len(docs),
		PairsCount:      len(pairs),
		BudgetTokens:    maxTokens,
		MaxDocs:         maxDocs,
		SolverUsed:      "epsilon-budget",
		FallbackReason:  "z3_not_available",
	}, nil
}

// fallbackMMR provides MMR fallback when optimization fails
func (s *optimizationSolver) fallbackMMR(docs []types.ScoredDocument,
	pairs []features.DocumentPair,
	maxTokens, maxDocs int) *optimizationResult {
	
	// Simple MMR implementation
	lambda := 0.7 // Balance between relevance and diversity
	
	var selected []int
	totalTokens := 0
	usedIndices := make(map[int]bool)
	
	for len(selected) < maxDocs {
		bestIdx := -1
		bestScore := -math.Inf(1)
		
		for i, doc := range docs {
			if usedIndices[i] {
				continue
			}
			
			if totalTokens+doc.Document.TokenCount > maxTokens {
				continue
			}
			
			// MMR score: λ * relevance - (1-λ) * max_similarity_to_selected
			relevance := doc.Features.Relevance
			maxSim := 0.0
			
			for _, selectedIdx := range selected {
				for _, pair := range pairs {
					if (pair.DocI == i && pair.DocJ == selectedIdx) ||
					   (pair.DocI == selectedIdx && pair.DocJ == i) {
						if pair.Similarity > maxSim {
							maxSim = pair.Similarity
						}
					}
				}
			}
			
			score := lambda*relevance - (1-lambda)*maxSim
			
			if score > bestScore {
				bestScore = score
				bestIdx = i
			}
		}
		
		if bestIdx == -1 {
			break
		}
		
		selected = append(selected, bestIdx)
		totalTokens += docs[bestIdx].Document.TokenCount
		usedIndices[bestIdx] = true
	}
	
	return &optimizationResult{
		SelectedDocs:    selected,
		ObjectiveValue:  s.computeObjectiveValue(docs, selected, pairs),
		Objective:       0,  // No integer objective for fallback
		SolveTimeUs:     0,  // Will be set by caller
		SolveTimeMs:     0,  // Will be set by caller
		VariableCount:   0,  // No optimization variables for fallback
		ConstraintCount: 0,  // No optimization budgets for fallback
		KCandidates:     len(docs),
		PairsCount:      len(pairs),
		BudgetTokens:    maxTokens,
		MaxDocs:         maxDocs,
		SolverUsed:      "mmr-fallback",
		FallbackReason:  "z3_not_available",
	}
}

// selectTopCandidates selects top K candidates by utility score
func (s *optimizationSolver) selectTopCandidates(docs []types.ScoredDocument, k int) []types.ScoredDocument {
	if len(docs) <= k {
		return docs
	}
	
	// Sort by utility score
	sorted := make([]types.ScoredDocument, len(docs))
	copy(sorted, docs)
	
	sort.Slice(sorted, func(i, j int) bool {
		return sorted[i].UtilityScore > sorted[j].UtilityScore
	})
	
	return sorted[:k]
}

// computeTierMultipliers computes lexicographic tier multipliers
func (s *optimizationSolver) computeTierMultipliers() []float64 {
	// After integer scaling (×1000), compute upper bounds per tier
	bounds := []float64{1000, 1000, 1000, 1000, 1000, 1000, 1000}
	multipliers := make([]float64, 7)
	
	multipliers[6] = 1.0 // Base tier (uncertainty)
	for t := 5; t >= 0; t-- {
		sum := 0.0
		for u := t + 1; u < 7; u++ {
			sum += bounds[u]
		}
		multipliers[t] = 1.0 + sum
	}
	
	return multipliers
}

// computeObjectiveValue computes the objective function value for selected documents
func (s *optimizationSolver) computeObjectiveValue(docs []types.ScoredDocument, 
	selected []int, 
	pairs []features.DocumentPair) float64 {
	
	if len(selected) == 0 {
		return 0.0
	}
	
	// Sum utility scores of selected documents
	totalUtility := 0.0
	for _, idx := range selected {
		totalUtility += docs[idx].UtilityScore
	}
	
	// Add pairwise bonuses/penalties
	selectedSet := make(map[int]bool)
	for _, idx := range selected {
		selectedSet[idx] = true
	}
	
	pairwiseScore := 0.0
	for _, pair := range pairs {
		if selectedSet[pair.DocI] && selectedSet[pair.DocJ] {
			// Both documents selected
			coherenceBonus := s.config.Weights.CoherenceBonus * pair.Coherence
			redundancyPenalty := s.config.Weights.RedundancyPenalty * pair.Redundancy
			pairwiseScore += coherenceBonus - redundancyPenalty
		}
	}
	
	return totalUtility + pairwiseScore
}
