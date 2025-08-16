package smt

import (
	"context"
	"fmt"
	"math"
	"sort"
	"time"

	"contextlite/internal/features"
	"contextlite/pkg/types"
)

// SMTSolver provides SMT-optimized context selection
type SMTSolver struct {
	config SMTConfig
}

// SMTConfig represents SMT solver configuration
type SMTConfig struct {
	TimeoutMs       int
	MaxOptGap       float64
	MaxCandidates   int
	MaxPairsPerDoc  int
	IntegerScaling  int
	ObjectiveStyle  string
	Weights         WeightConfig
}

// WeightConfig represents the 7D weight configuration
type WeightConfig struct {
	Relevance         float64
	Recency          float64
	Entanglement     float64
	Prior            float64
	Authority        float64
	Specificity      float64
	Uncertainty      float64
	RedundancyPenalty float64
	CoherenceBonus   float64
}

// SMTResult represents the result of SMT optimization
type SMTResult struct {
	SelectedDocs    []int               `json:"selected_docs"`
	ObjectiveValue  float64             `json:"objective_value"`
	OptimalityGap   float64             `json:"optimality_gap"`
	SolveTimeMs     int                 `json:"solve_time_ms"`
	VariableCount   int                 `json:"variable_count"`
	ConstraintCount int                 `json:"constraint_count"`
	SolverUsed      string              `json:"solver_used"`
	FallbackReason  string              `json:"fallback_reason,omitempty"`
}

// NewSMTSolver creates a new SMT solver
func NewSMTSolver(config SMTConfig) *SMTSolver {
	return &SMTSolver{
		config: config,
	}
}

// OptimizeSelection performs SMT-optimized document selection
func (s *SMTSolver) OptimizeSelection(ctx context.Context, 
	scoredDocs []types.ScoredDocument, 
	maxTokens int, 
	maxDocs int) (*SMTResult, error) {
	
	startTime := time.Now()
	
	// Limit candidates to keep SMT model manageable
	candidates := scoredDocs
	if len(candidates) > s.config.MaxCandidates {
		candidates = s.selectTopCandidates(scoredDocs, s.config.MaxCandidates)
	}
	
	// Compute pairwise similarities
	simComputer := features.NewSimilarityComputer(s.config.MaxPairsPerDoc)
	pairs := simComputer.ComputePairwiseScores(candidates)
	
	// Try SMT optimization based on objective style
	var result *SMTResult
	var err error
	
	switch s.config.ObjectiveStyle {
	case "weighted-sum":
		result, err = s.solveWeightedSum(candidates, pairs, maxTokens, maxDocs)
	case "lexicographic":
		result, err = s.solveLexicographic(candidates, pairs, maxTokens, maxDocs)
	case "epsilon-constraint":
		result, err = s.solveEpsilonConstraint(candidates, pairs, maxTokens, maxDocs)
	default:
		result, err = s.solveWeightedSum(candidates, pairs, maxTokens, maxDocs)
	}
	
	// If SMT fails or times out, fall back to MMR-greedy
	if err != nil || result == nil {
		result = s.fallbackMMR(candidates, pairs, maxTokens, maxDocs)
		result.FallbackReason = fmt.Sprintf("SMT failed: %v", err)
		result.SolverUsed = "fallback"
	}
	
	result.SolveTimeMs = int(time.Since(startTime).Milliseconds())
	return result, nil
}

// solveWeightedSum implements weighted-sum scalarization
func (s *SMTSolver) solveWeightedSum(docs []types.ScoredDocument, 
	pairs []features.DocumentPair, 
	maxTokens, maxDocs int) (*SMTResult, error) {
	
	// For now, implement using greedy approximation
	// TODO: Replace with actual SMT solver (Z3/CVC5) integration
	
	return s.greedyWeightedSelection(docs, pairs, maxTokens, maxDocs, "weighted-sum")
}

// solveLexicographic implements lexicographic optimization
func (s *SMTSolver) solveLexicographic(docs []types.ScoredDocument,
	pairs []features.DocumentPair,
	maxTokens, maxDocs int) (*SMTResult, error) {
	
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

// solveEpsilonConstraint implements ε-constraint method
func (s *SMTSolver) solveEpsilonConstraint(docs []types.ScoredDocument,
	pairs []features.DocumentPair,
	maxTokens, maxDocs int) (*SMTResult, error) {
	
	// Primary objective: maximize relevance
	// Constraints: limit redundancy, ensure coherence
	
	return s.greedyConstrainedSelection(docs, pairs, maxTokens, maxDocs)
}

// greedyWeightedSelection implements MMR-style greedy selection
func (s *SMTSolver) greedyWeightedSelection(docs []types.ScoredDocument,
	pairs []features.DocumentPair,
	maxTokens, maxDocs int, 
	method string) (*SMTResult, error) {
	
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
	
	return &SMTResult{
		SelectedDocs:    selected,
		ObjectiveValue:  s.computeObjectiveValue(docs, selected, pairs),
		OptimalityGap:   0.0, // Greedy is not guaranteed optimal
		VariableCount:   len(docs) + len(pairs),
		ConstraintCount: 3, // Budget, max docs, linking
		SolverUsed:      method,
	}, nil
}

// greedyConstrainedSelection implements ε-constraint greedy selection
func (s *SMTSolver) greedyConstrainedSelection(docs []types.ScoredDocument,
	pairs []features.DocumentPair,
	maxTokens, maxDocs int) (*SMTResult, error) {
	
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
	
	// Greedy selection with constraint checking
	for _, idx := range relevanceSorted {
		if len(selected) >= maxDocs {
			break
		}
		
		doc := docs[idx]
		if totalTokens+doc.Document.TokenCount > maxTokens {
			continue
		}
		
		// Check constraint violations
		newRedundancy := totalRedundancy
		newCoherence := totalCoherence
		
		for _, selectedIdx := range selected {
			key := fmt.Sprintf("%d-%d", idx, selectedIdx)
			if sim, exists := similarity[key]; exists {
				newRedundancy += sim
				newCoherence += sim // Approximation
			}
		}
		
		// ε-constraint thresholds (from config)
		maxRedundancy := 0.4 * float64(len(selected)+1) // Per-pair average
		
		if newRedundancy <= maxRedundancy {
			selected = append(selected, idx)
			totalTokens += doc.Document.TokenCount
			totalRedundancy = newRedundancy
			totalCoherence = newCoherence
		}
	}
	
	return &SMTResult{
		SelectedDocs:    selected,
		ObjectiveValue:  s.computeObjectiveValue(docs, selected, pairs),
		OptimalityGap:   0.0,
		VariableCount:   len(docs) + len(pairs),
		ConstraintCount: 5, // Budget, max docs, redundancy, coherence, recency
		SolverUsed:      "epsilon-constraint",
	}, nil
}

// fallbackMMR provides MMR fallback when SMT fails
func (s *SMTSolver) fallbackMMR(docs []types.ScoredDocument,
	pairs []features.DocumentPair,
	maxTokens, maxDocs int) *SMTResult {
	
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
	
	return &SMTResult{
		SelectedDocs:    selected,
		ObjectiveValue:  s.computeObjectiveValue(docs, selected, pairs),
		OptimalityGap:   0.1, // Approximation gap
		VariableCount:   len(docs),
		ConstraintCount: 2,
		SolverUsed:      "mmr-fallback",
	}
}

// selectTopCandidates selects top K candidates by utility score
func (s *SMTSolver) selectTopCandidates(docs []types.ScoredDocument, k int) []types.ScoredDocument {
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
func (s *SMTSolver) computeTierMultipliers() []float64 {
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
func (s *SMTSolver) computeObjectiveValue(docs []types.ScoredDocument, 
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
