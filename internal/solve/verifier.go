package solve

import (
	"fmt"
	"math"

	"contextlite/pkg/types"
)

// BruteForceVerifier provides exhaustive search for small problems to verify Z3 optimality
type BruteForceVerifier struct {
	integerScale int
}

// NewBruteForceVerifier creates a new brute force verifier
func NewBruteForceVerifier() *BruteForceVerifier {
	return &BruteForceVerifier{
		integerScale: 10000,
	}
}

// BruteForceResult represents the result of brute force optimization
type BruteForceResult struct {
	SelectedDocs   []int
	ObjectiveValue int
	Feasible       bool
	SolutionsChecked int
}

// BruteForceOptimize is an alias for OptimizeExhaustive for testing compatibility
func (bf *BruteForceVerifier) BruteForceOptimize(
	docs []types.ScoredDocument,
	pairs []DocumentPair,
	maxTokens int,
	maxDocs int) (*BruteForceResult, error) {
	return bf.OptimizeExhaustive(docs, pairs, maxTokens, maxDocs)
}

// OptimizeExhaustive performs exhaustive search for problems with N ≤ 12 documents
func (bf *BruteForceVerifier) OptimizeExhaustive(
	docs []types.ScoredDocument,
	pairs []DocumentPair,
	maxTokens int,
	maxDocs int) (*BruteForceResult, error) {

	n := len(docs)
	if n > 12 {
		return nil, fmt.Errorf("brute force limited to N ≤ 12 documents, got %d", n)
	}

	bestResult := &BruteForceResult{
		ObjectiveValue: math.MinInt32,
		Feasible:       false,
	}

	// Create pairwise lookup for efficiency
	pairMap := make(map[string]DocumentPair)
	for _, pair := range pairs {
		key := fmt.Sprintf("%d-%d", pair.DocI, pair.DocJ)
		pairMap[key] = pair
		// Add reverse direction
		reverseKey := fmt.Sprintf("%d-%d", pair.DocJ, pair.DocI)
		pairMap[reverseKey] = pair
	}

	// Enumerate all 2^n subsets
	maxSubsets := 1 << n
	for subset := 0; subset < maxSubsets; subset++ {
		bestResult.SolutionsChecked++

		// Extract selected documents from subset
		var selected []int
		totalTokens := 0
		
		for i := 0; i < n; i++ {
			if (subset >> i) & 1 == 1 {
				selected = append(selected, i)
				totalTokens += docs[i].Document.TokenCount
			}
		}

		// Check feasibility constraints
		if !bf.isFeasible(selected, totalTokens, maxTokens, maxDocs) {
			continue
		}

		// Compute objective value
		objValue := bf.computeObjective(docs, selected, pairMap)
		
		// Update best solution
		if objValue > bestResult.ObjectiveValue {
			bestResult.SelectedDocs = make([]int, len(selected))
			copy(bestResult.SelectedDocs, selected)
			bestResult.ObjectiveValue = objValue
			bestResult.Feasible = true
		}
	}

	return bestResult, nil
}

// isFeasible checks if a solution satisfies all constraints
func (bf *BruteForceVerifier) isFeasible(selected []int, totalTokens, maxTokens, maxDocs int) bool {
	// Check token budget
	if maxTokens > 0 && totalTokens > maxTokens {
		return false
	}
	
	// Check document count
	if maxDocs > 0 && len(selected) > maxDocs {
		return false
	}
	
	return true
}

// computeObjective calculates the objective value for a given selection
func (bf *BruteForceVerifier) computeObjective(
	docs []types.ScoredDocument,
	selected []int,
	pairMap map[string]DocumentPair) int {

	objective := 0

	// Per-document utility terms: Σ v_i * x_i
	for _, i := range selected {
		scaledUtility := int(docs[i].UtilityScore * float64(bf.integerScale))
		objective += scaledUtility
	}

	// Pairwise terms: Σ (c_ij - r_ij) * y_ij
	selectedSet := make(map[int]bool)
	for _, i := range selected {
		selectedSet[i] = true
	}

	// Check all pairs of selected documents
	for i := 0; i < len(selected); i++ {
		for j := i + 1; j < len(selected); j++ {
			docI, docJ := selected[i], selected[j]
			
			// Look up pair information
			key := fmt.Sprintf("%d-%d", docI, docJ)
			if pair, exists := pairMap[key]; exists {
				// Both documents are selected, so y_ij = 1
				netEffect := int((pair.CoherenceBonus - pair.RedundancyPenalty) * float64(bf.integerScale))
				objective += netEffect
			}
		}
	}

	return objective
}

// VerifyOptimality compares Z3 solution against brute force optimum
func (bf *BruteForceVerifier) VerifyOptimality(
	docs []types.ScoredDocument,
	pairs []DocumentPair,
	maxTokens int,
	maxDocs int,
	z3Result *OptimizeResult) (*VerificationResult, error) {

	// Get brute force optimum
	bruteResult, err := bf.OptimizeExhaustive(docs, pairs, maxTokens, maxDocs)
	if err != nil {
		return nil, err
	}

	verification := &VerificationResult{
		BruteForceOptimum: bruteResult.ObjectiveValue,
		Z3ObjectiveValue:  z3Result.ObjectiveValue,
		SolutionsChecked:  bruteResult.SolutionsChecked,
		IsOptimal:         false,
		Gap:               0.0,
	}

	if bruteResult.Feasible && z3Result.Status == "sat" {
		verification.IsOptimal = (z3Result.ObjectiveValue >= bruteResult.ObjectiveValue)
		if bruteResult.ObjectiveValue > 0 {
			verification.Gap = float64(bruteResult.ObjectiveValue - z3Result.ObjectiveValue) / float64(bruteResult.ObjectiveValue)
		}
	}

	return verification, nil
}

// VerificationResult contains the results of optimality verification
type VerificationResult struct {
	BruteForceOptimum int
	Z3ObjectiveValue  int
	SolutionsChecked  int
	IsOptimal         bool
	Gap               float64
}
