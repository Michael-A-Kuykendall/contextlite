package optimization

import (
	"testing"
	"contextlite/internal/features"
	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

func TestoptimizationSolver_DirectAlgorithmCalls(t *testing.T) {
	// Test algorithm methods directly to ensure coverage
	cfg := &config.Config{
		optimization: config.optimizationConfig{
			SolverTimeoutMs: 5000,
			ObjectiveStyle:  "weighted-sum",
		},
		Weights: config.WeightsConfig{
			Relevance:     0.6,
			Recency:       0.3,
			Entanglement:  0.1,
		},
		Lexicographic: config.LexConfig{
			ComputeAtRuntime: true,
		},
		EpsilonConstraint: config.EpsilonConfig{
			MaxRedundancy: 0.3,
			MinCoherence:  0.6,
			MinRecency:    0.5,
		},
	}

	// Create solver without optimizer for pure algorithm testing
	solver := &optimizationSolver{
		config:       cfg,
		z3Optimizer:  nil, // No optimizer
		verifier:     nil,
	}

	docs := []types.ScoredDocument{
		{
			Document: types.Document{ID: "direct1", TokenCount: 5},
			Features: types.FeatureVector{
				Relevance:    0.9,
				Recency:      0.8,
				Entanglement: 0.7,
			},
		},
		{
			Document: types.Document{ID: "direct2", TokenCount: 4},
			Features: types.FeatureVector{
				Relevance:    0.8,
				Recency:      0.7,
				Entanglement: 0.6,
			},
		},
		{
			Document: types.Document{ID: "direct3", TokenCount: 3},
			Features: types.FeatureVector{
				Relevance:    0.7,
				Recency:      0.6,
				Entanglement: 0.5,
			},
		},
	}

	// Create dummy pairs
	pairs := []features.DocumentPair{
		{DocI: 0, DocJ: 1, Similarity: 0.8, Redundancy: 0.2, Coherence: 0.9},
		{DocI: 0, DocJ: 2, Similarity: 0.6, Redundancy: 0.3, Coherence: 0.7},
		{DocI: 1, DocJ: 2, Similarity: 0.7, Redundancy: 0.25, Coherence: 0.8},
	}

	// Test solveWeightedSum
	t.Run("solveWeightedSum", func(t *testing.T) {
		result, err := solver.solveWeightedSum(docs, pairs, 10, 2)
		if err != nil {
			t.Fatalf("solveWeightedSum failed: %v", err)
		}
		if len(result.SelectedDocs) == 0 {
			t.Error("Expected documents to be selected")
		}
		t.Logf("WeightedSum selected %d docs", len(result.SelectedDocs))
	})

	// Test solveLexicographic
	t.Run("solveLexicographic", func(t *testing.T) {
		result, err := solver.solveLexicographic(docs, pairs, 10, 2)
		if err != nil {
			t.Fatalf("solveLexicographic failed: %v", err)
		}
		if len(result.SelectedDocs) == 0 {
			t.Error("Expected documents to be selected")
		}
		t.Logf("Lexicographic selected %d docs", len(result.SelectedDocs))
	})

	// Test solveEpsilonConstraint
	t.Run("solveEpsilonConstraint", func(t *testing.T) {
		result, err := solver.solveEpsilonConstraint(docs, pairs, 10, 2)
		if err != nil {
			t.Fatalf("solveEpsilonConstraint failed: %v", err)
		}
		if len(result.SelectedDocs) == 0 {
			t.Error("Expected documents to be selected")
		}
		t.Logf("EpsilonConstraint selected %d docs", len(result.SelectedDocs))
	})

	// Test greedyWeightedSelection
	t.Run("greedyWeightedSelection", func(t *testing.T) {
		result, err := solver.greedyWeightedSelection(docs, pairs, 10, 2, "test-greedy")
		if err != nil {
			t.Fatalf("greedyWeightedSelection failed: %v", err)
		}
		if len(result.SelectedDocs) == 0 {
			t.Error("Expected documents to be selected")
		}
		t.Logf("GreedyWeighted selected %d docs", len(result.SelectedDocs))
	})

	// Test greedyConstrainedSelection
	t.Run("greedyConstrainedSelection", func(t *testing.T) {
		result, err := solver.greedyConstrainedSelection(docs, pairs, 10, 2)
		if err != nil {
			t.Fatalf("greedyConstrainedSelection failed: %v", err)
		}
		if len(result.SelectedDocs) == 0 {
			t.Error("Expected documents to be selected")
		}
		t.Logf("GreedyConstrained selected %d docs", len(result.SelectedDocs))
	})

	// Test computeTierMultipliers
	t.Run("computeTierMultipliers", func(t *testing.T) {
		multipliers := solver.computeTierMultipliers()
		if len(multipliers) == 0 {
			t.Error("Expected multipliers to be returned")
		}
		for i, mult := range multipliers {
			t.Logf("Tier %d multiplier: %f", i, mult)
		}
	})
}
