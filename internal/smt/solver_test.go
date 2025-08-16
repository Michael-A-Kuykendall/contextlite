package smt

import (
	"context"
	"testing"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

func TestSMTSolver_Creation(t *testing.T) {
	// Test SMT solver creation with no Z3 path (should work)
	cfg := &config.Config{
		SMT: config.SMTConfig{
			SolverTimeoutMs: 5000,
			MaxCandidates:   100,
			MaxPairsPerDoc:  10,
			IntegerScaling:  10000,
			ObjectiveStyle:  "weighted-sum",
			Z3: config.Z3Config{
				BinaryPath:          "", // No Z3 binary
				EnableVerification:  false,
				MaxVerificationDocs: 12,
			},
		},
		Weights: config.WeightsConfig{
			Relevance:         0.3,
			Recency:          0.2,
			Entanglement:     0.15,
			Prior:            0.1,
			Authority:        0.1,
			Specificity:      0.05,
			Uncertainty:      0.05,
			RedundancyPenalty: 0.3,
			CoherenceBonus:   0.2,
		},
	}

	solver, err := NewSMTSolver(cfg)
	if err != nil {
		t.Fatalf("Failed to create SMT solver: %v", err)
	}

	if solver == nil {
		t.Fatal("SMT solver is nil")
	}
}

func TestSMTSolver_OptimizeSelection_Fallback(t *testing.T) {
	// Test that SMT solver falls back to greedy when Z3 is not available
	cfg := &config.Config{
		SMT: config.SMTConfig{
			SolverTimeoutMs: 5000,
			MaxCandidates:   100,
			MaxPairsPerDoc:  10,
			IntegerScaling:  10000,
			ObjectiveStyle:  "weighted-sum",
			Z3: config.Z3Config{
				BinaryPath:          "", // No Z3 binary
				EnableVerification:  false,
				MaxVerificationDocs: 12,
			},
		},
		Weights: config.WeightsConfig{
			Relevance:         0.3,
			Recency:          0.2,
			Entanglement:     0.15,
			Prior:            0.1,
			Authority:        0.1,
			Specificity:      0.05,
			Uncertainty:      0.05,
			RedundancyPenalty: 0.3,
			CoherenceBonus:   0.2,
		},
	}

	solver, err := NewSMTSolver(cfg)
	if err != nil {
		t.Fatalf("Failed to create SMT solver: %v", err)
	}

	// Create test documents
	docs := []types.ScoredDocument{
		{
			Document: types.Document{
				ID:         "doc1",
				Content:    "This is a test document about machine learning.",
				TokenCount: 10,
			},
			Features: types.FeatureVector{
				Relevance:    0.9,
				Recency:     0.8,
				Entanglement: 0.7,
				Prior:       0.6,
				Authority:   0.5,
				Specificity: 0.4,
				Uncertainty: 0.3,
			},
			UtilityScore: 0.75,
		},
		{
			Document: types.Document{
				ID:         "doc2",
				Content:    "Another document about artificial intelligence.",
				TokenCount: 8,
			},
			Features: types.FeatureVector{
				Relevance:    0.8,
				Recency:     0.7,
				Entanglement: 0.6,
				Prior:       0.5,
				Authority:   0.4,
				Specificity: 0.3,
				Uncertainty: 0.2,
			},
			UtilityScore: 0.65,
		},
	}

	ctx := context.Background()
	result, err := solver.OptimizeSelection(ctx, docs, 100, 2)
	if err != nil {
		t.Fatalf("Failed to optimize selection: %v", err)
	}

	if result == nil {
		t.Fatal("Result is nil")
	}

	if len(result.SelectedDocs) == 0 {
		t.Error("No documents selected")
	}

	// Should fall back to MMR since Z3 is not available
	if result.SolverUsed != "mmr-fallback" {
		t.Errorf("Expected solver to be 'mmr-fallback', got '%s'", result.SolverUsed)
	}

	t.Logf("Selected %d documents using %s solver", len(result.SelectedDocs), result.SolverUsed)
	t.Logf("Objective value: %.4f", result.ObjectiveValue)
	t.Logf("Solve time: %d ms", result.SolveTimeMs)
}
