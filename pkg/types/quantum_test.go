package types

import (
	"testing"
)

func TestWorkspaceWeights_Fields(t *testing.T) {
	weights := WorkspaceWeights{
		WorkspacePath:      "/test/workspace",
		RelevanceWeight:    0.30,
		RecencyWeight:      0.20,
		DiversityWeight:    0.15,
		EntanglementWeight: 0.15,
		RedundancyPenalty:  0.10,
		NormalizationStats: `{"mean":{"relevance":0.5},"std_dev":{"relevance":0.1},"count":100}`,
		UpdateCount:        5,
		LastUpdated:        "2025-08-21T10:00:00Z",
	}

	if weights.WorkspacePath != "/test/workspace" {
		t.Errorf("Expected WorkspacePath to be '/test/workspace', got %s", weights.WorkspacePath)
	}
	if weights.RelevanceWeight != 0.30 {
		t.Errorf("Expected RelevanceWeight to be 0.30, got %f", weights.RelevanceWeight)
	}
	if weights.RecencyWeight != 0.20 {
		t.Errorf("Expected RecencyWeight to be 0.20, got %f", weights.RecencyWeight)
	}
	if weights.DiversityWeight != 0.15 {
		t.Errorf("Expected DiversityWeight to be 0.15, got %f", weights.DiversityWeight)
	}
	if weights.EntanglementWeight != 0.15 {
		t.Errorf("Expected EntanglementWeight to be 0.15, got %f", weights.EntanglementWeight)
	}
	if weights.RedundancyPenalty != 0.10 {
		t.Errorf("Expected RedundancyPenalty to be 0.10, got %f", weights.RedundancyPenalty)
	}
	if weights.UpdateCount != 5 {
		t.Errorf("Expected UpdateCount to be 5, got %d", weights.UpdateCount)
	}
	if weights.LastUpdated != "2025-08-21T10:00:00Z" {
		t.Errorf("Expected LastUpdated to be '2025-08-21T10:00:00Z', got %s", weights.LastUpdated)
	}
}

func TestNormalizationStats_Fields(t *testing.T) {
	stats := NormalizationStats{
		Mean: map[string]float64{
			"relevance": 0.5,
			"recency":   0.4,
		},
		StdDev: map[string]float64{
			"relevance": 0.1,
			"recency":   0.15,
		},
		Count: 100,
	}

	if stats.Mean["relevance"] != 0.5 {
		t.Errorf("Expected Mean['relevance'] to be 0.5, got %f", stats.Mean["relevance"])
	}
	if stats.Mean["recency"] != 0.4 {
		t.Errorf("Expected Mean['recency'] to be 0.4, got %f", stats.Mean["recency"])
	}
	if stats.StdDev["relevance"] != 0.1 {
		t.Errorf("Expected StdDev['relevance'] to be 0.1, got %f", stats.StdDev["relevance"])
	}
	if stats.StdDev["recency"] != 0.15 {
		t.Errorf("Expected StdDev['recency'] to be 0.15, got %f", stats.StdDev["recency"])
	}
	if stats.Count != 100 {
		t.Errorf("Expected Count to be 100, got %d", stats.Count)
	}
}

func TestSMTConstraint_Fields(t *testing.T) {
	constraint := SMTConstraint{
		ID:          "constraint-1",
		Name:        "Max Documents",
		Description: "Limit the number of selected documents",
		Type:        "hard",
		Expression:  "sum(selected) <= 10",
		Weight:      1.0,
		Active:      true,
	}

	if constraint.ID != "constraint-1" {
		t.Errorf("Expected ID to be 'constraint-1', got %s", constraint.ID)
	}
	if constraint.Name != "Max Documents" {
		t.Errorf("Expected Name to be 'Max Documents', got %s", constraint.Name)
	}
	if constraint.Description != "Limit the number of selected documents" {
		t.Errorf("Expected Description to be 'Limit the number of selected documents', got %s", constraint.Description)
	}
	if constraint.Type != "hard" {
		t.Errorf("Expected Type to be 'hard', got %s", constraint.Type)
	}
	if constraint.Expression != "sum(selected) <= 10" {
		t.Errorf("Expected Expression to be 'sum(selected) <= 10', got %s", constraint.Expression)
	}
	if constraint.Weight != 1.0 {
		t.Errorf("Expected Weight to be 1.0, got %f", constraint.Weight)
	}
	if constraint.Active != true {
		t.Errorf("Expected Active to be true, got %t", constraint.Active)
	}
}

func TestUserFeedback_Fields(t *testing.T) {
	feedback := UserFeedback{
		Query:         "test query",
		AcceptedDocs:  []string{"doc1", "doc2"},
		RejectedDocs:  []string{"doc3", "doc4"},
		WorkspacePath: "/workspace/test",
		Timestamp:     1640995200, // 2022-01-01 00:00:00 UTC
	}

	if feedback.Query != "test query" {
		t.Errorf("Expected Query to be 'test query', got %s", feedback.Query)
	}
	if len(feedback.AcceptedDocs) != 2 {
		t.Errorf("Expected AcceptedDocs length to be 2, got %d", len(feedback.AcceptedDocs))
	}
	if feedback.AcceptedDocs[0] != "doc1" {
		t.Errorf("Expected AcceptedDocs[0] to be 'doc1', got %s", feedback.AcceptedDocs[0])
	}
	if len(feedback.RejectedDocs) != 2 {
		t.Errorf("Expected RejectedDocs length to be 2, got %d", len(feedback.RejectedDocs))
	}
	if feedback.RejectedDocs[0] != "doc3" {
		t.Errorf("Expected RejectedDocs[0] to be 'doc3', got %s", feedback.RejectedDocs[0])
	}
	if feedback.WorkspacePath != "/workspace/test" {
		t.Errorf("Expected WorkspacePath to be '/workspace/test', got %s", feedback.WorkspacePath)
	}
	if feedback.Timestamp != 1640995200 {
		t.Errorf("Expected Timestamp to be 1640995200, got %d", feedback.Timestamp)
	}
}