package types

import (
	"testing"
	"time"
)

func TestDocument_Fields(t *testing.T) {
	now := time.Now()
	doc := Document{
		ID:           "test-id",
		Content:      "test content",
		ContentHash:  "hash123",
		Path:         "/test/path",
		Language:     "go",
		ModifiedTime: now.Unix(),
		TokenCount:   100,
		ModelID:      "gpt-4",
		QuantumScore: 0.85,
		Entanglement: "entanglement-data",
		Coherence:    "coherence-data",
		CreatedAt:    now,
		UpdatedAt:    now,
		Metadata:     map[string]string{"key": "value"},
	}

	if doc.ID != "test-id" {
		t.Errorf("Expected ID to be 'test-id', got %s", doc.ID)
	}
	if doc.Content != "test content" {
		t.Errorf("Expected Content to be 'test content', got %s", doc.Content)
	}
	if doc.TokenCount != 100 {
		t.Errorf("Expected TokenCount to be 100, got %d", doc.TokenCount)
	}
	if doc.QuantumScore != 0.85 {
		t.Errorf("Expected QuantumScore to be 0.85, got %f", doc.QuantumScore)
	}
}

func TestDocumentReference_Fields(t *testing.T) {
	ref := DocumentReference{
		ID:              "ref-id",
		Path:            "/ref/path",
		Content:         "reference content",
		Language:        "python",
		UtilityScore:    0.75,
		RelevanceScore:  0.80,
		RecencyScore:    0.65,
		InclusionReason: "high relevance",
	}

	if ref.ID != "ref-id" {
		t.Errorf("Expected ID to be 'ref-id', got %s", ref.ID)
	}
	if ref.UtilityScore != 0.75 {
		t.Errorf("Expected UtilityScore to be 0.75, got %f", ref.UtilityScore)
	}
	if ref.RelevanceScore != 0.80 {
		t.Errorf("Expected RelevanceScore to be 0.80, got %f", ref.RelevanceScore)
	}
}

func TestFeatureVector_Fields(t *testing.T) {
	fv := FeatureVector{
		Relevance:    0.9,
		Recency:      0.8,
		Entanglement: 0.7,
		Prior:        0.6,
		Uncertainty:  0.1,
		Authority:    0.5,
		Specificity:  0.4,
	}

	if fv.Relevance != 0.9 {
		t.Errorf("Expected Relevance to be 0.9, got %f", fv.Relevance)
	}
	if fv.Recency != 0.8 {
		t.Errorf("Expected Recency to be 0.8, got %f", fv.Recency)
	}
	if fv.Entanglement != 0.7 {
		t.Errorf("Expected Entanglement to be 0.7, got %f", fv.Entanglement)
	}
	if fv.Prior != 0.6 {
		t.Errorf("Expected Prior to be 0.6, got %f", fv.Prior)
	}
	if fv.Uncertainty != 0.1 {
		t.Errorf("Expected Uncertainty to be 0.1, got %f", fv.Uncertainty)
	}
	if fv.Authority != 0.5 {
		t.Errorf("Expected Authority to be 0.5, got %f", fv.Authority)
	}
	if fv.Specificity != 0.4 {
		t.Errorf("Expected Specificity to be 0.4, got %f", fv.Specificity)
	}
}

func TestScoredDocument_Fields(t *testing.T) {
	doc := Document{ID: "scored-doc", Content: "content"}
	features := FeatureVector{Relevance: 0.9, Recency: 0.8}
	
	scored := ScoredDocument{
		Document:       doc,
		Features:       features,
		UtilityScore:   0.85,
		PairwiseScores: []float64{0.1, 0.2, 0.3},
	}

	if scored.Document.ID != "scored-doc" {
		t.Errorf("Expected Document ID to be 'scored-doc', got %s", scored.Document.ID)
	}
	if scored.Features.Relevance != 0.9 {
		t.Errorf("Expected Features.Relevance to be 0.9, got %f", scored.Features.Relevance)
	}
	if scored.UtilityScore != 0.85 {
		t.Errorf("Expected UtilityScore to be 0.85, got %f", scored.UtilityScore)
	}
	if len(scored.PairwiseScores) != 3 {
		t.Errorf("Expected PairwiseScores length to be 3, got %d", len(scored.PairwiseScores))
	}
}

func TestConcept_Fields(t *testing.T) {
	concept := Concept{
		DocID: "doc-123",
		Term:  "golang",
		TF:    5,
		DF:    2,
	}

	if concept.DocID != "doc-123" {
		t.Errorf("Expected DocID to be 'doc-123', got %s", concept.DocID)
	}
	if concept.Term != "golang" {
		t.Errorf("Expected Term to be 'golang', got %s", concept.Term)
	}
	if concept.TF != 5 {
		t.Errorf("Expected TF to be 5, got %d", concept.TF)
	}
	if concept.DF != 2 {
		t.Errorf("Expected DF to be 2, got %d", concept.DF)
	}
}