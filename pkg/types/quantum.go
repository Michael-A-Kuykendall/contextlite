package types

// WorkspaceWeights represents per-workspace weight configuration
type WorkspaceWeights struct {
	WorkspacePath     string            `json:"workspace_path" db:"workspace_path"`
	RelevanceWeight   float64           `json:"relevance_weight" db:"relevance_weight"`
	RecencyWeight     float64           `json:"recency_weight" db:"recency_weight"`
	DiversityWeight   float64           `json:"diversity_weight" db:"diversity_weight"`
	EntanglementWeight float64          `json:"entanglement_weight" db:"entanglement_weight"`
	RedundancyPenalty float64           `json:"redundancy_penalty" db:"redundancy_penalty"`
	NormalizationStats string           `json:"normalization_stats" db:"normalization_stats"`
	UpdateCount       int               `json:"update_count" db:"update_count"`
	LastUpdated       string            `json:"last_updated" db:"last_updated"`
}

// NormalizationStats represents z-score parameters for feature normalization
type NormalizationStats struct {
	Mean   map[string]float64 `json:"mean"`
	StdDev map[string]float64 `json:"std_dev"`
	Count  int                `json:"count"`
}

// optimizationConstraint represents a user-defined optimization budget
type optimizationConstraint struct {
	ID          string  `json:"id"`
	Name        string  `json:"name"`
	Description string  `json:"description"`
	Type        string  `json:"type"` // "hard" or "soft"
	Expression  string  `json:"expression"`
	Weight      float64 `json:"weight,omitempty"`
	Active      bool    `json:"active"`
}

// UserFeedback represents user feedback for weight adaptation
type UserFeedback struct {
	Query         string   `json:"query"`
	AcceptedDocs  []string `json:"accepted_docs"`
	RejectedDocs  []string `json:"rejected_docs"`
	WorkspacePath string   `json:"workspace_path"`
	Timestamp     int64    `json:"timestamp"`
}
