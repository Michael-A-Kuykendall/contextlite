package types

import (
	"time"
)

// Document represents a document in the knowledge base
type Document struct {
	ID             string            `json:"id" db:"id"`
	Content        string            `json:"content" db:"content"`
	ContentHash    string            `json:"content_hash" db:"content_hash"`
	Path           string            `json:"path" db:"path"`
	Language       string            `json:"language" db:"lang"`
	ModifiedTime   int64             `json:"modified_time" db:"mtime"`
	TokenCount     int               `json:"token_count" db:"token_count"`
	ModelID        string            `json:"model_id" db:"model_id"`
	QuantumScore   float64           `json:"quantum_score" db:"quantum_score"`
	Entanglement   string            `json:"entanglement_map" db:"entanglement_map"`
	Coherence      string            `json:"coherence_history" db:"coherence_history"`
	CreatedAt      time.Time         `json:"created_at" db:"created_at"`
	UpdatedAt      time.Time         `json:"updated_at" db:"updated_at"`
	Metadata       map[string]string `json:"metadata,omitempty"`
	
	// Clustering and Project Affinity Fields
	ProjectTags    []string         `json:"project_tags,omitempty"`
	WorkspaceID    string           `json:"workspace_id,omitempty" db:"workspace_id"`
	ResourceTier   string           `json:"resource_tier,omitempty" db:"resource_tier"` // "low", "medium", "high"
	Affinity       *ProjectAffinity `json:"affinity,omitempty"`
}

// DocumentReference represents a document in query results
type DocumentReference struct {
	ID              string  `json:"id"`
	Path            string  `json:"path"`
	Content         string  `json:"content"`
	Language        string  `json:"language"`
	UtilityScore    float64 `json:"utility_score"`
	RelevanceScore  float64 `json:"relevance_score"`
	RecencyScore    float64 `json:"recency_score"`
	// DiversityScore removed - diversity handled via pairwise terms in SMT objective
	InclusionReason string  `json:"inclusion_reason"`
}

// FeatureVector represents the 7D feature vector for a document
// CRITICAL: All features must be SET-INDEPENDENT for optimization correctness
type FeatureVector struct {
	Relevance    float64 `json:"relevance"`    // Query match (BM25, semantic similarity)
	Recency      float64 `json:"recency"`      // Time decay (exponential with 7-day half-life)
	Entanglement float64 `json:"entanglement"` // Cross-doc concept density (PMI over n-grams)
	Prior        float64 `json:"prior"`        // Historical selection likelihood (path frequency)
	Uncertainty  float64 `json:"uncertainty"`  // Score variance across estimators
	Authority    float64 `json:"authority"`    // Document importance (file size, commit frequency)
	Specificity  float64 `json:"specificity"`  // Query-doc topic alignment
}

// ScoredDocument represents a document with its computed scores
type ScoredDocument struct {
	Document       Document      `json:"document"`
	Features       FeatureVector `json:"features"`
	UtilityScore   float64       `json:"utility_score"`
	PairwiseScores []float64     `json:"pairwise_scores,omitempty"` // Similarity to other docs
}

// Concept represents a term in the document concept space
type Concept struct {
	DocID string `json:"doc_id" db:"doc_id"`
	Term  string `json:"term" db:"term"`
	TF    int    `json:"tf" db:"tf"`
	DF    int    `json:"df" db:"df"`
}

// ProjectAffinity defines cluster routing preferences for documents
type ProjectAffinity struct {
	PreferredNode  string   `json:"preferred_node,omitempty"`   // Node ID to prefer for this document
	RequiredNodes  []string `json:"required_nodes,omitempty"`   // Nodes that MUST handle this document
	AvoidNodes     []string `json:"avoid_nodes,omitempty"`      // Nodes to avoid for this document
	Locality       string   `json:"locality,omitempty"`         // "same-rack", "same-zone", "any"
	StickySession  bool     `json:"sticky_session,omitempty"`   // Pin queries to same node
}

// WorkspaceInfo provides workspace-level clustering metadata
type WorkspaceInfo struct {
	ID              string                 `json:"id"`
	Name            string                 `json:"name"`
	DocumentCount   int                    `json:"document_count"`
	ResourceUsage   ResourceUsage          `json:"resource_usage"`
	AffinityRules   map[string]interface{} `json:"affinity_rules"`
	LastAccessTime  time.Time              `json:"last_access_time"`
	AccessPattern   string                 `json:"access_pattern"` // "high-frequency", "normal", "archive"
}

// ResourceUsage tracks resource consumption per workspace
type ResourceUsage struct {
	MemoryMB        int64     `json:"memory_mb"`
	QueryCount      int64     `json:"query_count"`
	DocumentCount   int       `json:"document_count"`
	AvgResponseTime float64   `json:"avg_response_time_ms"`
	LastUpdated     time.Time `json:"last_updated"`
}

// ClusterNodeInfo represents a ContextLite node in the cluster
type ClusterNodeInfo struct {
	ID               string                    `json:"id"`
	Address          string                    `json:"address"`
	Port             int                       `json:"port"`
	Status           NodeStatus                `json:"status"`
	Workspaces       []WorkspaceInfo           `json:"workspaces"`
	ResourceLimits   ResourceLimits            `json:"resource_limits"`
	LoadFactor       float64                   `json:"load_factor"`       // 0.0 - 1.0
	LastHeartbeat    time.Time                 `json:"last_heartbeat"`
	Version          string                    `json:"version"`
	Features         []string                  `json:"features"`          // Supported features
}

// NodeStatus represents the health state of a cluster node
type NodeStatus string

const (
	NodeStatusHealthy     NodeStatus = "healthy"
	NodeStatusDegraded    NodeStatus = "degraded"
	NodeStatusUnhealthy   NodeStatus = "unhealthy"
	NodeStatusMaintenance NodeStatus = "maintenance"
	NodeStatusOffline     NodeStatus = "offline"
)

// ResourceLimits defines resource constraints for a workspace or node
type ResourceLimits struct {
	MaxConcurrentRequests int   `json:"max_concurrent_requests"`
	MaxTokensPerMinute   int   `json:"max_tokens_per_minute"`
	MaxDocumentsPerQuery int   `json:"max_documents_per_query"`
	MaxMemoryMB         int64 `json:"max_memory_mb"`
	MaxStorageMB        int64 `json:"max_storage_mb"`
}
