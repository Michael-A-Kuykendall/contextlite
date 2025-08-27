package middleware

import (
	"context"
	"fmt"
	"net/http"
	"strings"
	"time"

	"go.uber.org/zap"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// WorkspaceMiddleware provides workspace isolation and resource management
type WorkspaceMiddleware struct {
	config           *config.Config
	logger           *zap.Logger
	activeRequests   map[string]int                    // workspace_id -> active_count
	workspaceUsage   map[string]*types.ResourceUsage   // workspace_id -> usage stats
	lastCleanup      time.Time
}

// NewWorkspaceMiddleware creates a new workspace isolation middleware
func NewWorkspaceMiddleware(config *config.Config, logger *zap.Logger) *WorkspaceMiddleware {
	return &WorkspaceMiddleware{
		config:         config,
		logger:         logger,
		activeRequests: make(map[string]int),
		workspaceUsage: make(map[string]*types.ResourceUsage),
		lastCleanup:    time.Now(),
	}
}

// WorkspaceIsolation provides workspace-based request isolation and resource limiting
func (m *WorkspaceMiddleware) WorkspaceIsolation(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		ctx := r.Context()
		
		// Extract workspace ID from request
		workspaceID := m.extractWorkspaceID(r)
		if workspaceID == "" {
			workspaceID = "default"
		}
		
		// Check resource limits
		if !m.checkResourceLimits(workspaceID) {
			m.logger.Warn("Request rejected due to resource limits", 
				zap.String("workspace_id", workspaceID))
			http.Error(w, "Workspace resource limits exceeded", http.StatusTooManyRequests)
			return
		}
		
		// Track active request
		m.activeRequests[workspaceID]++
		defer func() {
			m.activeRequests[workspaceID]--
			if m.activeRequests[workspaceID] <= 0 {
				delete(m.activeRequests, workspaceID)
			}
		}()
		
		// Add workspace context
		ctx = m.addWorkspaceContext(ctx, workspaceID)
		
		// Update usage tracking
		startTime := time.Now()
		defer func() {
			processingTime := time.Since(startTime)
			m.updateUsageStats(workspaceID, processingTime)
		}()
		
		// Periodic cleanup
		m.periodicCleanup()
		
		// Continue to next handler
		next.ServeHTTP(w, r.WithContext(ctx))
	})
}

// extractWorkspaceID extracts workspace identifier from request
func (m *WorkspaceMiddleware) extractWorkspaceID(r *http.Request) string {
	// Try multiple sources for workspace ID
	
	// 1. Header-based workspace ID
	if workspaceID := r.Header.Get("X-Workspace-ID"); workspaceID != "" {
		return workspaceID
	}
	
	// 2. Query parameter
	if workspaceID := r.URL.Query().Get("workspace"); workspaceID != "" {
		return workspaceID
	}
	
	// 3. Extract from workspace path in request body (for context assembly)
	if r.Method == http.MethodPost {
		// This would require reading the body, but we can't consume it here
		// In a full implementation, you'd parse the JSON body carefully
	}
	
	// 4. Derive from request path patterns
	path := r.URL.Path
	if strings.Contains(path, "/workspace/") {
		parts := strings.Split(path, "/workspace/")
		if len(parts) > 1 {
			workspaceID := strings.Split(parts[1], "/")[0]
			return workspaceID
		}
	}
	
	// 5. Use User-Agent or other headers to infer workspace
	userAgent := r.Header.Get("User-Agent")
	if strings.Contains(userAgent, "mission-architect") {
		return "mission-architect"
	} else if strings.Contains(userAgent, "code-assistant") {
		return "code-assistant"
	}
	
	// Default workspace
	return "default"
}

// checkResourceLimits verifies workspace is within resource constraints
func (m *WorkspaceMiddleware) checkResourceLimits(workspaceID string) bool {
	if !m.config.Cluster.Enabled {
		return true // No limits in standalone mode
	}
	
	limits, exists := m.config.Cluster.ResourceLimits[workspaceID]
	if !exists {
		// Use default limits for unknown workspaces
		limits = config.WorkspaceResourceLimits{
			MaxConcurrentRequests: 5,
			MaxTokensPerMinute:   10000,
			MaxDocumentsPerQuery: 10,
			MaxMemoryMB:         256,
			MaxStorageMB:        1024,
			Priority:            3,
		}
	}
	
	// Check concurrent request limit
	activeCount := m.activeRequests[workspaceID]
	if activeCount >= limits.MaxConcurrentRequests {
		m.logger.Warn("Concurrent request limit exceeded",
			zap.String("workspace_id", workspaceID),
			zap.Int("active_requests", activeCount),
			zap.Int("limit", limits.MaxConcurrentRequests))
		return false
	}
	
	// Check rate limiting (tokens per minute)
	usage := m.getOrCreateUsageStats(workspaceID)
	now := time.Now()
	
	// Reset minute counter if needed
	if now.Sub(usage.LastUpdated) > time.Minute {
		usage.QueryCount = 0
		usage.LastUpdated = now
	}
	
	// Check if we're within rate limits
	// Note: This is simplified - real rate limiting would track token counts
	if int(usage.QueryCount) >= limits.MaxTokensPerMinute/1000 { // Rough approximation
		m.logger.Warn("Rate limit exceeded",
			zap.String("workspace_id", workspaceID),
			zap.Int64("queries_this_minute", usage.QueryCount),
			zap.Int("limit", limits.MaxTokensPerMinute))
		return false
	}
	
	return true
}

// addWorkspaceContext adds workspace information to request context
func (m *WorkspaceMiddleware) addWorkspaceContext(ctx context.Context, workspaceID string) context.Context {
	workspaceInfo := &types.WorkspaceInfo{
		ID:              workspaceID,
		Name:            m.getWorkspaceName(workspaceID),
		LastAccessTime:  time.Now(),
		AccessPattern:   m.determineAccessPattern(workspaceID),
		ResourceUsage:   *m.getOrCreateUsageStats(workspaceID),
		AffinityRules:   m.getAffinityRules(workspaceID),
	}
	
	return context.WithValue(ctx, "workspace_info", workspaceInfo)
}

// updateUsageStats updates resource usage statistics for workspace
func (m *WorkspaceMiddleware) updateUsageStats(workspaceID string, processingTime time.Duration) {
	usage := m.getOrCreateUsageStats(workspaceID)
	
	// Update query count
	usage.QueryCount++
	
	// Update average response time (exponential moving average)
	alpha := 0.1 // Smoothing factor
	newResponseTime := float64(processingTime.Milliseconds())
	usage.AvgResponseTime = alpha*newResponseTime + (1-alpha)*usage.AvgResponseTime
	
	// Update timestamp
	usage.LastUpdated = time.Now()
	
	m.workspaceUsage[workspaceID] = usage
}

// getOrCreateUsageStats gets or creates usage stats for workspace
func (m *WorkspaceMiddleware) getOrCreateUsageStats(workspaceID string) *types.ResourceUsage {
	if usage, exists := m.workspaceUsage[workspaceID]; exists {
		return usage
	}
	
	usage := &types.ResourceUsage{
		MemoryMB:        0,
		QueryCount:      0,
		DocumentCount:   0,
		AvgResponseTime: 50.0, // Default 50ms
		LastUpdated:     time.Now(),
	}
	
	m.workspaceUsage[workspaceID] = usage
	return usage
}

// getWorkspaceName returns human-readable name for workspace
func (m *WorkspaceMiddleware) getWorkspaceName(workspaceID string) string {
	nameMap := map[string]string{
		"mission-architect": "Mission Architect AI System",
		"code-assistant":    "Code Assistant Workspace",
		"development":       "Development Environment",
		"general":           "General Purpose Workspace",
		"archive":           "Archive Storage",
		"default":           "Default Workspace",
	}
	
	if name, exists := nameMap[workspaceID]; exists {
		return name
	}
	
	return fmt.Sprintf("Workspace %s", workspaceID)
}

// determineAccessPattern analyzes access pattern for workspace
func (m *WorkspaceMiddleware) determineAccessPattern(workspaceID string) string {
	usage := m.getOrCreateUsageStats(workspaceID)
	
	// Simple heuristic based on query frequency and recency
	now := time.Now()
	timeSinceLastAccess := now.Sub(usage.LastUpdated)
	
	if timeSinceLastAccess < 5*time.Minute && usage.QueryCount > 10 {
		return "high-frequency"
	} else if timeSinceLastAccess < time.Hour && usage.QueryCount > 5 {
		return "normal"
	} else {
		return "archive"
	}
}

// getAffinityRules returns affinity rules for workspace
func (m *WorkspaceMiddleware) getAffinityRules(workspaceID string) map[string]interface{} {
	if !m.config.Cluster.Enabled || !m.config.Cluster.Affinity.WorkspaceRouting {
		return map[string]interface{}{
			"routing_enabled": false,
		}
	}
	
	rules := make(map[string]interface{})
	rules["routing_enabled"] = true
	rules["sticky_sessions"] = m.config.Cluster.Affinity.StickySessions
	
	// Get workspace-specific affinity rules
	if affinityRule, exists := m.config.Cluster.Affinity.Rules[workspaceID]; exists {
		rules["preferred_nodes"] = affinityRule.PreferredNodes
		rules["avoid_nodes"] = affinityRule.AvoidNodes
		rules["resource_tier"] = affinityRule.ResourceTier
		rules["locality"] = affinityRule.Locality
	} else {
		rules["resource_tier"] = m.config.Cluster.Affinity.DefaultTier
		rules["locality"] = "any"
	}
	
	return rules
}

// periodicCleanup performs periodic cleanup of old usage data
func (m *WorkspaceMiddleware) periodicCleanup() {
	now := time.Now()
	
	// Only cleanup every 5 minutes
	if now.Sub(m.lastCleanup) < 5*time.Minute {
		return
	}
	
	m.lastCleanup = now
	
	// Remove usage stats for workspaces not accessed in last hour
	for workspaceID, usage := range m.workspaceUsage {
		if now.Sub(usage.LastUpdated) > time.Hour {
			delete(m.workspaceUsage, workspaceID)
			m.logger.Debug("Cleaned up stale workspace usage data",
				zap.String("workspace_id", workspaceID))
		}
	}
	
	// Remove empty active request counters
	for workspaceID, count := range m.activeRequests {
		if count <= 0 {
			delete(m.activeRequests, workspaceID)
		}
	}
}

// GetWorkspaceStats returns current workspace statistics (for health endpoint)
func (m *WorkspaceMiddleware) GetWorkspaceStats() map[string]interface{} {
	stats := make(map[string]interface{})
	
	// Overall stats
	stats["total_workspaces"] = len(m.workspaceUsage)
	stats["active_workspaces"] = len(m.activeRequests)
	
	// Per-workspace details
	workspaces := make(map[string]interface{})
	for workspaceID, usage := range m.workspaceUsage {
		activeRequests := m.activeRequests[workspaceID]
		
		workspaceStats := map[string]interface{}{
			"name":                m.getWorkspaceName(workspaceID),
			"active_requests":     activeRequests,
			"total_queries":       usage.QueryCount,
			"avg_response_time":   usage.AvgResponseTime,
			"last_access":         usage.LastUpdated.Unix(),
			"access_pattern":      m.determineAccessPattern(workspaceID),
			"memory_usage_mb":     usage.MemoryMB,
			"document_count":      usage.DocumentCount,
		}
		
		// Add resource limits if available
		if limits, exists := m.config.Cluster.ResourceLimits[workspaceID]; exists {
			workspaceStats["resource_limits"] = map[string]interface{}{
				"max_concurrent_requests": limits.MaxConcurrentRequests,
				"max_tokens_per_minute":   limits.MaxTokensPerMinute,
				"max_documents_per_query": limits.MaxDocumentsPerQuery,
				"max_memory_mb":          limits.MaxMemoryMB,
				"priority":               limits.Priority,
			}
		}
		
		workspaces[workspaceID] = workspaceStats
	}
	
	stats["workspaces"] = workspaces
	stats["resource_limits_enabled"] = m.config.Cluster.Enabled
	stats["workspace_routing_enabled"] = m.config.Cluster.Enabled && m.config.Cluster.Affinity.WorkspaceRouting
	
	return stats
}