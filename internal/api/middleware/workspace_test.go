package middleware

import (
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	"go.uber.org/zap"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

func TestWorkspaceMiddleware_ExtractWorkspaceID(t *testing.T) {
	cfg := &config.Config{
		Cluster: config.ClusterConfig{
			Enabled: true,
		},
	}
	
	logger := zap.NewNop()
	middleware := NewWorkspaceMiddleware(cfg, logger)

	tests := []struct {
		name           string
		setupRequest   func() *http.Request
		expectedID     string
	}{
		{
			name: "header based workspace ID",
			setupRequest: func() *http.Request {
				req := httptest.NewRequest("POST", "/api/v1/assemble", nil)
				req.Header.Set("X-Workspace-ID", "test-workspace")
				return req
			},
			expectedID: "test-workspace",
		},
		{
			name: "query parameter workspace ID",
			setupRequest: func() *http.Request {
				req := httptest.NewRequest("GET", "/api/v1/search?workspace=query-workspace", nil)
				return req
			},
			expectedID: "query-workspace",
		},
		{
			name: "path based workspace ID",
			setupRequest: func() *http.Request {
				req := httptest.NewRequest("POST", "/workspace/path-workspace/api/v1/assemble", nil)
				return req
			},
			expectedID: "path-workspace",
		},
		{
			name: "user-agent inference - mission-architect",
			setupRequest: func() *http.Request {
				req := httptest.NewRequest("POST", "/api/v1/assemble", nil)
				req.Header.Set("User-Agent", "mission-architect/1.0 (context-client)")
				return req
			},
			expectedID: "mission-architect",
		},
		{
			name: "user-agent inference - code-assistant",
			setupRequest: func() *http.Request {
				req := httptest.NewRequest("POST", "/api/v1/assemble", nil)
				req.Header.Set("User-Agent", "code-assistant-client/2.0")
				return req
			},
			expectedID: "code-assistant",
		},
		{
			name: "default workspace fallback",
			setupRequest: func() *http.Request {
				req := httptest.NewRequest("POST", "/api/v1/assemble", nil)
				return req
			},
			expectedID: "default",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			req := tt.setupRequest()
			actualID := middleware.extractWorkspaceID(req)
			
			if actualID != tt.expectedID {
				t.Errorf("Expected workspace ID '%s', got '%s'", tt.expectedID, actualID)
			}
		})
	}
}

func TestWorkspaceMiddleware_ResourceLimits(t *testing.T) {
	cfg := &config.Config{
		Cluster: config.ClusterConfig{
			Enabled: true,
			ResourceLimits: map[string]config.WorkspaceResourceLimits{
				"limited-workspace": {
					MaxConcurrentRequests: 2,
					MaxTokensPerMinute:   1000,
					MaxMemoryMB:         128,
					Priority:            5,
				},
			},
		},
	}
	
	logger := zap.NewNop()
	middleware := NewWorkspaceMiddleware(cfg, logger)

	tests := []struct {
		name        string
		workspaceID string
		setupFunc   func()
		expectAllow bool
	}{
		{
			name:        "allowed under limits",
			workspaceID: "limited-workspace",
			setupFunc:   func() {},
			expectAllow: true,
		},
		{
			name:        "blocked - concurrent limit exceeded",
			workspaceID: "limited-workspace",
			setupFunc: func() {
				// Simulate 2 active requests (at limit)
				middleware.activeRequests["limited-workspace"] = 2
			},
			expectAllow: false,
		},
		{
			name:        "unknown workspace uses defaults",
			workspaceID: "unknown-workspace",
			setupFunc:   func() {},
			expectAllow: true,
		},
		{
			name:        "clustering disabled - always allowed",
			workspaceID: "any-workspace",
			setupFunc: func() {
				cfg.Cluster.Enabled = false
			},
			expectAllow: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Reset state
			middleware.activeRequests = make(map[string]int)
			middleware.workspaceUsage = make(map[string]*types.ResourceUsage)
			cfg.Cluster.Enabled = true
			
			// Setup test conditions
			tt.setupFunc()
			
			// Test resource limits
			allowed := middleware.checkResourceLimits(tt.workspaceID)
			
			if allowed != tt.expectAllow {
				t.Errorf("Expected allow=%v, got allow=%v", tt.expectAllow, allowed)
			}
		})
	}
}

func TestWorkspaceMiddleware_WorkspaceIsolation(t *testing.T) {
	cfg := &config.Config{
		Cluster: config.ClusterConfig{
			Enabled: true,
			ResourceLimits: map[string]config.WorkspaceResourceLimits{
				"test-workspace": {
					MaxConcurrentRequests: 10,
					MaxTokensPerMinute:   50000,
					Priority:            8,
				},
			},
		},
	}
	
	logger := zap.NewNop()
	middleware := NewWorkspaceMiddleware(cfg, logger)

	// Create a test handler that checks context
	var capturedWorkspace *types.WorkspaceInfo
	testHandler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if workspace, ok := r.Context().Value("workspace_info").(*types.WorkspaceInfo); ok {
			capturedWorkspace = workspace
		}
		w.WriteHeader(http.StatusOK)
	})

	// Wrap with middleware
	wrappedHandler := middleware.WorkspaceIsolation(testHandler)

	tests := []struct {
		name             string
		setupRequest     func() *http.Request
		expectedWorkspace string
	}{
		{
			name: "workspace context added correctly",
			setupRequest: func() *http.Request {
				req := httptest.NewRequest("POST", "/api/v1/assemble", nil)
				req.Header.Set("X-Workspace-ID", "test-workspace")
				return req
			},
			expectedWorkspace: "test-workspace",
		},
		{
			name: "default workspace handling",
			setupRequest: func() *http.Request {
				req := httptest.NewRequest("POST", "/api/v1/assemble", nil)
				return req
			},
			expectedWorkspace: "default",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			capturedWorkspace = nil
			
			req := tt.setupRequest()
			rr := httptest.NewRecorder()
			
			wrappedHandler.ServeHTTP(rr, req)
			
			if capturedWorkspace == nil {
				t.Fatal("Expected workspace context to be set")
			}
			
			if capturedWorkspace.ID != tt.expectedWorkspace {
				t.Errorf("Expected workspace ID '%s', got '%s'", 
					tt.expectedWorkspace, capturedWorkspace.ID)
			}
			
			if rr.Code != http.StatusOK {
				t.Errorf("Expected status 200, got %d", rr.Code)
			}
		})
	}
}

func TestWorkspaceMiddleware_ResourceLimitRejection(t *testing.T) {
	cfg := &config.Config{
		Cluster: config.ClusterConfig{
			Enabled: true,
			ResourceLimits: map[string]config.WorkspaceResourceLimits{
				"restricted-workspace": {
					MaxConcurrentRequests: 1, // Very low limit
					MaxTokensPerMinute:   100,
					Priority:            1,
				},
			},
		},
	}
	
	logger := zap.NewNop()
	middleware := NewWorkspaceMiddleware(cfg, logger)

	testHandler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
	})

	wrappedHandler := middleware.WorkspaceIsolation(testHandler)

	// First request should succeed
	req1 := httptest.NewRequest("POST", "/api/v1/assemble", nil)
	req1.Header.Set("X-Workspace-ID", "restricted-workspace")
	rr1 := httptest.NewRecorder()
	
	// Simulate first request still active
	middleware.activeRequests["restricted-workspace"] = 1
	wrappedHandler.ServeHTTP(rr1, req1)
	
	// Second request should be rejected
	req2 := httptest.NewRequest("POST", "/api/v1/assemble", nil)
	req2.Header.Set("X-Workspace-ID", "restricted-workspace")
	rr2 := httptest.NewRecorder()
	
	wrappedHandler.ServeHTTP(rr2, req2)
	
	if rr2.Code != http.StatusTooManyRequests {
		t.Errorf("Expected status 429, got %d", rr2.Code)
	}
	
	if !strings.Contains(rr2.Body.String(), "resource limits exceeded") {
		t.Errorf("Expected resource limits error message, got: %s", rr2.Body.String())
	}
}

func TestWorkspaceMiddleware_UsageTracking(t *testing.T) {
	cfg := &config.Config{
		Cluster: config.ClusterConfig{
			Enabled: true,
		},
	}
	
	logger := zap.NewNop()
	middleware := NewWorkspaceMiddleware(cfg, logger)

	workspaceID := "tracking-workspace"
	processingTime := 100 * time.Millisecond

	// Update usage stats
	middleware.updateUsageStats(workspaceID, processingTime)

	// Check usage stats were created and updated
	usage := middleware.getOrCreateUsageStats(workspaceID)
	
	if usage.QueryCount != 1 {
		t.Errorf("Expected query count 1, got %d", usage.QueryCount)
	}
	
	expectedResponseTime := float64(processingTime.Milliseconds())
	tolerance := 1.0 // 1ms tolerance for floating point comparison
	
	if abs(usage.AvgResponseTime-expectedResponseTime) > tolerance {
		t.Errorf("Expected avg response time ~%.1f, got %.1f", 
			expectedResponseTime, usage.AvgResponseTime)
	}
	
	if time.Since(usage.LastUpdated) > time.Second {
		t.Errorf("Usage timestamp not updated recently")
	}
}

func TestWorkspaceMiddleware_GetWorkspaceStats(t *testing.T) {
	cfg := &config.Config{
		Cluster: config.ClusterConfig{
			Enabled: true,
			Affinity: config.AffinityConfig{
				WorkspaceRouting: true,
			},
			ResourceLimits: map[string]config.WorkspaceResourceLimits{
				"stats-workspace": {
					MaxConcurrentRequests: 5,
					MaxTokensPerMinute:   10000,
					Priority:            7,
				},
			},
		},
	}
	
	logger := zap.NewNop()
	middleware := NewWorkspaceMiddleware(cfg, logger)

	// Setup some test data
	workspaceID := "stats-workspace"
	middleware.activeRequests[workspaceID] = 2
	middleware.updateUsageStats(workspaceID, 50*time.Millisecond)
	
	// Get stats
	stats := middleware.GetWorkspaceStats()
	
	// Verify overall stats
	if totalWorkspaces, ok := stats["total_workspaces"].(int); !ok || totalWorkspaces < 1 {
		t.Errorf("Expected at least 1 total workspace, got %v", stats["total_workspaces"])
	}
	
	if activeWorkspaces, ok := stats["active_workspaces"].(int); !ok || activeWorkspaces < 1 {
		t.Errorf("Expected at least 1 active workspace, got %v", stats["active_workspaces"])
	}
	
	// Verify workspace-specific stats
	workspaces, ok := stats["workspaces"].(map[string]interface{})
	if !ok {
		t.Fatal("Expected workspaces to be a map")
	}
	
	workspaceStats, ok := workspaces[workspaceID].(map[string]interface{})
	if !ok {
		t.Fatalf("Expected stats for workspace %s", workspaceID)
	}
	
	if activeRequests, ok := workspaceStats["active_requests"].(int); !ok || activeRequests != 2 {
		t.Errorf("Expected 2 active requests, got %v", workspaceStats["active_requests"])
	}
	
	// Verify resource limits are included
	limits, ok := workspaceStats["resource_limits"].(map[string]interface{})
	if !ok {
		t.Fatal("Expected resource_limits to be included")
	}
	
	if maxRequests, ok := limits["max_concurrent_requests"].(int); !ok || maxRequests != 5 {
		t.Errorf("Expected max_concurrent_requests=5, got %v", limits["max_concurrent_requests"])
	}
}

func TestWorkspaceMiddleware_AccessPatterns(t *testing.T) {
	cfg := &config.Config{
		Cluster: config.ClusterConfig{
			Enabled: true,
		},
	}
	
	logger := zap.NewNop()
	middleware := NewWorkspaceMiddleware(cfg, logger)

	tests := []struct {
		name            string
		setupUsage      func(string) *types.ResourceUsage
		expectedPattern string
	}{
		{
			name: "high frequency pattern",
			setupUsage: func(workspaceID string) *types.ResourceUsage {
				usage := &types.ResourceUsage{
					QueryCount:    15,
					LastUpdated:   time.Now().Add(-2 * time.Minute),
				}
				middleware.workspaceUsage[workspaceID] = usage
				return usage
			},
			expectedPattern: "high-frequency",
		},
		{
			name: "normal pattern",
			setupUsage: func(workspaceID string) *types.ResourceUsage {
				usage := &types.ResourceUsage{
					QueryCount:    7,
					LastUpdated:   time.Now().Add(-30 * time.Minute),
				}
				middleware.workspaceUsage[workspaceID] = usage
				return usage
			},
			expectedPattern: "normal",
		},
		{
			name: "archive pattern",
			setupUsage: func(workspaceID string) *types.ResourceUsage {
				usage := &types.ResourceUsage{
					QueryCount:    2,
					LastUpdated:   time.Now().Add(-2 * time.Hour),
				}
				middleware.workspaceUsage[workspaceID] = usage
				return usage
			},
			expectedPattern: "archive",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			workspaceID := tt.name + "-workspace"
			tt.setupUsage(workspaceID)
			
			pattern := middleware.determineAccessPattern(workspaceID)
			
			if pattern != tt.expectedPattern {
				t.Errorf("Expected pattern '%s', got '%s'", tt.expectedPattern, pattern)
			}
		})
	}
}

func TestWorkspaceMiddleware_PeriodicCleanup(t *testing.T) {
	cfg := &config.Config{
		Cluster: config.ClusterConfig{
			Enabled: true,
		},
	}
	
	logger := zap.NewNop()
	middleware := NewWorkspaceMiddleware(cfg, logger)

	// Add some old usage data
	oldWorkspace := "old-workspace"
	recentWorkspace := "recent-workspace"
	
	middleware.workspaceUsage[oldWorkspace] = &types.ResourceUsage{
		LastUpdated: time.Now().Add(-2 * time.Hour), // Old data
	}
	
	middleware.workspaceUsage[recentWorkspace] = &types.ResourceUsage{
		LastUpdated: time.Now().Add(-10 * time.Minute), // Recent data
	}
	
	middleware.activeRequests[oldWorkspace] = 0     // Empty counter
	middleware.activeRequests[recentWorkspace] = 2  // Active counter
	
	// Force cleanup by setting last cleanup time to past
	middleware.lastCleanup = time.Now().Add(-10 * time.Minute)
	
	// Trigger cleanup
	middleware.periodicCleanup()
	
	// Verify old workspace data was removed
	if _, exists := middleware.workspaceUsage[oldWorkspace]; exists {
		t.Errorf("Expected old workspace data to be cleaned up")
	}
	
	// Verify recent workspace data was kept
	if _, exists := middleware.workspaceUsage[recentWorkspace]; !exists {
		t.Errorf("Expected recent workspace data to be preserved")
	}
	
	// Verify empty active request counter was removed
	if _, exists := middleware.activeRequests[oldWorkspace]; exists {
		t.Errorf("Expected empty active request counter to be removed")
	}
	
	// Verify active request counter was kept
	if count, exists := middleware.activeRequests[recentWorkspace]; !exists || count != 2 {
		t.Errorf("Expected active request counter to be preserved with value 2, got %d", count)
	}
}

func TestWorkspaceMiddleware_AffinityRules(t *testing.T) {
	cfg := &config.Config{
		Cluster: config.ClusterConfig{
			Enabled: true,
			Affinity: config.AffinityConfig{
				WorkspaceRouting: true,
				StickySessions:   true,
				DefaultTier:      "medium",
				Rules: map[string]config.WorkspaceAffinityRule{
					"mission-architect": {
						PreferredNodes: []string{"node-1", "node-2"},
						AvoidNodes:     []string{"node-3"},
						ResourceTier:   "high",
						Locality:       "same-rack",
					},
				},
			},
		},
	}
	
	logger := zap.NewNop()
	middleware := NewWorkspaceMiddleware(cfg, logger)

	tests := []struct {
		name         string
		workspaceID  string
		expectRouting bool
		expectTier   string
	}{
		{
			name:         "workspace with specific rules",
			workspaceID:  "mission-architect",
			expectRouting: true,
			expectTier:   "high",
		},
		{
			name:         "workspace with default rules",
			workspaceID:  "unknown-workspace",
			expectRouting: true,
			expectTier:   "medium",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			rules := middleware.getAffinityRules(tt.workspaceID)
			
			if routing, ok := rules["routing_enabled"].(bool); !ok || routing != tt.expectRouting {
				t.Errorf("Expected routing_enabled=%v, got %v", tt.expectRouting, rules["routing_enabled"])
			}
			
			if tier, ok := rules["resource_tier"].(string); !ok || tier != tt.expectTier {
				t.Errorf("Expected resource_tier='%s', got '%v'", tt.expectTier, rules["resource_tier"])
			}
			
			// Test specific workspace rules
			if tt.workspaceID == "mission-architect" {
				preferredNodes, ok := rules["preferred_nodes"].([]string)
				if !ok || len(preferredNodes) != 2 || preferredNodes[0] != "node-1" {
					t.Errorf("Expected preferred_nodes to be properly set, got %v", rules["preferred_nodes"])
				}
			}
		})
	}
}

// Math utility for floating point comparison
func abs(x float64) float64 {
	if x < 0 {
		return -x
	}
	return x
}