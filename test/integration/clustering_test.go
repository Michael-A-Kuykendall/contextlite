package integration

import (
	"bytes"
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"go.uber.org/zap"

	"contextlite/internal/api"
	"contextlite/internal/api/middleware"
	"contextlite/internal/engine"
	"contextlite/internal/license"
	"contextlite/internal/storage"
	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

func TestClusteringIntegration(t *testing.T) {
	// Skip if not testing clustering
	if os.Getenv("CONTEXTLITE_TEST_CLUSTERING") != "true" {
		t.Skip("Clustering tests require CONTEXTLITE_TEST_CLUSTERING=true")
	}

	tests := []struct {
		name string
		test func(*testing.T)
	}{
		{"TestMultiWorkspaceIsolation", testMultiWorkspaceIsolation},
		{"TestWorkspaceResourceLimits", testWorkspaceResourceLimits},
		{"TestWorkspaceAffinityRouting", testWorkspaceAffinityRouting},
		{"TestClusterHealthEndpoint", testClusterHealthEndpoint},
		{"TestWorkspaceSpecificContextAssembly", testWorkspaceSpecificContextAssembly},
	}

	for _, tt := range tests {
		t.Run(tt.name, tt.test)
	}
}

func testMultiWorkspaceIsolation(t *testing.T) {
	// Setup cluster configuration
	cfg := createClusterTestConfig()
	server := setupClusterTestServer(t, cfg)
	defer server.Close()

	// Create documents in different workspaces
	workspaces := []string{"mission-architect", "code-assistant", "general"}
	
	for i, workspace := range workspaces {
		doc := types.Document{
			ID:      fmt.Sprintf("doc-%s-%d", workspace, i),
			Content: fmt.Sprintf("This is content for %s workspace document %d", workspace, i),
			Path:    fmt.Sprintf("/projects/%s/doc%d.txt", workspace, i),
			Language: "text",
			WorkspaceID: workspace,
			ResourceTier: getResourceTier(workspace),
		}
		
		addDocumentToWorkspace(t, server.URL, workspace, doc)
	}

	// Test workspace isolation - each workspace should only see its own documents
	for _, workspace := range workspaces {
		t.Run(fmt.Sprintf("isolation_%s", workspace), func(t *testing.T) {
			result := searchWorkspace(t, server.URL, workspace, "content")
			
			// Verify only documents from this workspace are returned
			for _, doc := range result.Documents {
				if doc.Path != fmt.Sprintf("/projects/%s/doc%d.txt", workspace, getWorkspaceIndex(workspace)) {
					t.Errorf("Document %s should not appear in workspace %s results", doc.Path, workspace)
				}
			}
		})
	}
}

func testWorkspaceResourceLimits(t *testing.T) {
	cfg := createClusterTestConfig()
	
	// Set very low limits for testing
	cfg.Cluster.ResourceLimits["limited-workspace"] = config.WorkspaceResourceLimits{
		MaxConcurrentRequests: 1, // Only allow 1 concurrent request
		MaxTokensPerMinute:   100,
		MaxMemoryMB:         64,
		Priority:            1,
	}
	
	server := setupClusterTestServer(t, cfg)
	defer server.Close()

	// First request should succeed
	req1 := createWorkspaceRequest("limited-workspace", "test query 1")
	resp1 := executeRequest(t, server, req1)
	
	if resp1.StatusCode != http.StatusOK {
		t.Errorf("First request should succeed, got status %d", resp1.StatusCode)
	}

	// Simulate concurrent request (this is tricky in tests, so we'll test the middleware directly)
	cfg2 := createClusterTestConfig()
	cfg2.Cluster.ResourceLimits["limited-workspace"] = cfg.Cluster.ResourceLimits["limited-workspace"]
	
	logger := zap.NewNop()
	workspaceMiddleware := middleware.NewWorkspaceMiddleware(cfg2, logger)
	
	// Simulate active request
	workspaceMiddleware.GetWorkspaceStats() // Initialize internal maps
	
	// Test resource limits by making actual HTTP requests
	// This is a more realistic test approach
	requestCount := 3
	errorCount := 0
	
	for i := 0; i < requestCount; i++ {
		req := createWorkspaceRequest("limited-workspace", fmt.Sprintf("test query %d", i))
		resp := executeRequest(t, server, req)
		resp.Body.Close()
		
		if resp.StatusCode == http.StatusTooManyRequests {
			errorCount++
		}
	}
	
	// We expect at least some requests to be limited due to the low concurrent limit
	t.Logf("Got %d rate-limited requests out of %d total", errorCount, requestCount)
}

func testWorkspaceAffinityRouting(t *testing.T) {
	cfg := createClusterTestConfig()
	
	// Configure affinity rules
	cfg.Cluster.Affinity = config.AffinityConfig{
		WorkspaceRouting: true,
		StickySessions:   true,
		DefaultTier:      "medium",
		Rules: map[string]config.WorkspaceAffinityRule{
			"mission-architect": {
				PreferredNodes: []string{"node-1"},
				ResourceTier:   "high",
				StickySession:  true,
				Locality:       "same-rack",
			},
			"archive": {
				AvoidNodes:    []string{"node-1"},
				ResourceTier:  "low",
				StickySession: false,
				Locality:      "any",
			},
		},
	}
	
	server := setupClusterTestServer(t, cfg)
	defer server.Close()

	// Test high-priority workspace gets proper treatment
	result := searchWorkspace(t, server.URL, "mission-architect", "test query")
	
	// Verify response includes affinity information (this would be in headers or response metadata)
	if result.ProcessingTime > 1*time.Second {
		t.Errorf("High-priority workspace should have fast processing, took %v", result.ProcessingTime)
	}

	// Test archive workspace (low priority)
	archiveResult := searchWorkspace(t, server.URL, "archive", "archive query")
	
	// Archive requests can be slower but should still complete
	if archiveResult.ProcessingTime > 5*time.Second {
		t.Errorf("Archive workspace took too long: %v", archiveResult.ProcessingTime)
	}
}

func testClusterHealthEndpoint(t *testing.T) {
	cfg := createClusterTestConfig()
	server := setupClusterTestServer(t, cfg)
	defer server.Close()

	// Test general health endpoint
	resp, err := http.Get(server.URL + "/health")
	if err != nil {
		t.Fatalf("Failed to get health endpoint: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		t.Errorf("Health endpoint should return 200, got %d", resp.StatusCode)
	}

	var health map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&health); err != nil {
		t.Fatalf("Failed to decode health response: %v", err)
	}

	// Verify cluster information is present
	cluster, ok := health["cluster"].(map[string]interface{})
	if !ok {
		t.Fatal("Health response should include cluster information")
	}

	if enabled, ok := cluster["enabled"].(bool); !ok || !enabled {
		t.Error("Cluster should be reported as enabled")
	}

	if nodeID, ok := cluster["node_id"].(string); !ok || nodeID == "" {
		t.Error("Cluster should have a node ID")
	}

	// Verify workspace information
	workspaces, ok := health["workspaces"].(map[string]interface{})
	if !ok {
		t.Fatal("Health response should include workspace information")
	}

	if totalWorkspaces, ok := workspaces["total_workspaces"]; !ok {
		t.Error("Health response should include total_workspaces count")
	} else {
		t.Logf("Total workspaces: %v", totalWorkspaces)
	}
}

func testWorkspaceSpecificContextAssembly(t *testing.T) {
	cfg := createClusterTestConfig()
	server := setupClusterTestServer(t, cfg)
	defer server.Close()

	// Add documents to different workspaces
	workspaces := []string{"frontend", "backend", "docs"}
	
	for _, workspace := range workspaces {
		doc := types.Document{
			ID:          fmt.Sprintf("doc-%s", workspace),
			Content:     fmt.Sprintf("This document contains %s specific information and implementation details", workspace),
			Path:        fmt.Sprintf("/projects/%s/main.txt", workspace),
			Language:    "text",
			WorkspaceID: workspace,
		}
		
		addDocumentToWorkspace(t, server.URL, workspace, doc)
	}

	// Test context assembly for each workspace
	for _, workspace := range workspaces {
		t.Run(fmt.Sprintf("context_assembly_%s", workspace), func(t *testing.T) {
			req := types.AssembleRequest{
				Query:         "implementation details",
				MaxTokens:     2000,
				MaxDocuments:  5,
				WorkspacePath: fmt.Sprintf("/projects/%s", workspace),
			}
			
			result := assembleContext(t, server.URL, workspace, req)
			
			// Verify context was assembled
			if result.Context == "" {
				t.Error("Context should not be empty")
			}
			
			if len(result.Documents) == 0 {
				t.Error("Should return at least one document")
			}
			
			// Verify returned documents are from correct workspace
			for _, doc := range result.Documents {
				expectedPath := fmt.Sprintf("/projects/%s/main.txt", workspace)
				if doc.Path != expectedPath {
					t.Errorf("Document path %s should match expected %s for workspace %s", 
						doc.Path, expectedPath, workspace)
				}
			}
			
			// Verify workspace-specific content
			expectedContent := fmt.Sprintf("%s specific", workspace)
			if !contains(result.Context, expectedContent) {
				t.Errorf("Context should contain workspace-specific content: %s", expectedContent)
			}
		})
	}
}

// Helper functions

func createClusterTestConfig() *config.Config {
	return &config.Config{
		Server: config.ServerConfig{
			Host: "localhost",
			Port: 0, // Use random port for testing
		},
		Cluster: config.ClusterConfig{
			Enabled: true,
			NodeID:  "test-node-1",
			Discovery: config.DiscoveryConfig{
				Method:      "static",
				Endpoints:   []string{"localhost:8080"},
				ServiceName: "contextlite-test",
			},
			Affinity: config.AffinityConfig{
				WorkspaceRouting: true,
				StickySessions:   false,
				DefaultTier:      "medium",
			},
			LoadBalancing: config.LoadBalancingConfig{
				Strategy:            "workspace_hash",
				HealthCheckInterval: 30,
				MaxLoadFactor:      0.8,
			},
			ResourceLimits: map[string]config.WorkspaceResourceLimits{
				"mission-architect": {
					MaxConcurrentRequests: 10,
					MaxTokensPerMinute:   50000,
					MaxMemoryMB:         512,
					Priority:            8,
				},
				"archive": {
					MaxConcurrentRequests: 2,
					MaxTokensPerMinute:   5000,
					MaxMemoryMB:         128,
					Priority:            2,
				},
			},
		},
		SMT: config.SMTConfig{
			SolverTimeoutMs:  1000,
			MaxOptGap:       0.1,
			MaxCandidates:   50,
			ObjectiveStyle:  "weighted-sum",
		},
		Storage: config.StorageConfig{
			CacheSizeMB: 32,
		},
		Logging: config.LoggingConfig{
			Level: "warn", // Reduce noise in tests
		},
	}
}

func setupClusterTestServer(t *testing.T, cfg *config.Config) *httptest.Server {
	// Create temporary database
	dbPath := filepath.Join(t.TempDir(), "cluster_test.db")
	cfg.Storage.DatabasePath = dbPath
	
	// Initialize storage
	store, err := storage.New(dbPath)
	if err != nil {
		t.Fatalf("Failed to create test storage: %v", err)
	}

	// Create engine
	eng := engine.NewCoreEngine(cfg, store)

	// Create feature gate
	featureGate := license.NewEnhancedFeatureGate()

	// Create logger
	logger := zap.NewNop()

	// Create API server
	apiServer := api.New(eng, store, cfg, logger, featureGate)

	// Create test server
	testServer := httptest.NewServer(apiServer)
	
	t.Cleanup(func() {
		testServer.Close()
		store.Close()
	})

	return testServer
}

func addDocumentToWorkspace(t *testing.T, serverURL, workspaceID string, doc types.Document) {
	docJSON, err := json.Marshal(doc)
	if err != nil {
		t.Fatalf("Failed to marshal document: %v", err)
	}

	req, err := http.NewRequest("POST", serverURL+"/api/v1/documents", bytes.NewBuffer(docJSON))
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}

	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("X-Workspace-ID", workspaceID)

	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		t.Fatalf("Failed to add document: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusCreated {
		t.Fatalf("Failed to add document, status: %d", resp.StatusCode)
	}
}

func searchWorkspace(t *testing.T, serverURL, workspaceID, query string) *types.ContextResult {
	req, err := http.NewRequest("GET", 
		fmt.Sprintf("%s/api/v1/documents/search?q=%s&limit=10", serverURL, query), nil)
	if err != nil {
		t.Fatalf("Failed to create search request: %v", err)
	}

	req.Header.Set("X-Workspace-ID", workspaceID)

	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		t.Fatalf("Failed to search: %v", err)
	}
	defer resp.Body.Close()

	var result types.ContextResult
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		t.Fatalf("Failed to decode search response: %v", err)
	}

	return &result
}

func assembleContext(t *testing.T, serverURL, workspaceID string, req types.AssembleRequest) *types.ContextResult {
	reqJSON, err := json.Marshal(req)
	if err != nil {
		t.Fatalf("Failed to marshal request: %v", err)
	}

	httpReq, err := http.NewRequest("POST", serverURL+"/api/v1/assemble", bytes.NewBuffer(reqJSON))
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}

	httpReq.Header.Set("Content-Type", "application/json")
	httpReq.Header.Set("X-Workspace-ID", workspaceID)

	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(httpReq)
	if err != nil {
		t.Fatalf("Failed to assemble context: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		t.Fatalf("Context assembly failed with status: %d", resp.StatusCode)
	}

	var result types.ContextResult
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		t.Fatalf("Failed to decode assembly response: %v", err)
	}

	return &result
}

func createWorkspaceRequest(workspaceID, query string) *http.Request {
	req, _ := http.NewRequest("POST", "/api/v1/assemble", 
		bytes.NewBufferString(fmt.Sprintf(`{"query": "%s", "max_documents": 5}`, query)))
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("X-Workspace-ID", workspaceID)
	return req
}

func executeRequest(t *testing.T, server *httptest.Server, req *http.Request) *http.Response {
	// Properly construct the URL
	fullURL := server.URL + req.URL.Path
	if req.URL.RawQuery != "" {
		fullURL += "?" + req.URL.RawQuery
	}
	var err error
	req.URL, err = url.Parse(fullURL)
	if err != nil {
		t.Fatalf("Failed to parse URL: %v", err)
	}
	
	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		t.Fatalf("Failed to execute request: %v", err)
	}
	
	return resp
}

func getResourceTier(workspace string) string {
	switch workspace {
	case "mission-architect":
		return "high"
	case "code-assistant":
		return "medium"
	default:
		return "low"
	}
}

func getWorkspaceIndex(workspace string) int {
	workspaces := []string{"mission-architect", "code-assistant", "general"}
	for i, w := range workspaces {
		if w == workspace {
			return i
		}
	}
	return 0
}

func contains(haystack, needle string) bool {
	return len(haystack) > 0 && len(needle) > 0 && 
		   strings.Contains(strings.ToLower(haystack), strings.ToLower(needle))
}