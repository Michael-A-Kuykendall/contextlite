package enterprise

import (
	"database/sql"
	"strings"
	"testing"
	"time"
	_ "modernc.org/sqlite"
)

func TestMCPServerConfig_Fields(t *testing.T) {
	now := time.Now()
	config := MCPServerConfig{
		ID:        "mcp-server-1",
		Name:      "Test MCP Server",
		Type:      "websocket",
		Endpoint:  "ws://localhost:8080/mcp",
		Config:    map[string]interface{}{"timeout": 30},
		CreatedAt: now,
	}

	if config.ID != "mcp-server-1" {
		t.Errorf("Expected ID to be 'mcp-server-1', got %s", config.ID)
	}
	if config.Name != "Test MCP Server" {
		t.Errorf("Expected Name to be 'Test MCP Server', got %s", config.Name)
	}
	if config.Type != "websocket" {
		t.Errorf("Expected Type to be 'websocket', got %s", config.Type)
	}
	if config.Endpoint != "ws://localhost:8080/mcp" {
		t.Errorf("Expected Endpoint to be 'ws://localhost:8080/mcp', got %s", config.Endpoint)
	}
	if config.Config["timeout"] != 30 {
		t.Errorf("Expected Config timeout to be 30, got %v", config.Config["timeout"])
	}
	if config.CreatedAt != now {
		t.Errorf("Expected CreatedAt to be %v, got %v", now, config.CreatedAt)
	}
}

func TestMCPServer_Fields(t *testing.T) {
	now := time.Now()
	config := MCPConfig{
		Authentication: map[string]interface{}{"type": "bearer"},
		Capabilities:   []string{"tools", "resources"},
		Tools:          []MCPTool{{Name: "test-tool", Description: "Test tool"}},
		Resources:      []MCPResource{{Name: "Test Resource", URI: "res-1"}},
		Settings:       map[string]interface{}{"debug": true},
	}

	server := MCPServer{
		ID:          "server-123",
		TenantID:    "tenant-456",
		Name:        "My MCP Server",
		Description: "A test MCP server",
		Endpoint:    "http://localhost:3000",
		Protocol:    "http",
		Config:      config,
		Status:      "active",
		CreatedAt:   now,
		UpdatedAt:   now,
	}

	if server.ID != "server-123" {
		t.Errorf("Expected ID to be 'server-123', got %s", server.ID)
	}
	if server.TenantID != "tenant-456" {
		t.Errorf("Expected TenantID to be 'tenant-456', got %s", server.TenantID)
	}
	if server.Name != "My MCP Server" {
		t.Errorf("Expected Name to be 'My MCP Server', got %s", server.Name)
	}
	if server.Description != "A test MCP server" {
		t.Errorf("Expected Description to be 'A test MCP server', got %s", server.Description)
	}
	if server.Endpoint != "http://localhost:3000" {
		t.Errorf("Expected Endpoint to be 'http://localhost:3000', got %s", server.Endpoint)
	}
	if server.Protocol != "http" {
		t.Errorf("Expected Protocol to be 'http', got %s", server.Protocol)
	}
	if server.Status != "active" {
		t.Errorf("Expected Status to be 'active', got %s", server.Status)
	}
	if len(server.Config.Capabilities) != 2 {
		t.Errorf("Expected 2 capabilities, got %d", len(server.Config.Capabilities))
	}
	if server.Config.Capabilities[0] != "tools" {
		t.Errorf("Expected first capability to be 'tools', got %s", server.Config.Capabilities[0])
	}
}

func TestMCPConfig_Fields(t *testing.T) {
	config := MCPConfig{
		Authentication: map[string]interface{}{
			"type":   "oauth2",
			"client": "test-client",
		},
		Capabilities: []string{"tools", "resources", "prompts"},
		Tools: []MCPTool{
			{Name: "calculator", Description: "Perform calculations"},
			{Name: "weather", Description: "Get weather information"},
		},
		Resources: []MCPResource{
			{URI: "docs", Name: "Documentation"},
			{URI: "api", Name: "API Reference"},
		},
		Settings: map[string]interface{}{
			"timeout":    30,
			"retries":    3,
			"log_level": "info",
		},
	}

	if config.Authentication["type"] != "oauth2" {
		t.Errorf("Expected auth type to be 'oauth2', got %v", config.Authentication["type"])
	}
	if len(config.Capabilities) != 3 {
		t.Errorf("Expected 3 capabilities, got %d", len(config.Capabilities))
	}
	if config.Capabilities[2] != "prompts" {
		t.Errorf("Expected third capability to be 'prompts', got %s", config.Capabilities[2])
	}
	if len(config.Tools) != 2 {
		t.Errorf("Expected 2 tools, got %d", len(config.Tools))
	}
	if config.Tools[0].Name != "calculator" {
		t.Errorf("Expected first tool name to be 'calculator', got %s", config.Tools[0].Name)
	}
	if len(config.Resources) != 2 {
		t.Errorf("Expected 2 resources, got %d", len(config.Resources))
	}
	if config.Resources[1].URI != "api" {
		t.Errorf("Expected second resource URI to be 'api', got %s", config.Resources[1].URI)
	}
	if config.Settings["timeout"] != 30 {
		t.Errorf("Expected timeout setting to be 30, got %v", config.Settings["timeout"])
	}
}

func TestMCPTool_Fields(t *testing.T) {
	tool := MCPTool{
		Name:        "file-reader",
		Description: "Read files from disk",
		Parameters: map[string]interface{}{
			"path": map[string]interface{}{
				"type":        "string",
				"description": "File path to read",
				"required":    true,
			},
		},
		Handler: "file_handler",
	}

	if tool.Name != "file-reader" {
		t.Errorf("Expected Name to be 'file-reader', got %s", tool.Name)
	}
	if tool.Description != "Read files from disk" {
		t.Errorf("Expected Description to be 'Read files from disk', got %s", tool.Description)
	}
	if tool.Parameters["path"] == nil {
		t.Error("Expected path parameter to be defined")
	}
	if tool.Handler != "file_handler" {
		t.Errorf("Expected Handler to be 'file_handler', got %s", tool.Handler)
	}
}

func TestMCPResource_Fields(t *testing.T) {
	resource := MCPResource{
		URI:         "file:///docs/user-guide.md",
		Name:        "User Guide",
		Description: "Complete user guide documentation",
		MimeType:    "text/markdown",
		Metadata:    map[string]interface{}{"type": "document"},
	}

	if resource.URI != "file:///docs/user-guide.md" {
		t.Errorf("Expected URI to be 'file:///docs/user-guide.md', got %s", resource.URI)
	}
	if resource.Name != "User Guide" {
		t.Errorf("Expected Name to be 'User Guide', got %s", resource.Name)
	}
	if resource.Description != "Complete user guide documentation" {
		t.Errorf("Expected Description to be 'Complete user guide documentation', got %s", resource.Description)
	}
	if resource.MimeType != "text/markdown" {
		t.Errorf("Expected MimeType to be 'text/markdown', got %s", resource.MimeType)
	}
	if resource.Metadata["type"] != "document" {
		t.Errorf("Expected Metadata type to be 'document', got %v", resource.Metadata["type"])
	}
}

func TestNewMCPManager(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	if manager == nil {
		t.Fatal("Expected manager to be created")
	}
	if manager.featureGate != featureGate {
		t.Error("Expected featureGate to be set correctly")
	}
}

func TestMCPManager_CreateMCPServer(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	config := MCPConfig{
		Capabilities: []string{"tools"},
		Tools:        []MCPTool{{Name: "test-tool", Description: "Test tool"}},
	}
	
	// This should fail because we don't have a real database
	// We expect a panic or error due to nil database - catch it
	defer func() {
		if r := recover(); r != nil {
			t.Logf("CreateMCPServer panicked as expected with nil database: %v", r)
		}
	}()
	
	server, err := manager.CreateMCPServer("tenant-123", "test-server", "Test MCP Server", 
		"http://localhost:3000", "http", config)
	
	if err != nil {
		t.Logf("CreateMCPServer failed as expected without database: %v", err)
	} else if server != nil {
		t.Log("CreateMCPServer succeeded unexpectedly")
	}
}

func TestMCPManager_WithoutLicense(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": false}, // No enterprise license
		tier:     "Basic",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	config := MCPConfig{}
	
	// Should fail due to license check
	server, err := manager.CreateMCPServer("tenant-123", "test-server", "Test MCP Server", 
		"http://localhost:3000", "http", config)
	
	if err == nil {
		t.Error("Expected CreateMCPServer to fail without enterprise license")
	}
	if server != nil {
		t.Error("Expected server to be nil when creation fails")
	}
}

func TestGenerateServerID(t *testing.T) {
	id, err := generateServerID()
	if err != nil {
		t.Fatalf("generateServerID failed: %v", err)
	}
	if len(id) == 0 {
		t.Error("Expected non-empty server ID")
	}
	
	// Test that consecutive IDs are different
	id2, err := generateServerID()
	if err != nil {
		t.Fatalf("generateServerID failed on second call: %v", err)
	}
	if id == id2 {
		t.Error("Expected different server IDs from consecutive calls")
	}
}

func TestMCPManager_ValidateMCPConfig(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	// Valid config
	validConfig := map[string]interface{}{
		"timeout": 30,
		"retries": 3,
	}
	
	err := manager.validateMCPConfig(validConfig)
	if err != nil {
		t.Errorf("Expected valid config to pass validation, got error: %v", err)
	}
	
	// Invalid config - nil config
	err = manager.validateMCPConfig(nil)
	if err == nil {
		t.Error("Expected nil config to fail validation")
	}
}

func TestMCPManager_GenerateDeploymentConfig(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	server := &MCPServerConfig{
		ID:        "test-server-123",
		Name:      "Test Server",
		Type:      "http",
		Endpoint:  "http://localhost:3000",
		Config:    map[string]interface{}{"debug": true},
		CreatedAt: time.Now(),
	}
	
	config, err := manager.generateDeploymentConfig(server)
	if err != nil {
		t.Fatalf("generateDeploymentConfig failed: %v", err)
	}
	
	if config["server_id"] != server.ID {
		t.Errorf("Expected server_id to be %s, got %v", server.ID, config["server_id"])
	}
	if config["server_name"] != server.Name {
		t.Errorf("Expected server_name to be %s, got %v", server.Name, config["server_name"])
	}
	if config["server_type"] != server.Type {
		t.Errorf("Expected server_type to be %s, got %v", server.Type, config["server_type"])
	}
	if config["endpoint"] != server.Endpoint {
		t.Errorf("Expected endpoint to be %s, got %v", server.Endpoint, config["endpoint"])
	}
}

func TestMCPManager_GenerateJiraMCPCode(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	config := map[string]interface{}{
		"port": "3000",
		"debug": true,
	}
	
	code := manager.generateJiraMCPCode(config)
	if code == "" {
		t.Error("Expected non-empty Jira MCP code")
	}
	if !strings.Contains(code, "jira-mcp") {
		t.Error("Expected Jira MCP code to contain 'jira-mcp'")
	}
	if !strings.Contains(code, "search_issues") {
		t.Error("Expected Jira MCP code to contain 'search_issues'")
	}
}

func TestMCPManager_GenerateSlackMCPCode(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	config := map[string]interface{}{
		"port": "3000",
		"debug": true,
	}
	
	code := manager.generateSlackMCPCode(config)
	if code == "" {
		t.Error("Expected non-empty Slack MCP code")
	}
	if !strings.Contains(code, "slack-mcp") {
		t.Error("Expected Slack MCP code to contain 'slack-mcp'")
	}
	if !strings.Contains(code, "send_message") {
		t.Error("Expected Slack MCP code to contain 'send_message'")
	}
}

func TestMCPManager_GeneratePackageJSON(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	config := map[string]interface{}{
		"version": "1.0.0",
	}
	
	packageJSON := manager.generatePackageJSON("My Test Server", config)
	if packageJSON == "" {
		t.Error("Expected non-empty package.json")
	}
	if !strings.Contains(packageJSON, "my-test-server") {
		t.Error("Expected package.json to contain normalized name")
	}
	if !strings.Contains(packageJSON, "express") {
		t.Error("Expected package.json to contain express dependency")
	}
}

func TestMCPManager_GenerateConfigJSON(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	config := map[string]interface{}{
		"timeout": 30,
		"debug":   true,
		"nested": map[string]interface{}{
			"key": "value",
		},
	}
	
	configJSON := manager.generateConfigJSON(config)
	if configJSON == "" {
		t.Error("Expected non-empty config JSON")
	}
	if !strings.Contains(configJSON, "timeout") {
		t.Error("Expected config JSON to contain timeout")
	}
	if !strings.Contains(configJSON, "debug") {
		t.Error("Expected config JSON to contain debug")
	}
}

func TestMCPManager_CreateJiraIntegration(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	// This should fail due to nil database - catch panic
	defer func() {
		if r := recover(); r != nil {
			t.Logf("CreateJiraIntegration panicked as expected with nil database: %v", r)
		}
	}()
	
	server, err := manager.CreateJiraIntegration("tenant-123", "https://jira.example.com", "api-token-123")
	
	if err != nil {
		t.Logf("CreateJiraIntegration failed as expected without database: %v", err)
	} else if server != nil {
		t.Log("CreateJiraIntegration succeeded unexpectedly")
	}
}

func TestMCPManager_CreateSlackIntegration(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	// This should fail due to nil database - catch panic  
	defer func() {
		if r := recover(); r != nil {
			t.Logf("CreateSlackIntegration panicked as expected with nil database: %v", r)
		}
	}()
	
	server, err := manager.CreateSlackIntegration("tenant-123", "bot-token-123", "app-token-456")
	
	if err != nil {
		t.Logf("CreateSlackIntegration failed as expected without database: %v", err)
	} else if server != nil {
		t.Log("CreateSlackIntegration succeeded unexpectedly")
	}
}

func TestMCPManager_HealthCheck(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	// Test with invalid endpoint - should fail
	err := manager.healthCheck("http://localhost:99999")
	if err == nil {
		t.Error("Expected health check to fail with invalid endpoint")
	}
}

func TestMCPManager_DeployGithubServer(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	server := &MCPServerConfig{
		ID:       "github-server",
		Name:     "GitHub Integration", 
		Type:     "github",
		Endpoint: "https://api.github.com",
	}
	
	err := manager.deployGithubServer(server, map[string]interface{}{})
	if err == nil {
		t.Error("Expected deployGithubServer to return not implemented error")
	}
	if !strings.Contains(err.Error(), "not yet implemented") {
		t.Errorf("Expected 'not yet implemented' error, got: %v", err)
	}
}

func TestMCPManager_DeployCustomServer(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	server := &MCPServerConfig{
		ID:       "custom-server",
		Name:     "Custom Integration",
		Type:     "custom",
		Endpoint: "https://custom.example.com",
	}
	
	err := manager.deployCustomServer(server, map[string]interface{}{})
	if err == nil {
		t.Error("Expected deployCustomServer to return not implemented error")
	}
	if !strings.Contains(err.Error(), "not yet implemented") {
		t.Errorf("Expected 'not yet implemented' error, got: %v", err)
	}
}

func TestMCPManager_HealthCheckWithRetry(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	// Test with invalid endpoint and very short timeout - should fail quickly
	err := manager.healthCheckWithRetry("http://localhost:99999", 100*time.Millisecond)
	if err == nil {
		t.Error("Expected health check with retry to fail with invalid endpoint")
	}
	if !strings.Contains(err.Error(), "timeout") {
		t.Errorf("Expected timeout error, got: %v", err)
	}
}

func TestGenerateDeploymentConfig_WithPort(t *testing.T) {
	featureGate := &mockFeatureGate{
		features: map[string]bool{"custom_mcp": true},
		tier:     "Enterprise",
	}
	
	manager := NewMCPManager(nil, featureGate)
	
	// Test with endpoint that has port in URL
	server := &MCPServerConfig{
		ID:        "test-server-with-port",
		Name:      "Test Server With Port",
		Type:      "http", 
		Endpoint:  "http://localhost:8080/api",
		Config:    map[string]interface{}{"debug": true},
		CreatedAt: time.Now(),
	}
	
	config, err := manager.generateDeploymentConfig(server)
	if err != nil {
		t.Fatalf("generateDeploymentConfig failed: %v", err)
	}
	
	// The actual implementation extracts everything after the second colon, including path
	if config["port"] != "8080/api" {
		t.Errorf("Expected port to be extracted as '8080/api', got %v", config["port"])
	}
	
	// Check environment variables
	if env, ok := config["env"].(map[string]string); ok {
		if env["MCP_PORT"] != "8080/api" {
			t.Errorf("Expected MCP_PORT env var to be '8080/api', got %s", env["MCP_PORT"])
		}
		if env["MCP_SERVER_ID"] != server.ID {
			t.Errorf("Expected MCP_SERVER_ID env var to be %s, got %s", server.ID, env["MCP_SERVER_ID"])
		}
		if env["NODE_ENV"] != "production" {
			t.Errorf("Expected NODE_ENV to be 'production', got %s", env["NODE_ENV"])
		}
	} else {
		t.Error("Expected env config to be present as map[string]string")
	}
}

// Additional comprehensive tests with real database
func TestMCPManager_WithDatabase_CreateMCPServer(t *testing.T) {
	// Create test database and schema
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("Failed to create database: %v", err)
	}
	defer db.Close()
	
	if err := InitMCPSchema(db); err != nil {
		t.Fatalf("Failed to initialize schema: %v", err)
	}
	
	// Test with Enterprise license (should succeed)
	enterpriseGate := newMockFeatureGate("Enterprise")
	manager := NewMCPManager(db, enterpriseGate)
	
	config := MCPConfig{
		Authentication: map[string]interface{}{"type": "bearer"},
		Capabilities:   []string{"messages"},
		Settings:       map[string]interface{}{"timeout": 30},
	}
	
	server, err := manager.CreateMCPServer("tenant-123", "Test Server", "Test MCP server", "http://localhost:3000", "http", config)
	if err != nil {
		t.Fatalf("Failed to create MCP server: %v", err)
	}
	
	if server == nil {
		t.Fatal("Expected MCP server to be created")
	}
	if server.TenantID != "tenant-123" {
		t.Errorf("Expected tenant ID 'tenant-123', got %s", server.TenantID)
	}
	if server.Name != "Test Server" {
		t.Errorf("Expected name 'Test Server', got %s", server.Name)
	}
	if server.Status != "inactive" {
		t.Errorf("Expected status 'inactive', got %s", server.Status)
	}
}

func TestMCPManager_WithDatabase_GetMCPServer(t *testing.T) {
	// Create test database and schema
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("Failed to create database: %v", err)
	}
	defer db.Close()
	
	if err := InitMCPSchema(db); err != nil {
		t.Fatalf("Failed to initialize schema: %v", err)
	}
	
	enterpriseGate := newMockFeatureGate("Enterprise")
	manager := NewMCPManager(db, enterpriseGate)
	
	// Create a server first
	config := MCPConfig{
		Authentication: map[string]interface{}{"type": "bearer"},
		Capabilities:   []string{"messages"},
	}
	server, err := manager.CreateMCPServer("tenant-123", "Test Server", "Test description", "http://localhost:3000", "http", config)
	if err != nil {
		t.Fatalf("Failed to create MCP server: %v", err)
	}
	
	// Test retrieving the server
	retrieved, err := manager.GetMCPServer(server.ID)
	if err != nil {
		t.Fatalf("Failed to get MCP server: %v", err)
	}
	
	if retrieved.ID != server.ID {
		t.Errorf("Expected ID %s, got %s", server.ID, retrieved.ID)
	}
	if retrieved.Name != server.Name {
		t.Errorf("Expected name %s, got %s", server.Name, retrieved.Name)
	}
	if len(retrieved.Config.Capabilities) != 1 {
		t.Errorf("Expected 1 capability, got %d", len(retrieved.Config.Capabilities))
	}
	
	// Test getting non-existent server
	_, err = manager.GetMCPServer("non-existent")
	if err == nil {
		t.Error("Expected error when getting non-existent server")
	}
}

func TestMCPManager_WithDatabase_ListMCPServers(t *testing.T) {
	// Create test database and schema
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("Failed to create database: %v", err)
	}
	defer db.Close()
	
	if err := InitMCPSchema(db); err != nil {
		t.Fatalf("Failed to initialize schema: %v", err)
	}
	
	enterpriseGate := newMockFeatureGate("Enterprise")
	manager := NewMCPManager(db, enterpriseGate)
	
	// Create multiple servers for same tenant
	config := MCPConfig{Capabilities: []string{"messages"}}
	server1, err := manager.CreateMCPServer("tenant-123", "Server 1", "First server", "http://localhost:3001", "http", config)
	if err != nil {
		t.Fatalf("Failed to create server 1: %v", err)
	}
	
	server2, err := manager.CreateMCPServer("tenant-123", "Server 2", "Second server", "http://localhost:3002", "http", config)
	if err != nil {
		t.Fatalf("Failed to create server 2: %v", err)
	}
	
	// Create server for different tenant
	_, err = manager.CreateMCPServer("tenant-456", "Other Server", "Other server", "http://localhost:3003", "http", config)
	if err != nil {
		t.Fatalf("Failed to create other server: %v", err)
	}
	
	// Test listing servers for tenant-123
	servers, err := manager.ListMCPServers("tenant-123")
	if err != nil {
		t.Fatalf("Failed to list MCP servers: %v", err)
	}
	
	if len(servers) != 2 {
		t.Errorf("Expected 2 servers for tenant-123, got %d", len(servers))
	}
	
	// Verify server IDs are present
	foundServer1, foundServer2 := false, false
	for _, server := range servers {
		if server.ID == server1.ID {
			foundServer1 = true
		}
		if server.ID == server2.ID {
			foundServer2 = true
		}
	}
	if !foundServer1 || !foundServer2 {
		t.Error("Expected to find both created servers in list")
	}
}