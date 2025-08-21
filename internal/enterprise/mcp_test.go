package enterprise

import (
	"testing"
	"time"
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

// TestMCPParameter_Fields removed because MCPParameter type doesn't exist in the actual code