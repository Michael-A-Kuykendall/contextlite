package mcp

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"log"
	"net"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"time"

	"contextlite/internal/registry"
)

// sanitizeProjectName removes dangerous characters from project names
func sanitizeProjectName(name string) string {
	// SECURITY: Allow only alphanumeric, hyphens, underscores
	validPattern := regexp.MustCompile(`[^a-zA-Z0-9\-_]`)
	sanitized := validPattern.ReplaceAllString(name, "")
	
	// SECURITY: Prevent empty names and path injection
	if sanitized == "" || strings.Contains(sanitized, "..") {
		return ""
	}
	
	// SECURITY: Limit length to prevent buffer issues
	if len(sanitized) > 50 {
		sanitized = sanitized[:50]
	}
	
	return sanitized
}

// MCPServer implements Model Context Protocol server for ContextLite
type MCPServer struct {
	ProjectName    string
	ProjectPath    string
	RegistryPath   string
	SystemRegistry *registry.SystemRegistry
	Listener       net.Listener
	Running        bool
}

// MCPResource represents a resource exposed via MCP
type MCPResource struct {
	URI         string      `json:"uri"`
	Name        string      `json:"name"`
	Description string      `json:"description"`
	MimeType    string      `json:"mimeType"`
	Content     interface{} `json:"content"`
}

// MCPServerInfo contains MCP server information
type MCPServerInfo struct {
	Name         string   `json:"name"`
	Version      string   `json:"version"`
	Resources    []string `json:"resources"`
	Tools        []string `json:"tools"`
	Prompts      []string `json:"prompts"`
	Capabilities struct {
		Resources   bool `json:"resources"`
		Tools       bool `json:"tools"`
		Prompts     bool `json:"prompts"`
		Logging     bool `json:"logging"`
	} `json:"capabilities"`
}

// NewMCPServer creates a new MCP server for a ContextLite project
func NewMCPServer(projectName, projectPath string) *MCPServer {
	registryPath := filepath.Join(projectPath, "internal", "registry", "system_registry.json")
	
	return &MCPServer{
		ProjectName:  projectName,
		ProjectPath:  projectPath,
		RegistryPath: registryPath,
	}
}

// Start starts the MCP server on a unix socket
func (s *MCPServer) Start() error {
	// SECURITY: Sanitize project name to prevent path injection
	sanitizedName := sanitizeProjectName(s.ProjectName)
	if sanitizedName == "" {
		return fmt.Errorf("invalid project name for MCP socket")
	}
	
	// Create socket path in user's .contextlite directory
	homeDir, _ := os.UserHomeDir()
	socketDir := filepath.Join(homeDir, ".contextlite", "mcp")
	os.MkdirAll(socketDir, 0755)
	
	socketPath := filepath.Join(socketDir, fmt.Sprintf("%s.sock", sanitizedName))
	
	// Remove existing socket if it exists
	os.Remove(socketPath)
	
	// Create unix socket listener
	listener, err := net.Listen("unix", socketPath)
	if err != nil {
		return fmt.Errorf("failed to create MCP socket: %w", err)
	}
	
	s.Listener = listener
	s.Running = true
	
	log.Printf("MCP server started for %s: %s", s.ProjectName, socketPath)
	
	// Accept connections
	for s.Running {
		conn, err := listener.Accept()
		if err != nil {
			if s.Running {
				log.Printf("MCP accept error: %v", err)
			}
			continue
		}
		
		go s.handleConnection(conn)
	}
	
	return nil
}

// Stop stops the MCP server
func (s *MCPServer) Stop() error {
	s.Running = false
	if s.Listener != nil {
		return s.Listener.Close()
	}
	return nil
}

// handleConnection handles individual MCP client connections
func (s *MCPServer) handleConnection(conn net.Conn) {
	defer conn.Close()
	
	decoder := json.NewDecoder(conn)
	encoder := json.NewEncoder(conn)
	
	for {
		var request map[string]interface{}
		if err := decoder.Decode(&request); err != nil {
			return
		}
		
		response := s.handleRequest(request)
		
		if err := encoder.Encode(response); err != nil {
			return
		}
	}
}

// handleRequest processes MCP JSON-RPC requests
func (s *MCPServer) handleRequest(request map[string]interface{}) map[string]interface{} {
	method, ok := request["method"].(string)
	if !ok {
		return s.errorResponse("invalid method")
	}
	
	id := request["id"]
	
	switch method {
	case "initialize":
		return s.handleInitialize(id)
	case "resources/list":
		return s.handleResourcesList(id)
	case "resources/read":
		return s.handleResourceRead(request, id)
	case "tools/list":
		return s.handleToolsList(id)
	case "tools/call":
		return s.handleToolCall(request, id)
	default:
		return s.errorResponse("method not found")
	}
}

// handleInitialize handles MCP initialization
func (s *MCPServer) handleInitialize(id interface{}) map[string]interface{} {
	serverInfo := MCPServerInfo{
		Name:    fmt.Sprintf("contextlite-%s", s.ProjectName),
		Version: "1.0.0",
		Resources: []string{
			"contextlite://registry/components",
			"contextlite://registry/alerts",
			"contextlite://registry/coverage",
		},
		Tools: []string{
			"query_context",
			"update_registry",
		},
	}
	
	serverInfo.Capabilities.Resources = true
	serverInfo.Capabilities.Tools = true
	serverInfo.Capabilities.Logging = true
	
	return map[string]interface{}{
		"jsonrpc": "2.0",
		"id":      id,
		"result":  serverInfo,
	}
}

// handleResourcesList returns available resources
func (s *MCPServer) handleResourcesList(id interface{}) map[string]interface{} {
	resources := []MCPResource{
		{
			URI:         "contextlite://registry/components",
			Name:        "System Components",
			Description: fmt.Sprintf("All registered components for %s", s.ProjectName),
			MimeType:    "application/json",
		},
		{
			URI:         "contextlite://registry/alerts",
			Name:        "Critical Alerts",
			Description: "Current system alerts and issues",
			MimeType:    "application/json",
		},
		{
			URI:         "contextlite://registry/coverage",
			Name:        "Test Coverage Report", 
			Description: "Current test coverage and production readiness metrics",
			MimeType:    "application/json",
		},
	}
	
	return map[string]interface{}{
		"jsonrpc": "2.0",
		"id":      id,
		"result": map[string]interface{}{
			"resources": resources,
		},
	}
}

// handleResourceRead reads specific resource content
func (s *MCPServer) handleResourceRead(request map[string]interface{}, id interface{}) map[string]interface{} {
	params, ok := request["params"].(map[string]interface{})
	if !ok {
		return s.errorResponse("invalid params")
	}
	
	uri, ok := params["uri"].(string)
	if !ok {
		return s.errorResponse("missing uri")
	}
	
	var content interface{}
	var err error
	
	switch uri {
	case "contextlite://registry/components":
		content, err = s.getComponentsContent()
	case "contextlite://registry/alerts":
		content, err = s.getAlertsContent()
	case "contextlite://registry/coverage":
		content, err = s.getCoverageContent()
	default:
		return s.errorResponse("resource not found")
	}
	
	if err != nil {
		return s.errorResponse(err.Error())
	}
	
	return map[string]interface{}{
		"jsonrpc": "2.0",
		"id":      id,
		"result": map[string]interface{}{
			"contents": []map[string]interface{}{
				{
					"uri":      uri,
					"mimeType": "application/json",
					"text":     content,
				},
			},
		},
	}
}

// handleToolsList returns available tools
func (s *MCPServer) handleToolsList(id interface{}) map[string]interface{} {
	tools := []map[string]interface{}{
		{
			"name":        "query_context",
			"description": fmt.Sprintf("Query context from %s project database", s.ProjectName),
			"inputSchema": map[string]interface{}{
				"type": "object",
				"properties": map[string]interface{}{
					"query": map[string]interface{}{
						"type":        "string",
						"description": "Search query for context database",
					},
					"max_results": map[string]interface{}{
						"type":        "number",
						"description": "Maximum number of results to return",
						"default":     10,
					},
				},
				"required": []string{"query"},
			},
		},
	}
	
	return map[string]interface{}{
		"jsonrpc": "2.0",
		"id":      id,
		"result": map[string]interface{}{
			"tools": tools,
		},
	}
}

// handleToolCall executes tool calls
func (s *MCPServer) handleToolCall(request map[string]interface{}, id interface{}) map[string]interface{} {
	params, ok := request["params"].(map[string]interface{})
	if !ok {
		return s.errorResponse("invalid params")
	}
	
	name, ok := params["name"].(string)
	if !ok {
		return s.errorResponse("missing tool name")
	}
	
	arguments, _ := params["arguments"].(map[string]interface{})
	
	switch name {
	case "query_context":
		return s.executeQueryContext(arguments, id)
	default:
		return s.errorResponse("tool not found")
	}
}

// executeQueryContext performs context query
func (s *MCPServer) executeQueryContext(args map[string]interface{}, id interface{}) map[string]interface{} {
	query, ok := args["query"].(string)
	if !ok {
		return s.errorResponse("missing query parameter")
	}
	
	// This would integrate with ContextLite's actual query engine
	results := map[string]interface{}{
		"query":        query,
		"project":      s.ProjectName,
		"results_count": 0,
		"documents":    []interface{}{},
		"message":      fmt.Sprintf("Context query executed for %s", s.ProjectName),
	}
	
	return map[string]interface{}{
		"jsonrpc": "2.0",
		"id":      id,
		"result": map[string]interface{}{
			"content": []map[string]interface{}{
				{
					"type": "text",
					"text": fmt.Sprintf("Query results: %v", results),
				},
			},
		},
	}
}

// getComponentsContent returns system components data
func (s *MCPServer) getComponentsContent() (string, error) {
	// Load current system registry
	if _, err := os.Stat(s.RegistryPath); os.IsNotExist(err) {
		return `{"components": [], "message": "No registry found"}`, nil
	}
	
	data, err := ioutil.ReadFile(s.RegistryPath)
	if err != nil {
		return "", err
	}
	
	// Return registry content as string for MCP
	return string(data), nil
}

// getAlertsContent returns current system alerts
func (s *MCPServer) getAlertsContent() (string, error) {
	alerts := map[string]interface{}{
		"timestamp": time.Now().Format(time.RFC3339),
		"project":   s.ProjectName,
		"alerts":    []interface{}{},
		"status":    "healthy",
	}
	
	data, err := json.Marshal(alerts)
	if err != nil {
		return "", err
	}
	
	return string(data), nil
}

// getCoverageContent returns test coverage information
func (s *MCPServer) getCoverageContent() (string, error) {
	coverage := map[string]interface{}{
		"timestamp":        time.Now().Format(time.RFC3339),
		"project":          s.ProjectName,
		"overall_coverage": "unknown",
		"packages":         []interface{}{},
		"status":          "ready_for_analysis",
	}
	
	data, err := json.Marshal(coverage)
	if err != nil {
		return "", err
	}
	
	return string(data), nil
}

// errorResponse creates an MCP error response
func (s *MCPServer) errorResponse(message string) map[string]interface{} {
	return map[string]interface{}{
		"jsonrpc": "2.0",
		"error": map[string]interface{}{
			"code":    -32000,
			"message": message,
		},
	}
}