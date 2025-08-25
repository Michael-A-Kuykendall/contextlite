package enterprise

import (
	"fmt"
	"time"
	"database/sql"
	"encoding/json"
	"crypto/rand"
	"encoding/hex"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"net/http"
	"contextlite/pkg/types"
)

// MCPServerConfig represents an MCP server configuration (different from MCPServer for API compatibility)
type MCPServerConfig struct {
	ID        string                 `json:"id"`
	Name      string                 `json:"name"`
	Type      string                 `json:"type"`
	Endpoint  string                 `json:"endpoint"`
	Config    map[string]interface{} `json:"config"`
	CreatedAt time.Time              `json:"created_at"`
}
// MCPServer represents a custom Model Context Protocol server
type MCPServer struct {
	ID          string    `json:"id"`
	TenantID    string    `json:"tenant_id"`
	Name        string    `json:"name"`
	Description string    `json:"description"`
	Endpoint    string    `json:"endpoint"`
	Protocol    string    `json:"protocol"`    // "websocket", "stdio", "http"
	Config      MCPConfig `json:"config"`
	Status      string    `json:"status"`      // "active", "inactive", "error"
	CreatedAt   time.Time `json:"created_at"`
	UpdatedAt   time.Time `json:"updated_at"`
}

// MCPConfig contains server-specific configuration
type MCPConfig struct {
	Authentication map[string]interface{} `json:"authentication"`
	Capabilities   []string               `json:"capabilities"`
	Tools          []MCPTool              `json:"tools"`
	Resources      []MCPResource          `json:"resources"`
	Settings       map[string]interface{} `json:"settings"`
}

// MCPTool represents a tool exposed by the MCP server
type MCPTool struct {
	Name        string                 `json:"name"`
	Description string                 `json:"description"`
	Parameters  map[string]interface{} `json:"parameters"`
	Handler     string                 `json:"handler"`
}

// MCPResource represents a resource exposed by the MCP server
type MCPResource struct {
	URI         string                 `json:"uri"`
	Name        string                 `json:"name"`
	Description string                 `json:"description"`
	MimeType    string                 `json:"mime_type"`
	Metadata    map[string]interface{} `json:"metadata"`
}

// MCPManager handles custom MCP server operations
type MCPManager struct {
	db          *sql.DB
	featureGate types.FeatureGate
}

// NewMCPManager creates a new MCP manager
func NewMCPManager(db *sql.DB, featureGate types.FeatureGate) *MCPManager {
	return &MCPManager{
		db:          db,
		featureGate: featureGate,
	}
}

// CreateMCPServer creates a new custom MCP server for a tenant
func (mm *MCPManager) CreateMCPServer(tenantID, name, description, endpoint, protocol string, config MCPConfig) (*MCPServer, error) {
	// Validate enterprise license for custom MCP servers
	if err := mm.featureGate.ValidateCustomMCP(); err != nil {
		return nil, err
	}

	serverID, err := generateServerID()
	if err != nil {
		return nil, fmt.Errorf("failed to generate server ID: %w", err)
	}

	server := &MCPServer{
		ID:          serverID,
		TenantID:    tenantID,
		Name:        name,
		Description: description,
		Endpoint:    endpoint,
		Protocol:    protocol,
		Config:      config,
		Status:      "inactive",
		CreatedAt:   time.Now(),
		UpdatedAt:   time.Now(),
	}

	if err := mm.storeMCPServer(server); err != nil {
		return nil, fmt.Errorf("failed to store MCP server: %w", err)
	}

	return server, nil
}

// GetMCPServer retrieves an MCP server by ID
func (mm *MCPManager) GetMCPServer(serverID string) (*MCPServer, error) {
	query := `
		SELECT id, tenant_id, name, description, endpoint, protocol, 
		       config, status, created_at, updated_at
		FROM mcp_servers WHERE id = ?
	`
	
	row := mm.db.QueryRow(query, serverID)
	
	server := &MCPServer{}
	var configJSON string
	
	err := row.Scan(
		&server.ID, &server.TenantID, &server.Name, &server.Description,
		&server.Endpoint, &server.Protocol, &configJSON, &server.Status,
		&server.CreatedAt, &server.UpdatedAt,
	)
	
	if err != nil {
		return nil, fmt.Errorf("MCP server not found: %w", err)
	}
	
	if err := json.Unmarshal([]byte(configJSON), &server.Config); err != nil {
		return nil, fmt.Errorf("failed to parse MCP config: %w", err)
	}
	
	return server, nil
}

// ListMCPServers returns all MCP servers for a tenant
func (mm *MCPManager) ListMCPServers(tenantID string) ([]*MCPServer, error) {
	query := `
		SELECT id, tenant_id, name, description, endpoint, protocol,
		       config, status, created_at, updated_at
		FROM mcp_servers WHERE tenant_id = ? ORDER BY created_at DESC
	`
	
	rows, err := mm.db.Query(query, tenantID)
	if err != nil {
		return nil, fmt.Errorf("failed to query MCP servers: %w", err)
	}
	defer rows.Close()
	
	var servers []*MCPServer
	for rows.Next() {
		server := &MCPServer{}
		var configJSON string
		
		err := rows.Scan(
			&server.ID, &server.TenantID, &server.Name, &server.Description,
			&server.Endpoint, &server.Protocol, &configJSON, &server.Status,
			&server.CreatedAt, &server.UpdatedAt,
		)
		if err != nil {
			return nil, fmt.Errorf("failed to scan MCP server: %w", err)
		}
		
		if err := json.Unmarshal([]byte(configJSON), &server.Config); err != nil {
			return nil, fmt.Errorf("failed to parse MCP config: %w", err)
		}
		
		servers = append(servers, server)
	}
	
	return servers, nil
}

// UpdateMCPServer updates an MCP server configuration
func (mm *MCPManager) UpdateMCPServer(serverID string, config MCPConfig) error {
	configJSON, err := json.Marshal(config)
	if err != nil {
		return fmt.Errorf("failed to marshal config: %w", err)
	}
	
	query := `
		UPDATE mcp_servers SET config = ?, updated_at = ? WHERE id = ?
	`
	
	_, err = mm.db.Exec(query, string(configJSON), time.Now(), serverID)
	if err != nil {
		return fmt.Errorf("failed to update MCP server: %w", err)
	}
	
	return nil
}

// SetMCPServerStatus updates the status of an MCP server
func (mm *MCPManager) SetMCPServerStatus(serverID, status string) error {
	query := `
		UPDATE mcp_servers SET status = ?, updated_at = ? WHERE id = ?
	`
	
	_, err := mm.db.Exec(query, status, time.Now(), serverID)
	if err != nil {
		return fmt.Errorf("failed to update MCP server status: %w", err)
	}
	
	return nil
}

// DeleteMCPServer removes an MCP server
func (mm *MCPManager) DeleteMCPServer(serverID string) error {
	_, err := mm.db.Exec("DELETE FROM mcp_servers WHERE id = ?", serverID)
	if err != nil {
		return fmt.Errorf("failed to delete MCP server: %w", err)
	}
	
	return nil
}

// DeployMCPServer activates an MCP server for use
func (mm *MCPManager) DeployMCPServer(serverID string) error {
	server, err := mm.GetMCPServer(serverID)
	if err != nil {
		return fmt.Errorf("server not found: %w", err)
	}
	
	// Convert to MCPServerConfig for deployment logic
	deployServer := &MCPServerConfig{
		ID:        server.ID,
		Name:      server.Name,
		Type:      server.Protocol, // Use protocol as type for simplicity
		Endpoint:  server.Endpoint,
		Config:    server.Config.Settings, // Use settings as config
		CreatedAt: server.CreatedAt,
	}
	
	// Validate configuration before deployment
	if err := mm.validateMCPConfig(deployServer.Config); err != nil {
		return fmt.Errorf("invalid MCP configuration: %w", err)
	}
	
	// Update status to deploying
	if err := mm.SetMCPServerStatus(serverID, "deploying"); err != nil {
		return fmt.Errorf("failed to update status: %w", err)
	}
	
	// Generate deployment configuration
	deployConfig, err := mm.generateDeploymentConfig(deployServer)
	if err != nil {
		return fmt.Errorf("failed to generate deployment config: %w", err)
	}
	
	// Deploy based on server type
	var deployErr error
	switch deployServer.Type {
	case "http", "jira":
		deployErr = mm.deployJiraServer(deployServer, deployConfig)
	case "websocket", "slack":
		deployErr = mm.deploySlackServer(deployServer, deployConfig)
	case "stdio", "github":
		deployErr = mm.deployGithubServer(deployServer, deployConfig)
	case "custom":
		deployErr = mm.deployCustomServer(deployServer, deployConfig)
	default:
		return fmt.Errorf("unsupported server type: %s", deployServer.Type)
	}
	
	if deployErr != nil {
		mm.SetMCPServerStatus(serverID, "failed")
		return fmt.Errorf("deployment failed: %w", deployErr)
	}
	
	// Health check with retry
	if err := mm.healthCheckWithRetry(deployServer.Endpoint, 30*time.Second); err != nil {
		mm.SetMCPServerStatus(serverID, "unhealthy")
		return fmt.Errorf("health check failed: %w", err)
	}
	
	// Mark as active
	if err := mm.SetMCPServerStatus(serverID, "active"); err != nil {
		return fmt.Errorf("failed to update final status: %w", err)
	}
	
	return nil
}

// CreateJiraIntegration creates a custom MCP server for Jira integration
func (mm *MCPManager) CreateJiraIntegration(tenantID, jiraURL, apiToken string) (*MCPServer, error) {
	// Validate enterprise license for custom integrations
	if err := mm.featureGate.ValidateCustomMCP(); err != nil {
		return nil, err
	}

	config := MCPConfig{
		Authentication: map[string]interface{}{
			"type":      "bearer",
			"token":     apiToken,
			"base_url":  jiraURL,
		},
		Capabilities: []string{"issues", "projects", "search"},
		Tools: []MCPTool{
			{
				Name:        "search_issues",
				Description: "Search Jira issues with JQL",
				Parameters: map[string]interface{}{
					"jql":      map[string]interface{}{"type": "string", "required": true},
					"fields":   map[string]interface{}{"type": "array", "required": false},
					"max_results": map[string]interface{}{"type": "number", "default": 50},
				},
				Handler: "jira.search_issues",
			},
			{
				Name:        "get_issue",
				Description: "Get detailed information about a Jira issue",
				Parameters: map[string]interface{}{
					"issue_key": map[string]interface{}{"type": "string", "required": true},
				},
				Handler: "jira.get_issue",
			},
		},
		Resources: []MCPResource{
			{
				URI:         fmt.Sprintf("jira://%s/issues", tenantID),
				Name:        "Jira Issues",
				Description: "Access to Jira issues and projects",
				MimeType:    "application/json",
			},
		},
		Settings: map[string]interface{}{
			"rate_limit": 100,
			"timeout":    30,
		},
	}
	
	return mm.CreateMCPServer(tenantID, "Jira Integration", "Custom Jira MCP server", 
		fmt.Sprintf("%s/rest/api/2", jiraURL), "http", config)
}

// CreateSlackIntegration creates a custom MCP server for Slack integration
func (mm *MCPManager) CreateSlackIntegration(tenantID, botToken, appToken string) (*MCPServer, error) {
	// Validate enterprise license for custom integrations
	if err := mm.featureGate.ValidateCustomMCP(); err != nil {
		return nil, err
	}

	config := MCPConfig{
		Authentication: map[string]interface{}{
			"bot_token": botToken,
			"app_token": appToken,
		},
		Capabilities: []string{"messages", "channels", "users"},
		Tools: []MCPTool{
			{
				Name:        "send_message",
				Description: "Send a message to a Slack channel",
				Parameters: map[string]interface{}{
					"channel": map[string]interface{}{"type": "string", "required": true},
					"text":    map[string]interface{}{"type": "string", "required": true},
				},
				Handler: "slack.send_message",
			},
			{
				Name:        "search_messages",
				Description: "Search Slack messages",
				Parameters: map[string]interface{}{
					"query": map[string]interface{}{"type": "string", "required": true},
					"sort":  map[string]interface{}{"type": "string", "default": "timestamp"},
				},
				Handler: "slack.search_messages",
			},
		},
		Resources: []MCPResource{
			{
				URI:         fmt.Sprintf("slack://%s/messages", tenantID),
				Name:        "Slack Messages",
				Description: "Access to Slack conversations",
				MimeType:    "application/json",
			},
		},
	}
	
	return mm.CreateMCPServer(tenantID, "Slack Integration", "Custom Slack MCP server",
		"wss://wss.slack.com/websocket", "websocket", config)
}

// storeMCPServer persists MCP server configuration to database
func (mm *MCPManager) storeMCPServer(server *MCPServer) error {
	configJSON, err := json.Marshal(server.Config)
	if err != nil {
		return fmt.Errorf("failed to marshal config: %w", err)
	}
	
	query := `
		INSERT INTO mcp_servers (
			id, tenant_id, name, description, endpoint, protocol,
			config, status, created_at, updated_at
		) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
	`
	
	_, err = mm.db.Exec(query,
		server.ID, server.TenantID, server.Name, server.Description,
		server.Endpoint, server.Protocol, string(configJSON), server.Status,
		server.CreatedAt, server.UpdatedAt,
	)
	
	if err != nil {
		return fmt.Errorf("failed to store MCP server: %w", err)
	}
	
	return nil
}

// generateServerID creates a unique server identifier
func generateServerID() (string, error) {
	bytes := make([]byte, 16)
	if _, err := rand.Read(bytes); err != nil {
		return "", err
	}
	return "mcp_" + hex.EncodeToString(bytes)[:16], nil
}

// validateMCPConfig validates MCP server configuration
func (mm *MCPManager) validateMCPConfig(config map[string]interface{}) error {
	if config == nil {
		return fmt.Errorf("configuration cannot be nil")
	}
	return nil // Basic validation for now
}

// generateDeploymentConfig creates deployment-specific configuration
func (mm *MCPManager) generateDeploymentConfig(server *MCPServerConfig) (map[string]interface{}, error) {
	config := make(map[string]interface{})
	
	// Base configuration
	config["server_id"] = server.ID
	config["server_name"] = server.Name
	config["server_type"] = server.Type
	config["endpoint"] = server.Endpoint
	config["created_at"] = server.CreatedAt
	
	// Parse port from endpoint
	if strings.Contains(server.Endpoint, ":") {
		parts := strings.Split(server.Endpoint, ":")
		if len(parts) > 2 {
			config["port"] = parts[2]
		}
	}
	
	// Environment variables
	config["env"] = map[string]string{
		"MCP_SERVER_ID":   server.ID,
		"MCP_SERVER_NAME": server.Name,
		"NODE_ENV":        "production",
	}
	
	if port, ok := config["port"].(string); ok {
		config["env"].(map[string]string)["MCP_PORT"] = port
	}
	
	// Merge user configuration
	for key, value := range server.Config {
		config[key] = value
	}
	
	return config, nil
}

// deployJiraServer deploys a Jira integration MCP server
func (mm *MCPManager) deployJiraServer(server *MCPServerConfig, config map[string]interface{}) error {
	// Create server directory
	serverDir := filepath.Join("./mcp_servers", server.ID)
	if err := os.MkdirAll(serverDir, 0755); err != nil {
		return fmt.Errorf("failed to create server directory: %w", err)
	}
	
	// Generate basic Jira MCP server code
	serverCode := mm.generateJiraMCPCode(config)
	packageJSON := mm.generatePackageJSON(server.Name, config)
	
	// Write server files
	files := map[string]string{
		"package.json": packageJSON,
		"index.js":     serverCode,
		"config.json":  mm.generateConfigJSON(config),
	}
	
	for filename, content := range files {
		filePath := filepath.Join(serverDir, filename)
		if err := os.WriteFile(filePath, []byte(content), 0644); err != nil {
			return fmt.Errorf("failed to write %s: %w", filename, err)
		}
	}
	
	// Install dependencies and start server
	return mm.startNodeServer(serverDir, config)
}

// deploySlackServer deploys a Slack bot MCP server
func (mm *MCPManager) deploySlackServer(server *MCPServerConfig, config map[string]interface{}) error {
	serverDir := filepath.Join("./mcp_servers", server.ID)
	if err := os.MkdirAll(serverDir, 0755); err != nil {
		return fmt.Errorf("failed to create server directory: %w", err)
	}
	
	serverCode := mm.generateSlackMCPCode(config)
	packageJSON := mm.generatePackageJSON(server.Name, config)
	
	files := map[string]string{
		"package.json": packageJSON,
		"index.js":     serverCode,
		"config.json":  mm.generateConfigJSON(config),
	}
	
	for filename, content := range files {
		filePath := filepath.Join(serverDir, filename)
		if err := os.WriteFile(filePath, []byte(content), 0644); err != nil {
			return fmt.Errorf("failed to write %s: %w", filename, err)
		}
	}
	
	return mm.startNodeServer(serverDir, config)
}

// deployGithubServer deploys a GitHub integration MCP server
func (mm *MCPManager) deployGithubServer(server *MCPServerConfig, config map[string]interface{}) error {
	return fmt.Errorf("GitHub MCP server deployment not yet implemented")
}

// deployCustomServer deploys a custom MCP server
func (mm *MCPManager) deployCustomServer(server *MCPServerConfig, config map[string]interface{}) error {
	return fmt.Errorf("Custom MCP server deployment not yet implemented")
}

// healthCheckWithRetry performs health check with exponential backoff
func (mm *MCPManager) healthCheckWithRetry(endpoint string, timeout time.Duration) error {
	start := time.Now()
	backoff := 1 * time.Second
	
	for time.Since(start) < timeout {
		if err := mm.healthCheck(endpoint); err == nil {
			return nil
		}
		
		time.Sleep(backoff)
		backoff = time.Duration(float64(backoff) * 1.5)
		if backoff > 10*time.Second {
			backoff = 10 * time.Second
		}
	}
	
	return fmt.Errorf("health check timeout after %v", timeout)
}

// healthCheck performs a simple HTTP health check
func (mm *MCPManager) healthCheck(endpoint string) error {
	client := &http.Client{Timeout: 5 * time.Second}
	resp, err := client.Get(endpoint + "/health")
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	
	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("health check returned status %d", resp.StatusCode)
	}
	
	return nil
}

// startNodeServer installs dependencies and starts a Node.js MCP server
func (mm *MCPManager) startNodeServer(serverDir string, config map[string]interface{}) error {
	// Install npm dependencies
	npmInstallCmd := exec.Command("npm", "install")
	npmInstallCmd.Dir = serverDir
	if err := npmInstallCmd.Run(); err != nil {
		return fmt.Errorf("npm install failed: %w", err)
	}
	
	// Start server in background
	startCmd := exec.Command("npm", "start")
	startCmd.Dir = serverDir
	
	// Set environment variables
	if env, ok := config["env"].(map[string]string); ok {
		for key, value := range env {
			startCmd.Env = append(startCmd.Env, fmt.Sprintf("%s=%s", key, value))
		}
	}
	
	if err := startCmd.Start(); err != nil {
		return fmt.Errorf("failed to start server: %w", err)
	}
	
	return nil
}

// generateJiraMCPCode generates basic Node.js code for Jira MCP server
func (mm *MCPManager) generateJiraMCPCode(config map[string]interface{}) string {
	return `const express = require('express');
const app = express();
const port = process.env.MCP_PORT || 3000;

app.use(express.json());

// Health check endpoint
app.get('/health', (req, res) => {
  res.json({ status: 'healthy', server: 'jira-mcp' });
});

// MCP endpoints
app.post('/mcp/tools/search_issues', (req, res) => {
  // TODO: Implement Jira issue search
  res.json({ message: 'Jira search not implemented' });
});

app.listen(port, () => {
  console.log('Jira MCP server running on port', port);
});`
}

// generateSlackMCPCode generates basic Node.js code for Slack MCP server
func (mm *MCPManager) generateSlackMCPCode(config map[string]interface{}) string {
	return `const express = require('express');
const app = express();
const port = process.env.MCP_PORT || 3000;

app.use(express.json());

// Health check endpoint
app.get('/health', (req, res) => {
  res.json({ status: 'healthy', server: 'slack-mcp' });
});

// MCP endpoints
app.post('/mcp/tools/send_message', (req, res) => {
  // TODO: Implement Slack message sending
  res.json({ message: 'Slack integration not implemented' });
});

app.listen(port, () => {
  console.log('Slack MCP server running on port', port);
});`
}

// generatePackageJSON generates package.json for Node.js MCP server
func (mm *MCPManager) generatePackageJSON(name string, config map[string]interface{}) string {
	return fmt.Sprintf(`{
  "name": "%s",
  "version": "1.0.0",
  "description": "Generated MCP server",
  "main": "index.js",
  "scripts": {
    "start": "node index.js"
  },
  "dependencies": {
    "express": "^4.18.0"
  }
}`, strings.ToLower(strings.ReplaceAll(name, " ", "-")))
}

// generateConfigJSON generates config.json for MCP server
func (mm *MCPManager) generateConfigJSON(config map[string]interface{}) string {
	configBytes, _ := json.MarshalIndent(config, "", "  ")
	return string(configBytes)
}

// InitMCPSchema creates the MCP servers table
func InitMCPSchema(db *sql.DB) error {
	schema := `
		CREATE TABLE IF NOT EXISTS mcp_servers (
			id TEXT PRIMARY KEY,
			tenant_id TEXT NOT NULL,
			name TEXT NOT NULL,
			description TEXT,
			endpoint TEXT NOT NULL,
			protocol TEXT NOT NULL,
			config TEXT NOT NULL,
			status TEXT DEFAULT 'inactive',
			created_at DATETIME NOT NULL,
			updated_at DATETIME NOT NULL,
			FOREIGN KEY (tenant_id) REFERENCES tenants(id)
		);
		
		CREATE INDEX IF NOT EXISTS idx_mcp_servers_tenant_id ON mcp_servers(tenant_id);
		CREATE INDEX IF NOT EXISTS idx_mcp_servers_status ON mcp_servers(status);
	`
	
	_, err := db.Exec(schema)
	if err != nil {
		return fmt.Errorf("failed to create MCP schema: %w", err)
	}
	
	return nil
}
