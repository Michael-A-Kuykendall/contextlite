package enterprise

import (
	"fmt"
	"time"
	"database/sql"
	"encoding/json"
	"crypto/rand"
	"encoding/hex"
	"github.com/Michael-A-Kuykendall/contextlite/internal/features"
)

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
	featureGate *features.FeatureGate
}

// NewMCPManager creates a new MCP manager
func NewMCPManager(db *sql.DB, featureGate *features.FeatureGate) *MCPManager {
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
	
	// TODO: Implement actual deployment logic
	// - Validate server configuration
	// - Start server process/container
	// - Register with MCP registry
	// - Health check
	
	return mm.SetMCPServerStatus(serverID, "active")
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
