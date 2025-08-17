package enterprise

import (
	"fmt"
	"time"
	"database/sql"
	"crypto/rand"
	"encoding/hex"
	"os"
	"path/filepath"
	"contextlite/internal/features"
)

// TenantConfig represents a multi-tenant workspace configuration
type TenantConfig struct {
	ID          string    `json:"id"`
	Name        string    `json:"name"`
	Domain      string    `json:"domain"`      // e.g., "acme-corp"
	OrgID       string    `json:"org_id"`     // Parent organization
	DatabaseURL string    `json:"database_url"`
	CreatedAt   time.Time `json:"created_at"`
	Settings    TenantSettings `json:"settings"`
}

// TenantSettings contains tenant-specific configuration
type TenantSettings struct {
	MaxUsers       int               `json:"max_users"`
	MaxDocuments   int               `json:"max_documents"`
	RetentionDays  int               `json:"retention_days"`
	AllowedDomains []string          `json:"allowed_domains"`
	SSOEnabled     bool              `json:"sso_enabled"`
	SSOProvider    string            `json:"sso_provider"`
	CustomMCP      bool              `json:"custom_mcp"`
	Analytics      bool              `json:"analytics"`
	Settings       map[string]interface{} `json:"settings,omitempty"` // Additional settings
}

// TenantManager handles multi-tenant operations
type TenantManager struct {
	db          *sql.DB
	featureGate *features.FeatureGate
}

// NewTenantManager creates a new tenant manager
func NewTenantManager(db *sql.DB, featureGate *features.FeatureGate) *TenantManager {
	return &TenantManager{
		db:          db,
		featureGate: featureGate,
	}
}

// CreateTenant creates a new isolated tenant workspace
func (tm *TenantManager) CreateTenant(name, domain, orgID string, settings TenantSettings) (*TenantConfig, error) {
	// Validate enterprise license for multi-tenant features
	if err := tm.featureGate.ValidateMultiTenant(); err != nil {
		return nil, err
	}

	tenantID, err := generateTenantID()
	if err != nil {
		return nil, fmt.Errorf("failed to generate tenant ID: %w", err)
	}

	// Create isolated database for tenant
	dbURL := fmt.Sprintf("contextlite_tenant_%s.db", tenantID)
	
	tenant := &TenantConfig{
		ID:          tenantID,
		Name:        name,
		Domain:      domain,
		OrgID:       orgID,
		DatabaseURL: dbURL,
		CreatedAt:   time.Now(),
		Settings:    settings,
	}

	// Initialize tenant database schema
	if err := tm.initTenantDatabase(tenant); err != nil {
		return nil, fmt.Errorf("failed to initialize tenant database: %w", err)
	}

	// Store tenant configuration
	if err := tm.storeTenantConfig(tenant); err != nil {
		return nil, fmt.Errorf("failed to store tenant config: %w", err)
	}

	return tenant, nil
}

// GetTenant retrieves tenant configuration by ID
func (tm *TenantManager) GetTenant(tenantID string) (*TenantConfig, error) {
	query := `
		SELECT id, name, domain, org_id, database_url, created_at,
		       max_users, max_documents, retention_days, sso_enabled, 
		       sso_provider, custom_mcp, analytics
		FROM tenants WHERE id = ?
	`
	
	row := tm.db.QueryRow(query, tenantID)
	
	tenant := &TenantConfig{}
	err := row.Scan(
		&tenant.ID, &tenant.Name, &tenant.Domain, &tenant.OrgID,
		&tenant.DatabaseURL, &tenant.CreatedAt,
		&tenant.Settings.MaxUsers, &tenant.Settings.MaxDocuments,
		&tenant.Settings.RetentionDays, &tenant.Settings.SSOEnabled,
		&tenant.Settings.SSOProvider, &tenant.Settings.CustomMCP,
		&tenant.Settings.Analytics,
	)
	
	if err != nil {
		return nil, fmt.Errorf("tenant not found: %w", err)
	}
	
	return tenant, nil
}

// GetTenantByDomain retrieves tenant by domain name
func (tm *TenantManager) GetTenantByDomain(domain string) (*TenantConfig, error) {
	query := `
		SELECT id, name, domain, org_id, database_url, created_at,
		       max_users, max_documents, retention_days, sso_enabled, 
		       sso_provider, custom_mcp, analytics
		FROM tenants WHERE domain = ?
	`
	
	row := tm.db.QueryRow(query, domain)
	
	tenant := &TenantConfig{}
	err := row.Scan(
		&tenant.ID, &tenant.Name, &tenant.Domain, &tenant.OrgID,
		&tenant.DatabaseURL, &tenant.CreatedAt,
		&tenant.Settings.MaxUsers, &tenant.Settings.MaxDocuments,
		&tenant.Settings.RetentionDays, &tenant.Settings.SSOEnabled,
		&tenant.Settings.SSOProvider, &tenant.Settings.CustomMCP,
		&tenant.Settings.Analytics,
	)
	
	if err != nil {
		return nil, fmt.Errorf("tenant not found for domain %s: %w", domain, err)
	}
	
	return tenant, nil
}

// ListTenants returns all tenants for an organization
func (tm *TenantManager) ListTenants(orgID string) ([]*TenantConfig, error) {
	query := `
		SELECT id, name, domain, org_id, database_url, created_at,
		       max_users, max_documents, retention_days, sso_enabled, 
		       sso_provider, custom_mcp, analytics
		FROM tenants WHERE org_id = ? ORDER BY created_at DESC
	`
	
	rows, err := tm.db.Query(query, orgID)
	if err != nil {
		return nil, fmt.Errorf("failed to query tenants: %w", err)
	}
	defer rows.Close()
	
	var tenants []*TenantConfig
	for rows.Next() {
		tenant := &TenantConfig{}
		err := rows.Scan(
			&tenant.ID, &tenant.Name, &tenant.Domain, &tenant.OrgID,
			&tenant.DatabaseURL, &tenant.CreatedAt,
			&tenant.Settings.MaxUsers, &tenant.Settings.MaxDocuments,
			&tenant.Settings.RetentionDays, &tenant.Settings.SSOEnabled,
			&tenant.Settings.SSOProvider, &tenant.Settings.CustomMCP,
			&tenant.Settings.Analytics,
		)
		if err != nil {
			return nil, fmt.Errorf("failed to scan tenant: %w", err)
		}
		tenants = append(tenants, tenant)
	}
	
	return tenants, nil
}

// UpdateTenantSettings updates tenant configuration
func (tm *TenantManager) UpdateTenantSettings(tenantID string, settings TenantSettings) error {
	query := `
		UPDATE tenants SET 
		max_users = ?, max_documents = ?, retention_days = ?,
		sso_enabled = ?, sso_provider = ?, custom_mcp = ?, analytics = ?
		WHERE id = ?
	`
	
	_, err := tm.db.Exec(query,
		settings.MaxUsers, settings.MaxDocuments, settings.RetentionDays,
		settings.SSOEnabled, settings.SSOProvider, settings.CustomMCP,
		settings.Analytics, tenantID,
	)
	
	if err != nil {
		return fmt.Errorf("failed to update tenant settings: %w", err)
	}
	
	return nil
}

// DeleteTenant removes a tenant and its data (careful!)
func (tm *TenantManager) DeleteTenant(tenantID string) error {
	// First get tenant info to clean up database file
	tenant, err := tm.GetTenant(tenantID)
	if err != nil {
		return fmt.Errorf("tenant not found: %w", err)
	}
	
	// Delete tenant configuration
	_, err = tm.db.Exec("DELETE FROM tenants WHERE id = ?", tenantID)
	if err != nil {
		return fmt.Errorf("failed to delete tenant config: %w", err)
	}
	
	// TODO: Delete tenant database file
	// os.Remove(tenant.DatabaseURL)
	
	return nil
}

// initTenantDatabase creates the database schema for a new tenant
func (tm *TenantManager) initTenantDatabase(tenant *TenantConfig) error {
	// Create directory if needed
	dbDir := filepath.Dir(tenant.DatabaseURL)
	if err := os.MkdirAll(dbDir, 0755); err != nil {
		return fmt.Errorf("failed to create database directory: %w", err)
	}
	
	// Open database connection
	db, err := sql.Open("sqlite", tenant.DatabaseURL)
	if err != nil {
		return fmt.Errorf("failed to open tenant database: %w", err)
	}
	defer db.Close()
	
	// Enable foreign keys and WAL mode for better performance
	pragmas := []string{
		"PRAGMA foreign_keys = ON",
		"PRAGMA journal_mode = WAL",
		"PRAGMA synchronous = NORMAL",
		"PRAGMA cache_size = 10000",
		"PRAGMA temp_store = MEMORY",
	}
	
	for _, pragma := range pragmas {
		if _, err := db.Exec(pragma); err != nil {
			return fmt.Errorf("failed to set pragma %s: %w", pragma, err)
		}
	}
	
	// Initialize ContextLite schema
	schema := `
	-- Documents table
	CREATE TABLE IF NOT EXISTS documents (
		id TEXT PRIMARY KEY,
		path TEXT NOT NULL,
		content TEXT NOT NULL,
		language TEXT,
		size_bytes INTEGER DEFAULT 0,
		created_at INTEGER DEFAULT (strftime('%s', 'now')),
		updated_at INTEGER DEFAULT (strftime('%s', 'now')),
		tenant_id TEXT NOT NULL
	);
	
	-- FTS5 virtual table for full-text search
	CREATE VIRTUAL TABLE IF NOT EXISTS documents_fts USING fts5(
		content,
		content='documents',
		content_rowid='rowid'
	);
	
	-- Triggers to keep FTS in sync
	CREATE TRIGGER IF NOT EXISTS documents_ai AFTER INSERT ON documents BEGIN
		INSERT INTO documents_fts(rowid, content) VALUES (new.rowid, new.content);
	END;
	
	CREATE TRIGGER IF NOT EXISTS documents_ad AFTER DELETE ON documents BEGIN
		INSERT INTO documents_fts(documents_fts, rowid, content) VALUES('delete', old.rowid, old.content);
	END;
	
	CREATE TRIGGER IF NOT EXISTS documents_au AFTER UPDATE ON documents BEGIN
		INSERT INTO documents_fts(documents_fts, rowid, content) VALUES('delete', old.rowid, old.content);
		INSERT INTO documents_fts(rowid, content) VALUES (new.rowid, new.content);
	END;
	
	-- Cache table for query results
	CREATE TABLE IF NOT EXISTS cache (
		cache_key TEXT PRIMARY KEY,
		query_hash TEXT NOT NULL,
		result_data TEXT NOT NULL,
		created_at INTEGER DEFAULT (strftime('%s', 'now')),
		hit_count INTEGER DEFAULT 0,
		last_hit INTEGER DEFAULT (strftime('%s', 'now')),
		tenant_id TEXT NOT NULL
	);
	
	-- Workspace weights for learning
	CREATE TABLE IF NOT EXISTS workspace_weights (
		workspace_path TEXT PRIMARY KEY,
		relevance_weight REAL DEFAULT 0.3,
		recency_weight REAL DEFAULT 0.2,
		entanglement_weight REAL DEFAULT 0.15,
		diversity_weight REAL DEFAULT 0.15,
		redundancy_penalty REAL DEFAULT 0.2,
		update_count INTEGER DEFAULT 0,
		last_updated TEXT,
		tenant_id TEXT NOT NULL
	);
	
	-- Tenant-specific configuration
	CREATE TABLE IF NOT EXISTS tenant_config (
		key TEXT PRIMARY KEY,
		value TEXT NOT NULL,
		updated_at INTEGER DEFAULT (strftime('%s', 'now'))
	);
	
	-- Indexes for performance
	CREATE INDEX IF NOT EXISTS idx_documents_path ON documents(path);
	CREATE INDEX IF NOT EXISTS idx_documents_tenant ON documents(tenant_id);
	CREATE INDEX IF NOT EXISTS idx_cache_tenant ON cache(tenant_id);
	CREATE INDEX IF NOT EXISTS idx_cache_created_at ON cache(created_at);
	CREATE INDEX IF NOT EXISTS idx_workspace_weights_tenant ON workspace_weights(tenant_id);
	`
	
	// Execute schema
	if _, err := db.Exec(schema); err != nil {
		return fmt.Errorf("failed to initialize schema: %w", err)
	}
	
	// Insert tenant configuration
	configStmts := []struct {
		key   string
		value interface{}
	}{
		{"tenant_id", tenant.ID},
		{"tenant_name", tenant.Name},
		{"created_at", time.Now().Unix()},
		{"max_documents", tenant.Settings.MaxDocuments},
		{"max_cache_entries", 10000},
		{"cache_ttl_hours", 24},
	}
	
	// Apply tenant-specific settings
	if tenant.Settings.Settings != nil {
		for key, value := range tenant.Settings.Settings {
			configStmts = append(configStmts, struct {
				key   string
				value interface{}
			}{key, value})
		}
	}
	
	insertConfigStmt := "INSERT OR REPLACE INTO tenant_config (key, value) VALUES (?, ?)"
	for _, config := range configStmts {
		valueStr := fmt.Sprintf("%v", config.value)
		if _, err := db.Exec(insertConfigStmt, config.key, valueStr); err != nil {
			return fmt.Errorf("failed to insert config %s: %w", config.key, err)
		}
	}
	
	return nil
}

// storeTenantConfig persists tenant configuration to main database
func (tm *TenantManager) storeTenantConfig(tenant *TenantConfig) error {
	query := `
		INSERT INTO tenants (
			id, name, domain, org_id, database_url, created_at,
			max_users, max_documents, retention_days, sso_enabled,
			sso_provider, custom_mcp, analytics
		) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
	`
	
	_, err := tm.db.Exec(query,
		tenant.ID, tenant.Name, tenant.Domain, tenant.OrgID,
		tenant.DatabaseURL, tenant.CreatedAt,
		tenant.Settings.MaxUsers, tenant.Settings.MaxDocuments,
		tenant.Settings.RetentionDays, tenant.Settings.SSOEnabled,
		tenant.Settings.SSOProvider, tenant.Settings.CustomMCP,
		tenant.Settings.Analytics,
	)
	
	if err != nil {
		return fmt.Errorf("failed to store tenant config: %w", err)
	}
	
	return nil
}

// generateTenantID creates a unique tenant identifier
func generateTenantID() (string, error) {
	bytes := make([]byte, 16)
	if _, err := rand.Read(bytes); err != nil {
		return "", err
	}
	return hex.EncodeToString(bytes), nil
}

// InitTenantSchema creates the tenants table in main database
func InitTenantSchema(db *sql.DB) error {
	schema := `
		CREATE TABLE IF NOT EXISTS tenants (
			id TEXT PRIMARY KEY,
			name TEXT NOT NULL,
			domain TEXT UNIQUE NOT NULL,
			org_id TEXT NOT NULL,
			database_url TEXT NOT NULL,
			created_at DATETIME NOT NULL,
			max_users INTEGER DEFAULT 100,
			max_documents INTEGER DEFAULT 1000000,
			retention_days INTEGER DEFAULT 365,
			sso_enabled BOOLEAN DEFAULT false,
			sso_provider TEXT DEFAULT '',
			custom_mcp BOOLEAN DEFAULT false,
			analytics BOOLEAN DEFAULT true
		);
		
		CREATE INDEX IF NOT EXISTS idx_tenants_org_id ON tenants(org_id);
		CREATE INDEX IF NOT EXISTS idx_tenants_domain ON tenants(domain);
	`
	
	_, err := db.Exec(schema)
	if err != nil {
		return fmt.Errorf("failed to create tenant schema: %w", err)
	}
	
	return nil
}
