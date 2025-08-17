package enterprise

import (
	"fmt"
	"time"
	"database/sql"
	"crypto/rand"
	"encoding/hex"
	"github.com/Michael-A-Kuykendall/contextlite/internal/features"
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
	MaxUsers       int    `json:"max_users"`
	MaxDocuments   int    `json:"max_documents"`
	RetentionDays  int    `json:"retention_days"`
	AllowedDomains []string `json:"allowed_domains"`
	SSOEnabled     bool   `json:"sso_enabled"`
	SSOProvider    string `json:"sso_provider"`
	CustomMCP      bool   `json:"custom_mcp"`
	Analytics      bool   `json:"analytics"`
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
	// TODO: Create isolated SQLite database for tenant
	// Initialize with ContextLite schema
	// Apply tenant-specific settings
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
