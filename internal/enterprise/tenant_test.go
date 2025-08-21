package enterprise

import (
	"database/sql"
	"fmt"
	"testing"
	"time"
)

// mockFeatureGate provides a test implementation of types.FeatureGate
type mockFeatureGate struct {
	features map[string]bool
	tier     string
}

func newMockFeatureGate(tier string) *mockFeatureGate {
	return &mockFeatureGate{
		features: map[string]bool{
			"enterprise": tier == "Enterprise",
			"professional": tier == "Professional" || tier == "Enterprise",
			"custom_mcp": tier == "Enterprise",
			"multi_tenant": tier == "Enterprise",
		},
		tier: tier,
	}
}

func (m *mockFeatureGate) IsEnabled(feature string) bool {
	return m.features[feature]
}

func (m *mockFeatureGate) RequireFeature(feature string) error {
	if m.IsEnabled(feature) {
		return nil
	}
	return fmt.Errorf("feature %s not available", feature)
}

func (m *mockFeatureGate) RequireProfessional() error {
	if m.IsEnabled("professional") {
		return nil
	}
	return fmt.Errorf("professional license required")
}

func (m *mockFeatureGate) RequireEnterprise() error {
	if m.IsEnabled("enterprise") {
		return nil
	}
	return fmt.Errorf("enterprise license required")
}

func (m *mockFeatureGate) GetTier() string {
	return m.tier
}

func (m *mockFeatureGate) ValidateCustomMCP() error {
	return m.RequireFeature("custom_mcp")
}

func (m *mockFeatureGate) ValidateMultiTenant() error {
	return m.RequireFeature("multi_tenant")
}

func TestTenantConfig_Fields(t *testing.T) {
	now := time.Now()
	settings := TenantSettings{
		MaxUsers:       100,
		MaxDocuments:   10000,
		RetentionDays:  90,
		AllowedDomains: []string{"example.com", "test.org"},
		SSOEnabled:     true,
		SSOProvider:    "okta",
		CustomMCP:      true,
		Analytics:      false,
		Settings:       map[string]interface{}{"debug": true},
	}

	config := TenantConfig{
		ID:          "tenant-123",
		Name:        "Acme Corporation",
		Domain:      "acme-corp",
		OrgID:       "org-456",
		DatabaseURL: "sqlite:///tmp/tenant-123.db",
		CreatedAt:   now,
		Settings:    settings,
	}

	if config.ID != "tenant-123" {
		t.Errorf("Expected ID to be 'tenant-123', got %s", config.ID)
	}
	if config.Name != "Acme Corporation" {
		t.Errorf("Expected Name to be 'Acme Corporation', got %s", config.Name)
	}
	if config.Domain != "acme-corp" {
		t.Errorf("Expected Domain to be 'acme-corp', got %s", config.Domain)
	}
	if config.OrgID != "org-456" {
		t.Errorf("Expected OrgID to be 'org-456', got %s", config.OrgID)
	}
	if config.DatabaseURL != "sqlite:///tmp/tenant-123.db" {
		t.Errorf("Expected DatabaseURL to be 'sqlite:///tmp/tenant-123.db', got %s", config.DatabaseURL)
	}
	if config.CreatedAt != now {
		t.Errorf("Expected CreatedAt to be %v, got %v", now, config.CreatedAt)
	}
	if config.Settings.MaxUsers != 100 {
		t.Errorf("Expected MaxUsers to be 100, got %d", config.Settings.MaxUsers)
	}
}

func TestTenantSettings_Fields(t *testing.T) {
	settings := TenantSettings{
		MaxUsers:       50,
		MaxDocuments:   5000,
		RetentionDays:  30,
		AllowedDomains: []string{"company.com"},
		SSOEnabled:     false,
		SSOProvider:    "",
		CustomMCP:      false,
		Analytics:      true,
		Settings: map[string]interface{}{
			"theme":    "dark",
			"language": "en",
			"timezone": "UTC",
		},
	}

	if settings.MaxUsers != 50 {
		t.Errorf("Expected MaxUsers to be 50, got %d", settings.MaxUsers)
	}
	if settings.MaxDocuments != 5000 {
		t.Errorf("Expected MaxDocuments to be 5000, got %d", settings.MaxDocuments)
	}
	if settings.RetentionDays != 30 {
		t.Errorf("Expected RetentionDays to be 30, got %d", settings.RetentionDays)
	}
	if len(settings.AllowedDomains) != 1 {
		t.Errorf("Expected 1 allowed domain, got %d", len(settings.AllowedDomains))
	}
	if settings.AllowedDomains[0] != "company.com" {
		t.Errorf("Expected first domain to be 'company.com', got %s", settings.AllowedDomains[0])
	}
	if settings.SSOEnabled {
		t.Error("Expected SSOEnabled to be false")
	}
	if settings.SSOProvider != "" {
		t.Errorf("Expected empty SSOProvider, got %s", settings.SSOProvider)
	}
	if settings.CustomMCP {
		t.Error("Expected CustomMCP to be false")
	}
	if !settings.Analytics {
		t.Error("Expected Analytics to be true")
	}
	if settings.Settings["theme"] != "dark" {
		t.Errorf("Expected theme to be 'dark', got %v", settings.Settings["theme"])
	}
}

func TestNewTenantManager(t *testing.T) {
	// Create a mock database (nil for testing)
	var db *sql.DB
	featureGate := newMockFeatureGate("Enterprise")

	manager := NewTenantManager(db, featureGate)

	if manager == nil {
		t.Fatal("Expected TenantManager to be created")
	}
	if manager.db != db {
		t.Error("Expected db to be set correctly")
	}
	if manager.featureGate != featureGate {
		t.Error("Expected featureGate to be set correctly")
	}
}

func TestMockFeatureGate(t *testing.T) {
	// Test Enterprise tier
	enterpriseGate := newMockFeatureGate("Enterprise")

	if !enterpriseGate.IsEnabled("enterprise") {
		t.Error("Expected enterprise feature to be enabled for Enterprise tier")
	}
	if !enterpriseGate.IsEnabled("professional") {
		t.Error("Expected professional feature to be enabled for Enterprise tier")
	}
	if !enterpriseGate.IsEnabled("custom_mcp") {
		t.Error("Expected custom_mcp feature to be enabled for Enterprise tier")
	}
	if !enterpriseGate.IsEnabled("multi_tenant") {
		t.Error("Expected multi_tenant feature to be enabled for Enterprise tier")
	}
	
	if enterpriseGate.GetTier() != "Enterprise" {
		t.Errorf("Expected tier to be 'Enterprise', got %s", enterpriseGate.GetTier())
	}

	// Test Professional tier
	professionalGate := newMockFeatureGate("Professional")

	if professionalGate.IsEnabled("enterprise") {
		t.Error("Expected enterprise feature to be disabled for Professional tier")
	}
	if !professionalGate.IsEnabled("professional") {
		t.Error("Expected professional feature to be enabled for Professional tier")
	}
	if professionalGate.IsEnabled("custom_mcp") {
		t.Error("Expected custom_mcp feature to be disabled for Professional tier")
	}

	// Test Basic tier
	basicGate := newMockFeatureGate("Basic")

	if basicGate.IsEnabled("enterprise") {
		t.Error("Expected enterprise feature to be disabled for Basic tier")
	}
	if basicGate.IsEnabled("professional") {
		t.Error("Expected professional feature to be disabled for Basic tier")
	}
	if basicGate.IsEnabled("custom_mcp") {
		t.Error("Expected custom_mcp feature to be disabled for Basic tier")
	}

	// Test require methods
	if err := enterpriseGate.RequireEnterprise(); err != nil {
		t.Errorf("Expected RequireEnterprise to succeed for Enterprise tier, got error: %v", err)
	}
	if err := enterpriseGate.RequireProfessional(); err != nil {
		t.Errorf("Expected RequireProfessional to succeed for Enterprise tier, got error: %v", err)
	}
	if err := enterpriseGate.ValidateCustomMCP(); err != nil {
		t.Errorf("Expected ValidateCustomMCP to succeed for Enterprise tier, got error: %v", err)
	}
	if err := enterpriseGate.ValidateMultiTenant(); err != nil {
		t.Errorf("Expected ValidateMultiTenant to succeed for Enterprise tier, got error: %v", err)
	}

	// Test failure cases
	if err := basicGate.RequireEnterprise(); err == nil {
		t.Error("Expected RequireEnterprise to fail for Basic tier")
	}
	if err := basicGate.RequireProfessional(); err == nil {
		t.Error("Expected RequireProfessional to fail for Basic tier")
	}
	if err := basicGate.ValidateCustomMCP(); err == nil {
		t.Error("Expected ValidateCustomMCP to fail for Basic tier")
	}
}

func TestGenerateTenantID(t *testing.T) {
	id1, err := generateTenantID()
	if err != nil {
		t.Fatalf("Failed to generate tenant ID: %v", err)
	}
	
	if len(id1) != 32 { // 16 bytes = 32 hex chars
		t.Errorf("Expected tenant ID length to be 32, got %d", len(id1))
	}
	
	// Generate another ID to ensure uniqueness
	id2, err := generateTenantID()
	if err != nil {
		t.Fatalf("Failed to generate second tenant ID: %v", err)
	}
	
	if id1 == id2 {
		t.Error("Expected different tenant IDs, got duplicate")
	}
}

func TestInitTenantSchema(t *testing.T) {
	// Use in-memory database for testing
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("Failed to create in-memory database: %v", err)
	}
	defer db.Close()
	
	// Test successful schema creation
	err = InitTenantSchema(db)
	if err != nil {
		t.Fatalf("Failed to initialize tenant schema: %v", err)
	}
	
	// Verify table was created
	var count int
	err = db.QueryRow("SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='tenants'").Scan(&count)
	if err != nil {
		t.Fatalf("Failed to query table existence: %v", err)
	}
	if count != 1 {
		t.Errorf("Expected 1 tenants table, found %d", count)
	}
	
	// Test calling InitTenantSchema twice (should not error)
	err = InitTenantSchema(db)
	if err != nil {
		t.Errorf("Second call to InitTenantSchema should succeed: %v", err)
	}
}

func TestTenantManager_CreateTenant(t *testing.T) {
	// Create test database
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("Failed to create database: %v", err)
	}
	defer db.Close()
	
	// Initialize schema
	if err := InitTenantSchema(db); err != nil {
		t.Fatalf("Failed to initialize schema: %v", err)
	}
	
	// Test with Enterprise license (should succeed)
	enterpriseGate := newMockFeatureGate("Enterprise")
	manager := NewTenantManager(db, enterpriseGate)
	
	settings := TenantSettings{
		MaxUsers:       50,
		MaxDocuments:   5000,
		RetentionDays:  30,
		AllowedDomains: []string{"test.com"},
		SSOEnabled:     false,
		CustomMCP:      false,
		Analytics:      true,
	}
	
	tenant, err := manager.CreateTenant("Test Corp", "test-corp", "org-123", settings)
	if err != nil {
		t.Fatalf("Failed to create tenant: %v", err)
	}
	
	if tenant == nil {
		t.Fatal("Expected tenant to be created")
	}
	if tenant.Name != "Test Corp" {
		t.Errorf("Expected name 'Test Corp', got %s", tenant.Name)
	}
	if tenant.Domain != "test-corp" {
		t.Errorf("Expected domain 'test-corp', got %s", tenant.Domain)
	}
	if tenant.OrgID != "org-123" {
		t.Errorf("Expected org ID 'org-123', got %s", tenant.OrgID)
	}
	
	// Test with Basic license (should fail)
	basicGate := newMockFeatureGate("Basic")
	basicManager := NewTenantManager(db, basicGate)
	
	_, err = basicManager.CreateTenant("Basic Corp", "basic-corp", "org-456", settings)
	if err == nil {
		t.Error("Expected CreateTenant to fail with Basic license")
	}
}

func TestTenantManager_GetTenant(t *testing.T) {
	// Create test database and schema
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("Failed to create database: %v", err)
	}
	defer db.Close()
	
	if err := InitTenantSchema(db); err != nil {
		t.Fatalf("Failed to initialize schema: %v", err)
	}
	
	enterpriseGate := newMockFeatureGate("Enterprise")
	manager := NewTenantManager(db, enterpriseGate)
	
	// Create a tenant first
	settings := TenantSettings{MaxUsers: 100}
	tenant, err := manager.CreateTenant("Test Corp", "test-corp", "org-123", settings)
	if err != nil {
		t.Fatalf("Failed to create tenant: %v", err)
	}
	
	// Test retrieving the tenant
	retrieved, err := manager.GetTenant(tenant.ID)
	if err != nil {
		t.Fatalf("Failed to get tenant: %v", err)
	}
	
	if retrieved.ID != tenant.ID {
		t.Errorf("Expected ID %s, got %s", tenant.ID, retrieved.ID)
	}
	if retrieved.Name != tenant.Name {
		t.Errorf("Expected name %s, got %s", tenant.Name, retrieved.Name)
	}
	
	// Test getting non-existent tenant
	_, err = manager.GetTenant("non-existent")
	if err == nil {
		t.Error("Expected error when getting non-existent tenant")
	}
}

func TestTenantManager_GetTenantByDomain(t *testing.T) {
	// Create test database and schema
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("Failed to create database: %v", err)
	}
	defer db.Close()
	
	if err := InitTenantSchema(db); err != nil {
		t.Fatalf("Failed to initialize schema: %v", err)
	}
	
	enterpriseGate := newMockFeatureGate("Enterprise")
	manager := NewTenantManager(db, enterpriseGate)
	
	// Create a tenant first
	settings := TenantSettings{MaxUsers: 100}
	tenant, err := manager.CreateTenant("Test Corp", "test-corp", "org-123", settings)
	if err != nil {
		t.Fatalf("Failed to create tenant: %v", err)
	}
	
	// Test retrieving by domain
	retrieved, err := manager.GetTenantByDomain("test-corp")
	if err != nil {
		t.Fatalf("Failed to get tenant by domain: %v", err)
	}
	
	if retrieved.ID != tenant.ID {
		t.Errorf("Expected ID %s, got %s", tenant.ID, retrieved.ID)
	}
	
	// Test getting non-existent domain
	_, err = manager.GetTenantByDomain("non-existent")
	if err == nil {
		t.Error("Expected error when getting tenant by non-existent domain")
	}
}

func TestTenantManager_ListTenants(t *testing.T) {
	// Create test database and schema
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("Failed to create database: %v", err)
	}
	defer db.Close()
	
	if err := InitTenantSchema(db); err != nil {
		t.Fatalf("Failed to initialize schema: %v", err)
	}
	
	enterpriseGate := newMockFeatureGate("Enterprise")
	manager := NewTenantManager(db, enterpriseGate)
	
	// Create multiple tenants in same org
	settings := TenantSettings{MaxUsers: 100}
	tenant1, err := manager.CreateTenant("Corp 1", "corp1", "org-123", settings)
	if err != nil {
		t.Fatalf("Failed to create tenant 1: %v", err)
	}
	
	tenant2, err := manager.CreateTenant("Corp 2", "corp2", "org-123", settings)
	if err != nil {
		t.Fatalf("Failed to create tenant 2: %v", err)
	}
	
	// Create tenant in different org
	_, err = manager.CreateTenant("Other Corp", "other", "org-456", settings)
	if err != nil {
		t.Fatalf("Failed to create other tenant: %v", err)
	}
	
	// Test listing tenants for org-123
	tenants, err := manager.ListTenants("org-123")
	if err != nil {
		t.Fatalf("Failed to list tenants: %v", err)
	}
	
	if len(tenants) != 2 {
		t.Errorf("Expected 2 tenants for org-123, got %d", len(tenants))
	}
	
	// Verify tenant IDs are present
	foundTenant1, foundTenant2 := false, false
	for _, tenant := range tenants {
		if tenant.ID == tenant1.ID {
			foundTenant1 = true
		}
		if tenant.ID == tenant2.ID {
			foundTenant2 = true
		}
	}
	if !foundTenant1 || !foundTenant2 {
		t.Error("Expected to find both created tenants in list")
	}
	
	// Test listing tenants for different org
	otherTenants, err := manager.ListTenants("org-456")
	if err != nil {
		t.Fatalf("Failed to list other tenants: %v", err)
	}
	
	if len(otherTenants) != 1 {
		t.Errorf("Expected 1 tenant for org-456, got %d", len(otherTenants))
	}
	
	// Test listing for non-existent org
	emptyTenants, err := manager.ListTenants("non-existent")
	if err != nil {
		t.Fatalf("Failed to list tenants for non-existent org: %v", err)
	}
	if len(emptyTenants) != 0 {
		t.Errorf("Expected 0 tenants for non-existent org, got %d", len(emptyTenants))
	}
}

func TestTenantManager_UpdateTenantSettings(t *testing.T) {
	// Create test database and schema
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("Failed to create database: %v", err)
	}
	defer db.Close()
	
	if err := InitTenantSchema(db); err != nil {
		t.Fatalf("Failed to initialize schema: %v", err)
	}
	
	enterpriseGate := newMockFeatureGate("Enterprise")
	manager := NewTenantManager(db, enterpriseGate)
	
	// Create a tenant first
	originalSettings := TenantSettings{
		MaxUsers:     50,
		MaxDocuments: 1000,
		SSOEnabled:   false,
		Analytics:    false,
	}
	tenant, err := manager.CreateTenant("Test Corp", "test-corp", "org-123", originalSettings)
	if err != nil {
		t.Fatalf("Failed to create tenant: %v", err)
	}
	
	// Update settings
	updatedSettings := TenantSettings{
		MaxUsers:     100,
		MaxDocuments: 5000,
		SSOEnabled:   true,
		SSOProvider:  "okta",
		Analytics:    true,
		CustomMCP:    true,
	}
	
	err = manager.UpdateTenantSettings(tenant.ID, updatedSettings)
	if err != nil {
		t.Fatalf("Failed to update tenant settings: %v", err)
	}
	
	// Verify settings were updated
	retrieved, err := manager.GetTenant(tenant.ID)
	if err != nil {
		t.Fatalf("Failed to retrieve updated tenant: %v", err)
	}
	
	if retrieved.Settings.MaxUsers != 100 {
		t.Errorf("Expected MaxUsers 100, got %d", retrieved.Settings.MaxUsers)
	}
	if retrieved.Settings.MaxDocuments != 5000 {
		t.Errorf("Expected MaxDocuments 5000, got %d", retrieved.Settings.MaxDocuments)
	}
	if !retrieved.Settings.SSOEnabled {
		t.Error("Expected SSO to be enabled")
	}
	if retrieved.Settings.SSOProvider != "okta" {
		t.Errorf("Expected SSO provider 'okta', got %s", retrieved.Settings.SSOProvider)
	}
	if !retrieved.Settings.Analytics {
		t.Error("Expected Analytics to be enabled")
	}
	if !retrieved.Settings.CustomMCP {
		t.Error("Expected CustomMCP to be enabled")
	}
}

func TestTenantManager_DeleteTenant(t *testing.T) {
	// Create test database and schema
	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("Failed to create database: %v", err)
	}
	defer db.Close()
	
	if err := InitTenantSchema(db); err != nil {
		t.Fatalf("Failed to initialize schema: %v", err)
	}
	
	enterpriseGate := newMockFeatureGate("Enterprise")
	manager := NewTenantManager(db, enterpriseGate)
	
	// Create a tenant first
	settings := TenantSettings{MaxUsers: 100}
	tenant, err := manager.CreateTenant("Test Corp", "test-corp", "org-123", settings)
	if err != nil {
		t.Fatalf("Failed to create tenant: %v", err)
	}
	
	// Verify tenant exists
	_, err = manager.GetTenant(tenant.ID)
	if err != nil {
		t.Fatalf("Tenant should exist before deletion: %v", err)
	}
	
	// Delete tenant
	err = manager.DeleteTenant(tenant.ID)
	if err != nil {
		t.Fatalf("Failed to delete tenant: %v", err)
	}
	
	// Verify tenant no longer exists
	_, err = manager.GetTenant(tenant.ID)
	if err == nil {
		t.Error("Expected error when getting deleted tenant")
	}
	
	// Test deleting non-existent tenant
	err = manager.DeleteTenant("non-existent")
	if err == nil {
		t.Error("Expected error when deleting non-existent tenant")
	}
}