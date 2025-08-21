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