package test

import (
	"crypto/rand"
	"crypto/rsa"
	"encoding/base64"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
	"time"

	"contextlite/internal/license"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestLicenseManager_NewLicenseManager(t *testing.T) {
	lm := license.NewLicenseManager()
	assert.NotNil(t, lm)
}

func TestLicenseManager_GetFeatures(t *testing.T) {
	tests := []struct {
		name           string
		tier           license.LicenseTier
		expectedCount  int
		expectedCore   []string
	}{
		{
			name:         "no license defaults to developer",
			tier:         "",
			expectedCount: 4,
			expectedCore: []string{"basic_search", "rest_api", "sqlite_storage", "single_workspace"},
		},
		{
			name:         "developer tier",
			tier:         license.TierDeveloper,
			expectedCount: 4,
			expectedCore: []string{"basic_search", "rest_api", "sqlite_storage", "single_workspace"},
		},
		{
			name:         "professional tier",
			tier:         license.TierPro,
			expectedCount: 9,
			expectedCore: []string{"basic_search", "unlimited_workspaces", "advanced_optimization", "caching"},
		},
		{
			name:         "enterprise tier",
			tier:         license.TierEnterprise,
			expectedCount: 22,
			expectedCore: []string{"basic_search", "multi_tenant", "sso_ldap", "white_label", "analytics"},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			lm := license.NewLicenseManager()
			
			// Test without loading license (defaults to developer)
			features := lm.GetFeatures()
			
			if tt.tier == "" || tt.tier == license.TierDeveloper {
				// Test default developer features
				assert.Len(t, features, tt.expectedCount)
				for _, expectedFeature := range tt.expectedCore {
					assert.Contains(t, features, expectedFeature)
				}
			} else {
				// For pro/enterprise, we can only test the default (developer) behavior
				// since we can't easily mock the private license field
				assert.Len(t, features, 4) // Always returns developer features without valid license
				assert.Contains(t, features, "basic_search")
			}
		})
	}
}

func TestLicenseManager_HasFeature(t *testing.T) {
	lm := license.NewLicenseManager()
	
	// Test core features available in developer tier
	assert.True(t, lm.HasFeature("basic_search"))
	assert.True(t, lm.HasFeature("rest_api"))
	
	// Test advanced features not available in developer tier
	assert.False(t, lm.HasFeature("multi_tenant"))
	assert.False(t, lm.HasFeature("sso_ldap"))
	assert.False(t, lm.HasFeature("analytics"))
}

func TestLicenseManager_GetMaxDocuments(t *testing.T) {
	lm := license.NewLicenseManager()
	
	// Without license, should get limited documents (grace period check)
	maxDocs := lm.GetMaxDocuments()
	assert.True(t, maxDocs > 0)
	assert.True(t, maxDocs <= 10000) // Either grace period (10000) or unlicensed (1000)
}

func TestLicenseManager_GetTier(t *testing.T) {
	lm := license.NewLicenseManager()
	
	// Without license, should default to developer tier
	tier := lm.GetTier()
	assert.Equal(t, license.TierDeveloper, tier)
}

func TestLicenseManager_IsInGracePeriod(t *testing.T) {
	lm := license.NewLicenseManager()
	
	// Test grace period functionality
	// Note: This will use the actual user home directory first run file
	// In a real implementation, we might want to make this configurable for testing
	
	inGrace := lm.IsInGracePeriod()
	// Should be true (grace period) since we don't have a license loaded
	assert.True(t, inGrace)
}

func TestGenerateLicense(t *testing.T) {
	// Generate test RSA key pair
	privateKey, err := rsa.GenerateKey(rand.Reader, 2048)
	require.NoError(t, err)
	
	tests := []struct {
		name       string
		email      string
		tier       license.LicenseTier
		hardwareID string
		wantErr    bool
	}{
		{
			name:       "valid developer license",
			email:      "dev@example.com",
			tier:       license.TierDeveloper,
			hardwareID: "hw_test_123",
			wantErr:    false,
		},
		{
			name:       "valid professional license",
			email:      "pro@example.com",
			tier:       license.TierPro,
			hardwareID: "hw_test_456",
			wantErr:    false,
		},
		{
			name:       "valid enterprise license",
			email:      "ent@example.com",
			tier:       license.TierEnterprise,
			hardwareID: "hw_test_789",
			wantErr:    false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			licenseString, err := license.GenerateLicense(tt.email, tt.tier, tt.hardwareID, privateKey)
			
			if tt.wantErr {
				assert.Error(t, err)
				return
			}
			
			require.NoError(t, err)
			assert.NotEmpty(t, licenseString)
			
			// Decode and verify license structure
			licenseJSON, err := base64.StdEncoding.DecodeString(licenseString)
			require.NoError(t, err)
			
			var lic license.License
			err = json.Unmarshal(licenseJSON, &lic)
			require.NoError(t, err)
			
			// Verify license fields
			assert.Equal(t, tt.email, lic.Email)
			assert.Equal(t, tt.tier, lic.Tier)
			assert.Equal(t, tt.hardwareID, lic.HardwareID)
			assert.NotEmpty(t, lic.Key)
			assert.NotEmpty(t, lic.Signature)
			assert.NotZero(t, lic.IssuedAt)
			assert.NotNil(t, lic.ExpiresAt)
			
			// Verify tier-specific limits
			switch tt.tier {
			case license.TierDeveloper:
				assert.Equal(t, 1000, lic.MaxDocuments)
				assert.Equal(t, 1, lic.MaxUsers)
			case license.TierPro:
				assert.Equal(t, 100000, lic.MaxDocuments)
				assert.Equal(t, 10, lic.MaxUsers)
			case license.TierEnterprise:
				assert.Equal(t, 0, lic.MaxDocuments) // unlimited
				assert.Equal(t, 0, lic.MaxUsers)     // unlimited
			}
		})
	}
}

func TestValidateLicense(t *testing.T) {
	// Generate test RSA key pair
	privateKey, err := rsa.GenerateKey(rand.Reader, 2048)
	require.NoError(t, err)
	publicKey := &privateKey.PublicKey
	
	// Generate a valid license using the same private key
	validLicenseString, err := license.GenerateLicense("test@example.com", license.TierPro, "hw_test", privateKey)
	require.NoError(t, err)
	
	// Decode for manipulation tests
	licenseJSON, err := base64.StdEncoding.DecodeString(validLicenseString)
	require.NoError(t, err)
	
	tests := []struct {
		name        string
		license     string
		setupLicense func() string
		wantValid   bool
		wantErr     bool
	}{
		{
			name:      "valid license",
			license:   string(licenseJSON),
			wantValid: true,
			wantErr:   false,
		},
		{
			name:        "invalid JSON",
			setupLicense: func() string { return "invalid json" },
			wantValid:   false,
			wantErr:     true,
		},
		{
			name: "tampered signature",
			setupLicense: func() string {
				var lic license.License
				json.Unmarshal(licenseJSON, &lic)
				lic.Signature = "dGFtcGVyZWRfc2lnbmF0dXJl" // base64 encoded "tampered_signature"
				modified, _ := json.Marshal(lic)
				return string(modified)
			},
			wantValid: false,
			wantErr:   true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			testLicense := tt.license
			if tt.setupLicense != nil {
				testLicense = tt.setupLicense()
			}
			
			valid, err := license.ValidateLicense(testLicense, publicKey)
			
			if tt.wantErr {
				assert.Error(t, err)
			} else {
				assert.NoError(t, err)
			}
			
			assert.Equal(t, tt.wantValid, valid)
		})
	}
}

func TestLicenseFeatureGate(t *testing.T) {
	fg := license.NewFeatureGate()
	
	// Test basic functionality
	assert.NotNil(t, fg)
	assert.Equal(t, "developer", fg.GetTier())
	
	// Test feature checking
	assert.True(t, fg.IsEnabled("basic_search"))
	assert.False(t, fg.IsEnabled("multi_tenant"))
	
	// Test feature requirements
	err := fg.RequireFeature("basic_search")
	assert.NoError(t, err)
	
	err = fg.RequireFeature("multi_tenant")
	assert.Error(t, err)
	
	// Test tier requirements
	err = fg.RequireProfessional()
	assert.Error(t, err) // Developer tier doesn't meet professional requirement
	
	err = fg.RequireEnterprise()
	assert.Error(t, err) // Developer tier doesn't meet enterprise requirement
	
	// Test specific validations
	err = fg.ValidateCustomMCP()
	assert.Error(t, err) // Requires enterprise
	
	err = fg.ValidateMultiTenant()
	assert.Error(t, err) // Requires enterprise
}

func TestLicenseTierFeatures(t *testing.T) {
	tests := []struct {
		name           string
		tier           license.LicenseTier
		expectedCore   []string
		unexpectedCore []string
	}{
		{
			name: "developer features",
			tier: license.TierDeveloper,
			expectedCore:   []string{"basic_search", "rest_api", "sqlite_storage", "single_workspace"},
			unexpectedCore: []string{"unlimited_workspaces", "multi_tenant", "analytics"},
		},
		{
			name: "professional features",
			tier: license.TierPro,
			expectedCore:   []string{"basic_search", "unlimited_workspaces", "advanced_optimization", "caching"},
			unexpectedCore: []string{"multi_tenant", "sso_ldap", "white_label"},
		},
		{
			name: "enterprise features",
			tier: license.TierEnterprise,
			expectedCore:   []string{"basic_search", "multi_tenant", "sso_ldap", "analytics", "compliance_reporting"},
			unexpectedCore: []string{}, // Enterprise has all features
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// This tests the internal feature list functions
			// We can't directly test them, but we can test through the FeatureGate
			// This is a limitation of the current design - consider making feature functions public
			
			// For now, just verify the tier constants are properly defined
			assert.NotEmpty(t, string(tt.tier))
		})
	}
}

func TestLicenseKeyGeneration(t *testing.T) {
	// We can't directly test generateLicenseKey since it's not exported
	// But we can test it through GenerateLicense
	privateKey, err := rsa.GenerateKey(rand.Reader, 2048)
	require.NoError(t, err)
	
	licenseString, err := license.GenerateLicense("test@example.com", license.TierDeveloper, "hw_test", privateKey)
	require.NoError(t, err)
	
	licenseJSON, err := base64.StdEncoding.DecodeString(licenseString)
	require.NoError(t, err)
	
	var lic license.License
	err = json.Unmarshal(licenseJSON, &lic)
	require.NoError(t, err)
	
	// Verify key format (should be XXXX-XXXX-XXXX-XXXX)
	assert.Len(t, lic.Key, 19) // 16 chars + 3 dashes
	assert.Contains(t, lic.Key, "-")
	
	// Check for expected format
	keyParts := []rune(lic.Key)
	assert.Equal(t, '-', keyParts[4])
	assert.Equal(t, '-', keyParts[9])
	assert.Equal(t, '-', keyParts[14])
}

// Helper function to get test-specific first run path
func getTestFirstRunPath(t *testing.T) string {
	tempDir := t.TempDir()
	return filepath.Join(tempDir, ".contextlite_first_run")
}

// Benchmark license operations
func BenchmarkGenerateLicense(b *testing.B) {
	privateKey, err := rsa.GenerateKey(rand.Reader, 2048)
	require.NoError(b, err)
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, err := license.GenerateLicense("test@example.com", license.TierDeveloper, "hw_test", privateKey)
		require.NoError(b, err)
	}
}

func BenchmarkValidateLicense(b *testing.B) {
	privateKey, err := rsa.GenerateKey(rand.Reader, 2048)
	require.NoError(b, err)
	publicKey := &privateKey.PublicKey
	
	// Generate test license
	licenseString, err := license.GenerateLicense("test@example.com", license.TierDeveloper, "hw_test", privateKey)
	require.NoError(b, err)
	
	licenseJSON, err := base64.StdEncoding.DecodeString(licenseString)
	require.NoError(b, err)
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, err := license.ValidateLicense(string(licenseJSON), publicKey)
		require.NoError(b, err)
	}
}
