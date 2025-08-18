package license_test

import (
	"crypto/rand"
	"crypto/rsa"
	"encoding/base64"
	"encoding/json"
	"testing"

	"contextlite/internal/license"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestLicenseManager_NewLicenseManager(t *testing.T) {
	lm := license.NewLicenseManager()
	assert.NotNil(t, lm)
}

func TestLicenseManager_GetFeatures(t *testing.T) {
	lm := license.NewLicenseManager()
	
	// Without license, should default to developer features
	features := lm.GetFeatures()
	assert.Len(t, features, 4)
	assert.Contains(t, features, "basic_search")
	assert.Contains(t, features, "rest_api")
	assert.Contains(t, features, "sqlite_storage")
	assert.Contains(t, features, "single_workspace")
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
	tests := []struct {
		name        string
		setupLicense func() string
		wantValid   bool
		wantErr     bool
	}{
		{
			name:        "invalid JSON",
			setupLicense: func() string { return "invalid json" },
			wantValid:   false,
			wantErr:     true,
		},
		{
			name: "valid JSON structure but invalid signature",
			setupLicense: func() string {
				// Create a license with invalid signature but valid structure
				lic := license.License{
					Key:          "TEST-1234-5678-9ABC",
					Email:        "test@example.com",
					Tier:         license.TierDeveloper,
					MaxDocuments: 1000,
					MaxUsers:     1,
					Signature:    "invalid_signature",
				}
				licenseJSON, _ := json.Marshal(lic)
				return string(licenseJSON)
			},
			wantValid: false,
			wantErr:   true,
		},
	}

	// Create a dummy public key for testing
	privateKey, err := rsa.GenerateKey(rand.Reader, 2048)
	require.NoError(t, err)
	publicKey := &privateKey.PublicKey

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			testLicense := tt.setupLicense()
			
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
