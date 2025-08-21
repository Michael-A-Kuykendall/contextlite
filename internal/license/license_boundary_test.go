package license

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

// TestRemainingZeroCoverage targets the last 2 functions with 0% coverage
func TestRemainingZeroCoverage(t *testing.T) {
	t.Run("ValidateTierLimits_AllErrorPaths", func(t *testing.T) {
		manager := NewLicenseManager()
		
		// Test Developer tier violations
		t.Run("Developer_ExceedsDocumentLimit", func(t *testing.T) {
			license := &License{
				Tier:         TierDeveloper,
				MaxDocuments: 20000, // Exceeds 10,000 limit
				MaxUsers:     1,
			}
			err := manager.validateTierLimits(license)
			assert.Error(t, err)
			assert.Contains(t, err.Error(), "developer tier limited to 10,000 documents")
		})
		
		t.Run("Developer_ExceedsUserLimit", func(t *testing.T) {
			license := &License{
				Tier:         TierDeveloper,
				MaxDocuments: 5000,
				MaxUsers:     5, // Exceeds 1 user limit
			}
			err := manager.validateTierLimits(license)
			assert.Error(t, err)
			assert.Contains(t, err.Error(), "developer tier limited to single user")
		})
		
		// Test Pro tier violations
		t.Run("Pro_TooFewDocuments", func(t *testing.T) {
			license := &License{
				Tier:         TierPro,
				MaxDocuments: 5000, // Below 10,001 minimum for Pro
				MaxUsers:     5,
			}
			err := manager.validateTierLimits(license)
			assert.Error(t, err)
			assert.Contains(t, err.Error(), "professional tier requires unlimited documents")
		})
		
		t.Run("Pro_ExceedsUserLimit", func(t *testing.T) {
			license := &License{
				Tier:         TierPro,
				MaxDocuments: 50000,
				MaxUsers:     25, // Exceeds 10 user limit for Pro
			}
			err := manager.validateTierLimits(license)
			assert.Error(t, err)
			assert.Contains(t, err.Error(), "professional tier limited to 10 users")
		})
		
		// Test Enterprise tier (should pass validation)
		t.Run("Enterprise_ValidLimits", func(t *testing.T) {
			license := &License{
				Tier:         TierEnterprise,
				MaxDocuments: 1000000,
				MaxUsers:     100,
			}
			err := manager.validateTierLimits(license)
			assert.NoError(t, err)
		})
		
		// Test edge cases
		t.Run("Pro_ExactLimits", func(t *testing.T) {
			license := &License{
				Tier:         TierPro,
				MaxDocuments: 10001, // Exact minimum
				MaxUsers:     10,    // Exact maximum
			}
			err := manager.validateTierLimits(license)
			assert.NoError(t, err)
		})
		
		t.Run("Developer_ExactLimits", func(t *testing.T) {
			license := &License{
				Tier:         TierDeveloper,
				MaxDocuments: 10000, // Exact maximum
				MaxUsers:     1,     // Exact maximum
			}
			err := manager.validateTierLimits(license)
			assert.NoError(t, err)
		})
		
		// Test unlimited documents for Pro (0 = unlimited)
		t.Run("Pro_UnlimitedDocuments", func(t *testing.T) {
			license := &License{
				Tier:         TierPro,
				MaxDocuments: 0, // 0 means unlimited
				MaxUsers:     5,
			}
			err := manager.validateTierLimits(license)
			assert.NoError(t, err)
		})
	})
	
	t.Run("GenerateInstallID_DirectCall", func(t *testing.T) {
		// Create a trial manager and force a call to generateInstallID
		manager := NewTrialManager()
		
		// Call generateInstallID directly through a method that uses it
		// We need to test the actual generation logic
		
		// Test 1: Basic format and validity tests
		id1 := manager.generateInstallID()
		
		// Test 2: Verify format and length  
		assert.Len(t, id1, 32, "Install ID should be 32 characters (16 bytes hex encoded)")
		
		// Test 3: Verify hex encoding
		assert.Regexp(t, "^[0-9a-f]{32}$", id1, "Install ID should be valid hex")
		
		// Test 4: Test with different hardware IDs (should be different)
		manager2 := &TrialManager{hwID: "different-hardware"}
		id2 := manager2.generateInstallID()
		
		// Should be different from original manager due to different hwID
		assert.NotEqual(t, id1, id2, "Different hardware should generate different IDs")
		assert.Len(t, id2, 32, "Different hardware ID should still be 32 chars")
		
		// Test 5: Test a few more unique hardware IDs
		manager3 := &TrialManager{hwID: "unique-hardware-3"}
		manager4 := &TrialManager{hwID: "unique-hardware-4"}
		id3 := manager3.generateInstallID()
		id4 := manager4.generateInstallID()
		
		// All different hardware should generate different IDs
		assert.NotEqual(t, id1, id3, "Hardware-1 vs Hardware-3 should be different")
		assert.NotEqual(t, id1, id4, "Hardware-1 vs Hardware-4 should be different")
		assert.NotEqual(t, id2, id3, "Hardware-2 vs Hardware-3 should be different")
		assert.NotEqual(t, id2, id4, "Hardware-2 vs Hardware-4 should be different")
		assert.NotEqual(t, id3, id4, "Hardware-3 vs Hardware-4 should be different")
	})
}
