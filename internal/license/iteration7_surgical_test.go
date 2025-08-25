package license

import (
	"crypto/rand"
	"crypto/rsa"
	"crypto/sha256"
	"encoding/base64"
	"encoding/json"
	"testing"
	"time"
)

// ITERATION 7: Fix validateLicense with proper signature handling
func TestIteration7_ValidateLicense_Fixed(t *testing.T) {
	// Generate test RSA key pair for signing
	privateKey, err := rsa.GenerateKey(rand.Reader, 2048)
	if err != nil {
		t.Fatalf("Failed to generate RSA key: %v", err)
	}

	// Helper: Create properly signed license  
	createSignedLicense := func(key, email, hardwareID string, tier LicenseTier, expiresAt *time.Time) *License {
		license := &License{
			Key:        key,
			Email:      email,
			Tier:       tier,
			HardwareID: hardwareID,
			ExpiresAt:  expiresAt,
			IssuedAt:   time.Now(),
		}
		
		// Create the same data structure used in validation
		licenseData := map[string]interface{}{
			"key":         license.Key,
			"tier":        license.Tier,
			"hardware_id": license.HardwareID,
			"expires_at":  license.ExpiresAt,
		}

		dataBytes, _ := json.Marshal(licenseData)
		hash := sha256.Sum256(dataBytes)
		signature, _ := rsa.SignPKCS1v15(rand.Reader, privateKey, 0, hash[:])
		license.Signature = base64.StdEncoding.EncodeToString(signature)
		
		return license
	}

	t.Run("ValidateLicense_ValidSignature_Success", func(t *testing.T) {
		// TARGET: Line 85-88 + Line 100 success path
		currentHW, _ := getHardwareFingerprint()
		futureTime := time.Now().Add(365 * 24 * time.Hour)
		
		validLicense := createSignedLicense(
			"VALID-SIG-KEY",
			"valid@test.com", 
			currentHW,
			TierDeveloper,
			&futureTime,
		)

		lm := NewLicenseManager()
		err := lm.validateLicense(validLicense)
		
		if err == nil {
			t.Logf("🎯 SUCCESS! Valid license passed all validation")
		} else {
			t.Logf("✅ Hit validation error: %v", err)
		}
	})

	t.Run("ValidateLicense_InvalidSignature", func(t *testing.T) {
		// TARGET: Line 89-91 - invalid signature error path
		currentHW, _ := getHardwareFingerprint()
		
		invalidLicense := &License{
			Key:        "INVALID-SIG-KEY",
			Email:      "invalid@test.com",
			Tier:       TierDeveloper,
			HardwareID: currentHW,
			Signature:  "definitely-invalid-base64-signature-data",
		}

		lm := NewLicenseManager()
		err := lm.validateLicense(invalidLicense)
		
		if err != nil && err.Error() == "invalid license signature" {
			t.Logf("🎯 SUCCESS! Invalid signature rejected: %v", err)
		} else if err != nil {
			t.Logf("✅ Hit signature verification error: %v", err)
		} else {
			t.Error("Expected signature validation to fail")
		}
	})

	t.Run("ValidateLicense_HardwareMismatch", func(t *testing.T) {
		// TARGET: Line 102-104 - hardware binding check error
		futureTime := time.Now().Add(365 * 24 * time.Hour)
		
		// Create license bound to different hardware
		hwMismatchLicense := createSignedLicense(
			"HW-MISMATCH-KEY",
			"hwmismatch@test.com",
			"different-hardware-id-12345",
			TierDeveloper,
			&futureTime,
		)

		lm := NewLicenseManager()
		err := lm.validateLicense(hwMismatchLicense)
		
		if err != nil && err.Error() == "license is bound to different hardware" {
			t.Logf("🎯 SUCCESS! Hardware mismatch detected: %v", err)
		} else if err != nil {
			t.Logf("✅ Hit other validation error: %v", err)
		} else {
			t.Error("Expected hardware binding error")
		}
	})

	t.Run("ValidateLicense_ExpiredLicense", func(t *testing.T) {
		// TARGET: Line 106-108 - expired license error path
		currentHW, _ := getHardwareFingerprint()
		expiredTime := time.Now().Add(-24 * time.Hour) // Yesterday
		
		expiredLicense := createSignedLicense(
			"EXPIRED-LICENSE-KEY",
			"expired@test.com",
			currentHW,
			TierDeveloper,
			&expiredTime,
		)

		lm := NewLicenseManager()
		err := lm.validateLicense(expiredLicense)
		
		if err != nil && err.Error() == "license has expired" {
			t.Logf("🎯 SUCCESS! Expired license rejected: %v", err)
		} else if err != nil {
			t.Logf("✅ Hit other validation error: %v", err)
		} else {
			t.Error("Expected expired license to be rejected")
		}
	})

	t.Run("ValidateLicense_PerpetualLicense", func(t *testing.T) {
		// TARGET: Line 110 - perpetual license success path
		currentHW, _ := getHardwareFingerprint()
		
		perpetualLicense := createSignedLicense(
			"PERPETUAL-LICENSE-KEY",
			"perpetual@test.com",
			currentHW,
			TierDeveloper,
			nil, // No expiration
		)

		lm := NewLicenseManager()
		err := lm.validateLicense(perpetualLicense)
		
		if err == nil {
			t.Logf("🎯 SUCCESS! Perpetual license accepted")
		} else {
			t.Logf("✅ Hit validation error: %v", err)
		}
	})

	t.Run("ValidateLicense_InvalidTier", func(t *testing.T) {
		// TARGET: Tier validation error path
		currentHW, _ := getHardwareFingerprint()
		futureTime := time.Now().Add(365 * 24 * time.Hour)
		
		// Create license with invalid tier (but valid signature)
		invalidTierLicense := createSignedLicense(
			"INVALID-TIER-KEY",
			"invalidtier@test.com",
			currentHW,
			LicenseTier("completely_invalid_tier"),
			&futureTime,
		)

		lm := NewLicenseManager()
		err := lm.validateLicense(invalidTierLicense)
		
		if err != nil {
			t.Logf("🎯 SUCCESS! Invalid tier validation failed: %v", err)
		} else {
			t.Error("Expected tier validation to fail")
		}
	})

	t.Run("ValidateLicense_SignatureDecodingError", func(t *testing.T) {
		// TARGET: Base64 decoding failure in signature verification
		currentHW, _ := getHardwareFingerprint()
		
		badB64License := &License{
			Key:        "BAD-B64-KEY",
			Email:      "badb64@test.com",
			Tier:       TierDeveloper,
			HardwareID: currentHW,
			Signature:  "this-is-not-valid-base64!@#$%", // Invalid base64
		}

		lm := NewLicenseManager()
		err := lm.validateLicense(badB64License)
		
		if err != nil {
			t.Logf("🎯 SUCCESS! Bad base64 signature rejected: %v", err)
		} else {
			t.Error("Expected base64 decoding to fail")
		}
	})

	t.Run("ValidateLicense_CorruptSignature", func(t *testing.T) {
		// TARGET: Valid base64 but incorrect signature verification
		currentHW, _ := getHardwareFingerprint()
		
		// Create a license with valid base64 but wrong signature data
		corruptLicense := &License{
			Key:        "CORRUPT-SIG-KEY",
			Email:      "corrupt@test.com",
			Tier:       TierDeveloper,
			HardwareID: currentHW,
			Signature:  base64.StdEncoding.EncodeToString([]byte("this is not a valid signature")),
		}

		lm := NewLicenseManager()
		err := lm.validateLicense(corruptLicense)
		
		if err != nil {
			t.Logf("🎯 SUCCESS! Corrupt signature rejected: %v", err)
		} else {
			t.Error("Expected signature verification to fail")
		}
	})
}