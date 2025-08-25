package license

import (
	"testing"
)

// TestEasyTargets_verifySignature - Target 88.9% → 100%
func TestEasyTargets_verifySignature(t *testing.T) {
	lm := NewLicenseManager()

	// TARGET: Various base64 decoding errors
	t.Run("InvalidBase64Formats", func(t *testing.T) {
		testCases := []struct {
			name      string
			signature string
		}{
			{"EmptySignature", ""},
			{"InvalidBase64Chars", "invalid!@#$%^&*()"},
			{"PartialBase64", "abc="},
			{"WrongPadding", "YWJjZA==extra"},
			{"NonBase64", "hello world"},
			{"OnlyWhitespace", "   "},
			{"SpecialChars", "signature_with_underscores_and-dashes"},
		}

		for _, tc := range testCases {
			t.Run(tc.name, func(t *testing.T) {
				license := &License{
					Key:       "TEST-KEY",
					Email:     "test@example.com",
					Tier:      TierDeveloper,
					Signature: tc.signature,
				}

				err := lm.verifySignature(license)
				if err != nil {
					t.Logf("✅ %s: Hit base64 decode error: %v", tc.name, err)
				} else {
					t.Errorf("%s: Expected base64 decode error", tc.name)
				}
			})
		}
	})

	// TARGET: RSA verification failures with valid base64 but invalid signatures
	t.Run("ValidBase64InvalidSignatures", func(t *testing.T) {
		testCases := []struct {
			name      string
			signature string
		}{
			{"ShortSignature", "YWJj"},                                      // "abc" in base64
			{"LongButInvalid", "VGhpcyBpcyBhIGxvbmcgYnV0IGludmFsaWQgc2lnbmF0dXJl"}, // Long but invalid
			{"EmptyBytes", ""},                                             // Empty
			{"RandomBytes", "cmFuZG9tIGJ5dGVzIGZvciBzaWduYXR1cmUgdGVzdGluZw=="}, // Random bytes
			{"WrongLength", "dGVzdA=="},                                    // "test" - too short for RSA
		}

		for _, tc := range testCases {
			t.Run(tc.name, func(t *testing.T) {
				license := &License{
					Key:       "RSA-TEST-KEY",
					Email:     "rsa@example.com", 
					Tier:      TierDeveloper,
					Signature: tc.signature,
				}

				err := lm.verifySignature(license)
				if err != nil {
					t.Logf("✅ %s: Hit RSA verification error: %v", tc.name, err)
				} else {
					t.Errorf("%s: Expected RSA verification error", tc.name)
				}
			})
		}
	})

	// TARGET: Payload creation edge cases
	t.Run("PayloadEdgeCases", func(t *testing.T) {
		// Test with extreme values that might affect payload construction
		license := &License{
			Key:          "EXTREME-TEST-KEY-WITH-VERY-LONG-NAME-THAT-MIGHT-AFFECT-HASHING",
			Email:        "extremelylongemailaddressthatmightcausehashingissues@verylongdomainnamethatmightcauseproblems.com",
			Tier:         TierEnterprise,
			MaxDocuments: 999999999,
			MaxUsers:     999999999,
			HardwareID:   "hardware-id-with-special-chars-!@#$%^&*()_+-=[]{}|;:,.<>?",
			Signature:    "aW52YWxpZCBzaWduYXR1cmUgZm9yIGV4dHJlbWUgcGF5bG9hZA==",
		}

		err := lm.verifySignature(license)
		if err != nil {
			t.Logf("✅ Extreme payload: Hit verification error: %v", err)
		} else {
			t.Error("Expected verification error with extreme payload")
		}
	})
}

// TestEasyTargets_getPublicKey - Target 75% → 100%
func TestEasyTargets_getPublicKey(t *testing.T) {
	// TARGET: Multiple calls to getPublicKey to exercise different paths
	t.Run("MultipleCallsCoverage", func(t *testing.T) {
		// Call getPublicKey multiple times to ensure all code paths are covered
		for i := 0; i < 10; i++ {
			key := getPublicKey()
			if key == nil {
				t.Errorf("getPublicKey returned nil on call %d", i)
			} else {
				t.Logf("✅ Call %d: getPublicKey returned valid key (size: %d bits)", i, key.N.BitLen())
			}
		}
	})

	// TARGET: Verify the key is actually usable
	t.Run("PublicKeyUsability", func(t *testing.T) {
		key := getPublicKey()
		
		// Verify the key has expected properties
		if key.N == nil {
			t.Error("Public key N is nil")
		}
		if key.E == 0 {
			t.Error("Public key E is zero")
		}

		// Test that we can use the key (this exercises the key initialization paths)
		t.Logf("✅ Public key properties: N bit length=%d, E=%d", key.N.BitLen(), key.E)
	})

	// TARGET: Creating multiple LicenseManagers to exercise getPublicKey path
	t.Run("MultipleLicenseManagers", func(t *testing.T) {
		// Create multiple license managers, each will call getPublicKey
		for i := 0; i < 5; i++ {
			lm := NewLicenseManager()
			if lm.publicKey == nil {
				t.Errorf("LicenseManager %d has nil publicKey", i)
			} else {
				t.Logf("✅ LicenseManager %d: publicKey initialized", i)
			}
		}
	})
}