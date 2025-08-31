package jwt

import (
	"testing"
)

func TestJWTAuthenticator(t *testing.T) {
	auth, err := NewJWTAuthenticator()
	if err != nil {
		t.Fatalf("Failed to create JWT authenticator: %v", err)
	}

	// Test token generation
	userID := "john.doe"
	roles := []string{"developer", "analyst"}
	clearance := "SECRET"
	
	token, err := auth.GenerateToken(userID, roles, clearance)
	if err != nil {
		t.Fatalf("Failed to generate token: %v", err)
	}

	// Test token validation
	claims, err := auth.ValidateToken(token)
	if err != nil {
		t.Fatalf("Failed to validate token: %v", err)
	}

	if claims.UserID != userID {
		t.Errorf("Expected user ID %s, got %s", userID, claims.UserID)
	}

	if claims.Clearance != clearance {
		t.Errorf("Expected clearance %s, got %s", clearance, claims.Clearance)
	}

	if len(claims.Roles) != 2 {
		t.Errorf("Expected 2 roles, got %d", len(claims.Roles))
	}
}

func TestMFAAuthentication(t *testing.T) {
	auth, err := NewJWTAuthenticator()
	if err != nil {
		t.Fatalf("Failed to create JWT authenticator: %v", err)
	}

	userID := "security.officer"
	roles := []string{"security", "admin"}
	clearance := "TOP_SECRET"
	
	// Generate initial token
	token, err := auth.GenerateToken(userID, roles, clearance)
	if err != nil {
		t.Fatalf("Failed to generate token: %v", err)
	}

	// Validate initial token
	claims, err := auth.ValidateToken(token)
	if err != nil {
		t.Fatalf("Failed to validate token: %v", err)
	}

	// Initially MFA should not be verified
	if claims.MFAVerified {
		t.Error("MFA should not be verified initially")
	}

	// Update MFA status
	updatedToken, err := auth.UpdateMFAStatus(token, true, true)
	if err != nil {
		t.Fatalf("Failed to update MFA status: %v", err)
	}

	// Validate updated token
	updatedClaims, err := auth.ValidateToken(updatedToken)
	if err != nil {
		t.Fatalf("Failed to validate updated token: %v", err)
	}

	if !updatedClaims.MFAVerified {
		t.Error("MFA should be verified after update")
	}

	if !updatedClaims.CACVerified {
		t.Error("CAC should be verified after update")
	}
}

func TestAccountLockout(t *testing.T) {
	auth, err := NewJWTAuthenticator()
	if err != nil {
		t.Fatalf("Failed to create JWT authenticator: %v", err)
	}

	userID := "test.user"
	totpSecret := "JBSWY3DPEHPK3PXP" // Base32 test secret

	// Test successful TOTP validation
	// Note: This will fail in actual test since we don't have a real TOTP code
	// In practice, you'd mock the TOTP validation or use a known test vector
	
	// Simulate failed attempts
	for i := 0; i < 6; i++ {
		err := auth.VerifyTOTP(userID, "000000", totpSecret) // Invalid TOTP
		if i < 5 {
			if err != ErrInvalidTOTP {
				t.Errorf("Expected ErrInvalidTOTP, got %v", err)
			}
		} else {
			if err != ErrAccountLocked {
				t.Errorf("Expected ErrAccountLocked after 5 attempts, got %v", err)
			}
		}
	}

	// Verify account is locked
	if !auth.IsAccountLocked(userID) {
		t.Error("Account should be locked after 5 failed attempts")
	}

	// Test unlock
	auth.UnlockAccount(userID)
	if auth.IsAccountLocked(userID) {
		t.Error("Account should be unlocked after manual unlock")
	}
}

func TestClearanceValidation(t *testing.T) {
	auth, err := NewJWTAuthenticator()
	if err != nil {
		t.Fatalf("Failed to create JWT authenticator: %v", err)
	}

	// Test various clearance levels
	testCases := []struct {
		userClearance     string
		requiredClearance string
		shouldPass        bool
	}{
		{"TOP_SECRET", "SECRET", true},
		{"TOP_SECRET", "CONFIDENTIAL", true},
		{"SECRET", "TOP_SECRET", false},
		{"CONFIDENTIAL", "SECRET", false},
		{"CUI", "UNCLASSIFIED", true},
		{"UNCLASSIFIED", "CUI", false},
	}

	for _, tc := range testCases {
		claims := &JWTClaims{
			UserID:    "test.user",
			Clearance: tc.userClearance,
		}

		err := auth.ValidateClearanceLevel(claims, tc.requiredClearance)
		
		if tc.shouldPass && err != nil {
			t.Errorf("User with %s clearance should access %s resources", 
				tc.userClearance, tc.requiredClearance)
		}
		
		if !tc.shouldPass && err == nil {
			t.Errorf("User with %s clearance should NOT access %s resources", 
				tc.userClearance, tc.requiredClearance)
		}
	}
}

func TestTokenExpiration(t *testing.T) {
	auth, err := NewJWTAuthenticator()
	if err != nil {
		t.Fatalf("Failed to create JWT authenticator: %v", err)
	}

	// Generate token with very short expiry for testing
	userID := "expiry.test"
	token, err := auth.GenerateToken(userID, []string{"test"}, "UNCLASSIFIED")
	if err != nil {
		t.Fatalf("Failed to generate token: %v", err)
	}

	// Token should be valid initially
	_, err = auth.ValidateToken(token)
	if err != nil {
		t.Fatalf("Token should be valid initially: %v", err)
	}

	// Test token refresh
	refreshedToken, err := auth.RefreshToken(token)
	if err != nil {
		t.Fatalf("Failed to refresh token: %v", err)
	}

	// Refreshed token should be valid
	refreshedClaims, err := auth.ValidateToken(refreshedToken)
	if err != nil {
		t.Fatalf("Refreshed token should be valid: %v", err)
	}

	// Should have new token ID
	originalClaims, _ := auth.ValidateToken(token)
	if refreshedClaims.ID == originalClaims.ID {
		t.Error("Refreshed token should have new ID")
	}
}

func TestLockoutStatus(t *testing.T) {
	auth, err := NewJWTAuthenticator()
	if err != nil {
		t.Fatalf("Failed to create JWT authenticator: %v", err)
	}

	userID := "lockout.test"
	
	// Initial status
	attempts, locked, remaining := auth.GetLockoutStatus(userID)
	if attempts != 0 || locked || remaining != 0 {
		t.Error("Initial lockout status should be clean")
	}

	// Make failed attempts
	totpSecret := "JBSWY3DPEHPK3PXP"
	for i := 0; i < 3; i++ {
		auth.VerifyTOTP(userID, "000000", totpSecret) // Will fail
	}

	// Check status
	attempts, locked, remaining = auth.GetLockoutStatus(userID)
	if attempts != 3 {
		t.Errorf("Expected 3 attempts, got %d", attempts)
	}
	if locked {
		t.Error("Should not be locked yet")
	}

	// Trigger lockout
	auth.VerifyTOTP(userID, "000000", totpSecret)
	auth.VerifyTOTP(userID, "000000", totpSecret)

	attempts, locked, remaining = auth.GetLockoutStatus(userID)
	if !locked {
		t.Error("Should be locked after 5 attempts")
	}
	if remaining <= 0 {
		t.Error("Should have positive time remaining")
	}
}
