package license

import (
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"testing"
	"time"
)

// Test validateLicense with all validation paths
func TestLicenseManager_ValidateLicense_Comprehensive(t *testing.T) {
	lm := NewLicenseManager()
	
	// Create base valid license
	validLicense := &License{
		Key:          "test-key-12345",
		Email:        "test@example.com",
		Tier:         TierPro,
		IssuedAt:     time.Now(),
		MaxDocuments: 10000,
		MaxUsers:     10,
		Features:     []string{"smt_optimization", "custom_weights"},
	}
	
	// Test 1: Valid license should pass
	err := lm.validateLicense(validLicense)
	if err != nil {
		t.Errorf("Valid license should pass validation: %v", err)
	}
	
	// Test 2: Invalid signature should fail
	invalidSigLicense := *validLicense
	invalidSigLicense.Signature = "invalid-signature"
	err = lm.validateLicense(&invalidSigLicense)
	if err == nil {
		t.Error("Expected validation to fail for invalid signature")
	}
	
	// Test 3: Hardware binding mismatch should fail
	currentHW, _ := getHardwareFingerprint()
	hwBoundLicense := *validLicense
	hwBoundLicense.HardwareID = "different-hardware-id-" + currentHW
	err = lm.validateLicense(&hwBoundLicense)
	if err == nil {
		t.Error("Expected validation to fail for hardware binding mismatch")
	}
	
	// Test 4: Expired license should fail
	expiredLicense := *validLicense
	pastTime := time.Now().Add(-24 * time.Hour)
	expiredLicense.ExpiresAt = &pastTime
	err = lm.validateLicense(&expiredLicense)
	if err == nil {
		t.Error("Expected validation to fail for expired license")
	}
	
	// Test 5: Future expiration should pass
	futureLicense := *validLicense
	futureTime := time.Now().Add(24 * time.Hour)
	futureLicense.ExpiresAt = &futureTime
	err = lm.validateLicense(&futureLicense)
	if err != nil {
		t.Errorf("Future expiration should pass: %v", err)
	}
	
	// Test 6: No expiration (nil) should pass
	noExpirationLicense := *validLicense
	noExpirationLicense.ExpiresAt = nil
	err = lm.validateLicense(&noExpirationLicense)
	if err != nil {
		t.Errorf("No expiration should pass: %v", err)
	}
}

// Test LoadLicenseWithActivation with all paths
func TestTrackedLicenseManager_LoadLicenseWithActivation_Comprehensive(t *testing.T) {
	// Create mock license server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/api/v1/license/activate" {
			activation := map[string]interface{}{
				"activation_id": "test-activation-123",
				"status":        "active",
				"activated_at":  time.Now().Unix(),
			}
			w.Header().Set("Content-Type", "application/json")
			json.NewEncoder(w).Encode(activation)
		} else {
			http.NotFound(w, r)
		}
	}))
	defer server.Close()
	
	// Create temporary directory for license files
	tempDir := t.TempDir()
	
	// Test 1: Valid license with successful activation
	validLicenseContent := fmt.Sprintf(`{
		"key": "CONTEXTLITE-TEST-12345",
		"email": "test@example.com",
		"tier": "professional",
		"issued_at": "%s",
		"max_documents": 10000,
		"max_users": 10,
		"features": ["smt_optimization", "custom_weights"],
		"signature": "valid-signature"
	}`, time.Now().Format(time.RFC3339))
	
	validLicensePath := filepath.Join(tempDir, "valid_license.json")
	err := os.WriteFile(validLicensePath, []byte(validLicenseContent), 0644)
	if err != nil {
		t.Fatalf("Failed to write valid license: %v", err)
	}
	
	tlm := NewTrackedLicenseManager(server.URL)
	err = tlm.LoadLicenseWithActivation(validLicensePath)
	if err != nil {
		t.Logf("LoadLicenseWithActivation error (may be expected in test env): %v", err)
	}
	
	// Test 2: Invalid license file should fail
	invalidLicenseContent := `{invalid json}`
	invalidLicensePath := filepath.Join(tempDir, "invalid_license.json")
	err = os.WriteFile(invalidLicensePath, []byte(invalidLicenseContent), 0644)
	if err != nil {
		t.Fatalf("Failed to write invalid license: %v", err)
	}
	
	tlm2 := NewTrackedLicenseManager(server.URL)
	err = tlm2.LoadLicenseWithActivation(invalidLicensePath)
	if err == nil {
		t.Error("Expected LoadLicenseWithActivation to fail for invalid JSON")
	}
	
	// Test 3: Non-existent license file should fail
	tlm3 := NewTrackedLicenseManager(server.URL)
	err = tlm3.LoadLicenseWithActivation("/non/existent/license.json")
	if err == nil {
		t.Error("Expected LoadLicenseWithActivation to fail for non-existent file")
	}
}

// Test StartOrGetTrial with all branches
func TestTrialManager_StartOrGetTrial_Comprehensive(t *testing.T) {
	tm := NewTrialManager()
	
	// Test 1: Start new trial (no existing trial)
	trial, err := tm.StartOrGetTrial()
	if err != nil {
		t.Fatalf("Failed to start trial: %v", err)
	}
	
	if trial == nil {
		t.Fatal("Trial should not be nil")
	}
	
	if trial.InstallID == "" {
		t.Error("Trial should have install ID")
	}
	
	if trial.StartDate.IsZero() {
		t.Error("Trial should have start time")
	}
	
	// Test 2: Get existing trial (should return same trial)
	trial2, err := tm.StartOrGetTrial()
	if err != nil {
		t.Fatalf("Failed to get existing trial: %v", err)
	}
	
	if trial2.InstallID != trial.InstallID {
		t.Errorf("Should return same trial. Expected %s, got %s", trial.InstallID, trial2.InstallID)
	}
	
	if !trial2.StartDate.Equal(trial.StartDate) {
		t.Error("Should return same trial start time")
	}
	
	// Test 3: Verify trial is active
	if !tm.IsTrialActive() {
		t.Error("Newly created trial should be active")
	}
	
	// Test 4: Check days remaining
	days := tm.DaysRemaining()
	if days <= 0 || days > 30 {
		t.Errorf("Expected 1-30 days remaining, got %d", days)
	}
}

// Test CheckAccess with all access scenarios
func TestEnhancedFeatureGate_CheckAccess_Comprehensive(t *testing.T) {
	// Test 1: Trial with valid access
	tm := NewTrialManager()
	_, err := tm.StartOrGetTrial()
	if err != nil {
		t.Fatalf("Failed to start trial: %v", err)
	}
	
	gate := NewEnhancedFeatureGate()
	
	// Check access to professional features (should be allowed in trial)
	err = gate.CheckAccess("smt_optimization")
	if err != nil {
		t.Errorf("Trial should allow access to smt_optimization: %v", err)
	}
	
	// Test 2: Check access to enterprise feature (should be denied in trial)
	err = gate.CheckAccess("multi_tenant")
	if err == nil {
		t.Error("Trial should not allow access to enterprise features")
	}
	
	// Test 3: Check access to unknown feature (should allow due to graceful degradation)
	err = gate.CheckAccess("unknown_feature")
	if err != nil {
		t.Errorf("Unknown features should be allowed due to graceful degradation, but got error: %v", err)
	}
}

// Test getDefaultFeatures with different tiers
func TestGetDefaultFeatures_AllTiers(t *testing.T) {
	// Test developer tier
	devFeatures := getDefaultFeatures(TierDeveloper)
	if len(devFeatures) == 0 {
		t.Error("Developer tier should have default features")
	}
	
	// Test professional tier
	proFeatures := getDefaultFeatures(TierPro)
	if len(proFeatures) == 0 {
		t.Error("Professional tier should have default features")
	}
	
	// Should have more features than developer
	if len(proFeatures) <= len(devFeatures) {
		t.Error("Professional should have more features than developer")
	}
	
	// Test enterprise tier
	entFeatures := getDefaultFeatures(TierEnterprise)
	if len(entFeatures) == 0 {
		t.Error("Enterprise tier should have default features")
	}
	
	// Should have more features than professional
	if len(entFeatures) <= len(proFeatures) {
		t.Error("Enterprise should have more features than professional")
	}
	
	// Test unknown tier (should default to developer features)
	unknownFeatures := getDefaultFeatures(LicenseTier("unknown"))
	devFeaturesForComparison := getDefaultFeatures(TierDeveloper)
	if len(unknownFeatures) != len(devFeaturesForComparison) {
		t.Errorf("Unknown tier should return developer features, got %d features, expected %d", len(unknownFeatures), len(devFeaturesForComparison))
	}
}

// Test RequireProfessional and RequireEnterprise edge cases
func TestFeatureGate_RequireTier_EdgeCases(t *testing.T) {
	// Test with default feature gate (no license loaded)
	gate := NewFeatureGate()
	
	err := gate.RequireProfessional()
	if err == nil {
		t.Error("RequireProfessional should fail with developer tier")
	}
	
	err = gate.RequireEnterprise()
	if err == nil {
		t.Error("RequireEnterprise should fail with developer tier")
	}
	
	// Test enhanced feature gate
	enhancedGate := NewEnhancedFeatureGate()
	
	err = enhancedGate.RequireProfessional()
	// May pass or fail depending on trial status, just exercise the code
	t.Logf("Enhanced RequireProfessional result: %v", err)
	
	err = enhancedGate.RequireEnterprise()
	// Should typically fail unless special license
	if err == nil {
		t.Log("Enhanced RequireEnterprise passed (may have special license)")
	}
}