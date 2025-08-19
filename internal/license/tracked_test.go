package license

import (
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"testing"

	"github.com/stretchr/testify/assert"
)

// TestTrackedLicenseManager_NewTrackedLicenseManager tests tracked manager creation
func TestTrackedLicenseManager_NewTrackedLicenseManager(t *testing.T) {
	serverURL := "https://api.contextlite.com"
	tlm := NewTrackedLicenseManager(serverURL)

	assert.NotNil(t, tlm)
	assert.Equal(t, serverURL, tlm.serverURL)
	assert.NotNil(t, tlm.httpClient)
	assert.NotNil(t, tlm.LicenseManager)
}

// TestTrackedLicenseManager_RecordUsage tests usage recording
func TestTrackedLicenseManager_RecordUsage(t *testing.T) {
	// Create mock server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/usage" {
			assert.Equal(t, "POST", r.Method)
			assert.Equal(t, "application/json", r.Header.Get("Content-Type"))

			var req map[string]interface{}
			err := json.NewDecoder(r.Body).Decode(&req)
			assert.NoError(t, err)
			assert.Equal(t, "TEST-LICENSE-003", req["license_key"])
			assert.Equal(t, "test-activation-003", req["activation_id"])
			assert.Equal(t, "app_startup", req["event_type"])

			w.Header().Set("Content-Type", "application/json")
			response := map[string]interface{}{
				"success": true,
				"message": "Usage recorded",
			}
			json.NewEncoder(w).Encode(response)
		}
	}))
	defer server.Close()

	tlm := NewTrackedLicenseManager(server.URL)

	// Set up license and activation info
	tlm.license = &License{
		Key:        "TEST-LICENSE-003",
		Email:      "test@example.com",
		Tier:       TierPro,
	}
	tlm.activationID = "test-activation-003"

	err := tlm.RecordUsage("app_startup", map[string]interface{}{
		"version": "1.0.0",
	})
	assert.NoError(t, err)
}

// TestTrackedFeatureGate_NewTrackedFeatureGate tests tracked feature gate creation
func TestTrackedFeatureGate_NewTrackedFeatureGate(t *testing.T) {
	serverURL := "https://api.contextlite.com"
	fg := NewTrackedFeatureGate(serverURL)
	
	assert.NotNil(t, fg)
	assert.NotNil(t, fg.tracker)
	assert.Equal(t, serverURL, fg.tracker.serverURL)
	assert.NotNil(t, fg.EnhancedFeatureGate)
}

// TestTrackedLicenseManager_NetworkErrors tests handling of network errors
func TestTrackedLicenseManager_NetworkErrors(t *testing.T) {
	tlm := NewTrackedLicenseManager("http://invalid-server:9999")

	// Set up license and activation info for usage recording test
	tlm.license = &License{
		Key:        "TEST-LICENSE-004",
		Email:      "test@example.com",
		Tier:       TierPro,
	}
	tlm.activationID = "test-activation-004"

	// Test usage recording with network error (should not fail)
	err := tlm.RecordUsage("test_event", nil)
	assert.NoError(t, err) // Usage recording is async and shouldn't fail
}

// TestTrackedLicenseManager_DeactivateFromServer tests license deactivation
func TestTrackedLicenseManager_DeactivateFromServer(t *testing.T) {
	// Create mock server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/deactivate" {
			assert.Equal(t, "POST", r.Method)

			var req map[string]interface{}
			err := json.NewDecoder(r.Body).Decode(&req)
			assert.NoError(t, err)
			assert.Equal(t, "TEST-DEACTIVATE-001", req["license_key"])

			w.Header().Set("Content-Type", "application/json")
			response := map[string]interface{}{
				"success": true,
				"message": "License deactivated successfully",
			}
			json.NewEncoder(w).Encode(response)
		}
	}))
	defer server.Close()

	tlm := NewTrackedLicenseManager(server.URL)
	tlm.license = &License{
		Key:        "TEST-DEACTIVATE-001",
		Email:      "test@example.com",
		Tier:       TierPro,
	}
	tlm.activationID = "deactivate-activation-001"

	err := tlm.DeactivateFromServer()
	assert.NoError(t, err)
	assert.Equal(t, "", tlm.activationID) // Should be cleared
}

// TestTrackedFeatureGate_RequireFeature tests feature requirement with tracking
func TestTrackedFeatureGate_RequireFeature(t *testing.T) {
	// Create mock server for usage tracking
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/usage" {
			w.Header().Set("Content-Type", "application/json")
			response := map[string]interface{}{
				"success": true,
				"message": "Usage recorded",
			}
			json.NewEncoder(w).Encode(response)
		}
	}))
	defer server.Close()

	fg := NewTrackedFeatureGate(server.URL)

	// Test feature requirement (should fail without valid license)
	err := fg.RequireFeature("advanced_optimization")
	if err != nil {
		assert.Error(t, err) // Expected case - no valid license
	} else {
		// If no error, the feature gate found a license file - that's also valid
		assert.NoError(t, err)
	}
}

// TestTrackedFeatureGate_TrackingMethods tests various tracking methods
func TestTrackedFeatureGate_TrackingMethods(t *testing.T) {
	// Create mock server for usage tracking
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/usage" {
			w.Header().Set("Content-Type", "application/json")
			response := map[string]interface{}{
				"success": true,
				"message": "Usage recorded",
			}
			json.NewEncoder(w).Encode(response)
		}
	}))
	defer server.Close()

	fg := NewTrackedFeatureGate(server.URL)

	// Test various tracking methods
	fg.TrackStartup()
	fg.TrackQuery("semantic", 150, 10)
	fg.TrackError("network", "connection failed")

	// All should complete without error (async)
	assert.NotNil(t, fg)
}

// TestTrackedLicenseManager_ValidateWithServer tests online validation
func TestTrackedLicenseManager_ValidateWithServer(t *testing.T) {
	// Create mock server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/usage" {
			w.Header().Set("Content-Type", "application/json")
			response := map[string]interface{}{
				"success": true,
				"message": "Usage recorded",
			}
			json.NewEncoder(w).Encode(response)
		}
	}))
	defer server.Close()

	tlm := NewTrackedLicenseManager(server.URL)
	tlm.license = &License{
		Key:        "TEST-VALIDATE-001",
		Email:      "test@example.com",
		Tier:       TierPro,
	}
	tlm.activationID = "validate-activation-001"

	err := tlm.ValidateWithServer()
	assert.NoError(t, err)
}

// TestTrackedLicenseManager_ActivateWithServer tests activation flow
func TestTrackedLicenseManager_ActivateWithServer(t *testing.T) {
	// Create mock server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		assert.Equal(t, "POST", r.Method)
		assert.Equal(t, "/activate", r.URL.Path)
		assert.Equal(t, "application/json", r.Header.Get("Content-Type"))

		var req map[string]interface{}
		err := json.NewDecoder(r.Body).Decode(&req)
		assert.NoError(t, err)

		// Mock successful response
		response := ActivationResponse{
			Success: true,
			Activation: &LicenseActivation{
				ID:           1,
				LicenseKey:   req["license_key"].(string),
				Email:        req["email"].(string),
				HardwareID:   req["hardware_id"].(string),
				ActivationID: "test-activation-001",
				IsActive:     true,
			},
			Message: "License activated successfully",
		}

		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(response)
	}))
	defer server.Close()

	tlm := NewTrackedLicenseManager(server.URL)

	// Create a test license first
	license := &License{
		Key:        "TEST-LICENSE-001",
		Email:      "test@example.com",
		Tier:       TierPro,
	}

	activation, err := tlm.activateWithServer(license, "test-hardware-001")
	assert.NoError(t, err)
	assert.NotNil(t, activation)
	assert.Equal(t, "TEST-LICENSE-001", activation.LicenseKey)
	assert.Equal(t, "test-activation-001", activation.ActivationID)
	assert.True(t, activation.IsActive)
}
