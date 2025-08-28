package main

import (
	"bytes"
	"crypto/rand"
	"crypto/rsa"
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"contextlite/internal/license"
)

// generateTestPrivateKey creates a test RSA private key
func generateTestPrivateKey() *rsa.PrivateKey {
	privateKey, _ := rsa.GenerateKey(rand.Reader, 2048)
	return privateKey
}

// TestLicenseServer_EnhancedEndpoints tests the new tracking endpoints
func TestLicenseServer_EnhancedEndpoints(t *testing.T) {
	config := getTestConfig()
	server, err := NewLicenseServer(config)
	require.NoError(t, err)
	defer server.tracker.Close()

	t.Run("activate_endpoint", func(t *testing.T) {
		payload := map[string]interface{}{
			"license_key": "TEST-ACTIVATE-001",
			"email":       "activate@example.com",
			"hardware_id": "activate-hardware-001",
			"tier":        "professional",
		}

		jsonData, _ := json.Marshal(payload)
		req := httptest.NewRequest("POST", "/activate", bytes.NewBuffer(jsonData))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("X-Forwarded-For", "192.168.1.100")
		req.Header.Set("User-Agent", "ContextLite/1.0.0")

		w := httptest.NewRecorder()
		server.handleActivateLicense(w, req)

		assert.Equal(t, http.StatusOK, w.Code)

		var response map[string]interface{}
		err := json.NewDecoder(w.Body).Decode(&response)
		assert.NoError(t, err)
		assert.True(t, response["success"].(bool))
		assert.Contains(t, response, "activation")
	})

	t.Run("activate_limit_exceeded", func(t *testing.T) {
		licenseKey := "TEST-LIMIT-001"

		// Activate on first device (should succeed)
		payload1 := map[string]interface{}{
			"license_key": licenseKey,
			"email":       "limit@example.com",
			"hardware_id": "limit-hardware-001",
			"tier":        "developer", // Only 1 activation allowed
		}

		jsonData1, _ := json.Marshal(payload1)
		req1 := httptest.NewRequest("POST", "/activate", bytes.NewBuffer(jsonData1))
		req1.Header.Set("Content-Type", "application/json")

		w1 := httptest.NewRecorder()
		server.handleActivateLicense(w1, req1)
		assert.Equal(t, http.StatusOK, w1.Code)

		// Try to activate on second device (should fail)
		payload2 := map[string]interface{}{
			"license_key": licenseKey,
			"email":       "limit@example.com",
			"hardware_id": "limit-hardware-002",
			"tier":        "developer",
		}

		jsonData2, _ := json.Marshal(payload2)
		req2 := httptest.NewRequest("POST", "/activate", bytes.NewBuffer(jsonData2))
		req2.Header.Set("Content-Type", "application/json")

		w2 := httptest.NewRecorder()
		server.handleActivateLicense(w2, req2)
		assert.Equal(t, http.StatusBadRequest, w2.Code)

		var response map[string]interface{}
		_ = json.NewDecoder(w2.Body).Decode(&response)
		assert.False(t, response["success"].(bool))
		assert.Contains(t, response["error"].(string), "activation limit exceeded")
	})

	t.Run("deactivate_endpoint", func(t *testing.T) {
		// First activate a license
		licenseKey := "TEST-DEACTIVATE-001"
		activatePayload := map[string]interface{}{
			"license_key": licenseKey,
			"email":       "deactivate@example.com",
			"hardware_id": "deactivate-hardware-001",
			"tier":        "professional",
		}

		jsonData, _ := json.Marshal(activatePayload)
		req := httptest.NewRequest("POST", "/activate", bytes.NewBuffer(jsonData))
		req.Header.Set("Content-Type", "application/json")

		w := httptest.NewRecorder()
		server.handleActivateLicense(w, req)
		assert.Equal(t, http.StatusOK, w.Code)

		// Now deactivate it
		deactivatePayload := map[string]interface{}{
			"license_key": licenseKey,
			"hardware_id": "deactivate-hardware-001",
		}

		jsonData, _ = json.Marshal(deactivatePayload)
		req = httptest.NewRequest("POST", "/deactivate", bytes.NewBuffer(jsonData))
		req.Header.Set("Content-Type", "application/json")

		w = httptest.NewRecorder()
		server.handleDeactivateLicense(w, req)
		assert.Equal(t, http.StatusOK, w.Code)

		var response map[string]interface{}
		_ = json.NewDecoder(w.Body).Decode(&response)
		assert.True(t, response["success"].(bool))
	})

	t.Run("record_usage_endpoint", func(t *testing.T) {
		payload := map[string]interface{}{
			"license_key":   "TEST-USAGE-001",
			"activation_id": "test-activation-001",
			"event_type":    "app_startup",
			"metadata": map[string]interface{}{
				"version": "1.0.0",
				"os":      "windows",
			},
		}

		jsonData, _ := json.Marshal(payload)
		req := httptest.NewRequest("POST", "/usage", bytes.NewBuffer(jsonData))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("X-Forwarded-For", "192.168.1.100")

		w := httptest.NewRecorder()
		server.handleRecordUsage(w, req)
		assert.Equal(t, http.StatusOK, w.Code)

		var response map[string]interface{}
		_ = json.NewDecoder(w.Body).Decode(&response)
		assert.True(t, response["success"].(bool))
	})

	t.Run("analytics_endpoint", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/analytics?days=30", nil)
		w := httptest.NewRecorder()

		server.handleGetAnalytics(w, req)
		assert.Equal(t, http.StatusOK, w.Code)

		var response map[string]interface{}
		_ = json.NewDecoder(w.Body).Decode(&response)
		assert.True(t, response["success"].(bool))
		assert.Contains(t, response, "analytics")
	})

	t.Run("security_events_endpoint", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/security?hours=24", nil)
		w := httptest.NewRecorder()

		server.handleSecurityEvents(w, req)
		assert.Equal(t, http.StatusOK, w.Code)

		var response map[string]interface{}
		_ = json.NewDecoder(w.Body).Decode(&response)
		assert.True(t, response["success"].(bool))
		assert.Contains(t, response, "events")
	})
}

// TestLicenseServer_EnhancedLicenseGeneration tests license generation with tracking
func TestLicenseServer_EnhancedLicenseGeneration(t *testing.T) {
	config := getTestConfig()
	server, err := NewLicenseServer(config)
	require.NoError(t, err)
	defer server.tracker.Close()

	t.Run("generate_and_send_with_tracking", func(t *testing.T) {
		email := "tracking@example.com"
		tier := license.TierPro
		customerID := "cust_tracking_123"
		hardwareID := "tracking-hardware-001"

		err := server.generateAndSendLicense(email, tier, customerID, hardwareID)
		assert.NoError(t, err)

		// Verify usage was recorded (would need to check database in real implementation)
		analytics, err := server.tracker.GetAnalytics(1)
		assert.NoError(t, err)
		assert.NotNil(t, analytics)
	})
}

// TestLicenseServer_ErrorHandling tests error handling in new endpoints
func TestLicenseServer_ErrorHandling(t *testing.T) {
	config := getTestConfig()
	server, err := NewLicenseServer(config)
	require.NoError(t, err)
	defer server.tracker.Close()

	tests := []struct {
		name       string
		endpoint   string
		method     string
		payload    interface{}
		wantStatus int
	}{
		{
			name:       "activate_invalid_method",
			endpoint:   "/activate",
			method:     "GET",
			payload:    nil,
			wantStatus: http.StatusMethodNotAllowed,
		},
		{
			name:       "activate_invalid_json",
			endpoint:   "/activate",
			method:     "POST",
			payload:    "invalid json",
			wantStatus: http.StatusBadRequest,
		},
		{
			name:       "usage_invalid_method",
			endpoint:   "/usage",
			method:     "GET",
			payload:    nil,
			wantStatus: http.StatusMethodNotAllowed,
		},
		{
			name:       "analytics_invalid_method",
			endpoint:   "/analytics",
			method:     "POST",
			payload:    nil,
			wantStatus: http.StatusMethodNotAllowed,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			var req *http.Request

			if tt.payload != nil {
				if str, ok := tt.payload.(string); ok {
					req = httptest.NewRequest(tt.method, tt.endpoint, bytes.NewBufferString(str))
				} else {
					jsonData, _ := json.Marshal(tt.payload)
					req = httptest.NewRequest(tt.method, tt.endpoint, bytes.NewBuffer(jsonData))
				}
			} else {
				req = httptest.NewRequest(tt.method, tt.endpoint, nil)
			}

			if tt.method == "POST" {
				req.Header.Set("Content-Type", "application/json")
			}

			w := httptest.NewRecorder()

			switch tt.endpoint {
			case "/activate":
				server.handleActivateLicense(w, req)
			case "/deactivate":
				server.handleDeactivateLicense(w, req)
			case "/usage":
				server.handleRecordUsage(w, req)
			case "/analytics":
				server.handleGetAnalytics(w, req)
			case "/security":
				server.handleSecurityEvents(w, req)
			}

			assert.Equal(t, tt.wantStatus, w.Code)
		})
	}
}

// TestLicenseServer_ConcurrentRequests tests handling of concurrent requests
func TestLicenseServer_ConcurrentRequests(t *testing.T) {
	config := getTestConfig()
	server, err := NewLicenseServer(config)
	require.NoError(t, err)
	defer server.tracker.Close()

	const numRequests = 50
	results := make(chan error, numRequests)

	// Send concurrent activation requests
	for i := 0; i < numRequests; i++ {
		go func(id int) {
			payload := map[string]interface{}{
				"license_key": fmt.Sprintf("CONCURRENT-%03d", id),
				"email":       fmt.Sprintf("user%d@example.com", id),
				"hardware_id": fmt.Sprintf("hardware-%03d", id),
				"tier":        "professional",
			}

			jsonData, _ := json.Marshal(payload)
			req := httptest.NewRequest("POST", "/activate", bytes.NewBuffer(jsonData))
			req.Header.Set("Content-Type", "application/json")

			w := httptest.NewRecorder()
			server.handleActivateLicense(w, req)

			if w.Code != http.StatusOK {
				results <- fmt.Errorf("request %d failed with status %d", id, w.Code)
			} else {
				results <- nil
			}
		}(i)
	}

	// Collect results
	successCount := 0
	for i := 0; i < numRequests; i++ {
		err := <-results
		if err == nil {
			successCount++
		} else {
			t.Logf("Request failed: %v", err)
		}
	}

	// Most requests should succeed (allowing for some database contention)
	assert.GreaterOrEqual(t, successCount, numRequests-5, "Most concurrent requests should succeed")
}

// TestLicenseServer_UsageAnalyticsFlow tests the complete usage analytics flow
func TestLicenseServer_UsageAnalyticsFlow(t *testing.T) {
	config := getTestConfig()
	
	// Create a temporary database for this test to avoid interference
	tmpDB := filepath.Join(os.TempDir(), fmt.Sprintf("test_analytics_%d.db", time.Now().UnixNano()))
	defer func() { _ = os.Remove(tmpDB) }()
	
	// Create server with clean database
	tracker, err := license.NewLicenseTracker(tmpDB)
	require.NoError(t, err)
	defer func() { _ = tracker.Close() }()
	
	server := &LicenseServer{
		config:     config,
		privateKey: generateTestPrivateKey(),
		tracker:    tracker,
	}

	// Step 1: Activate multiple licenses
	licenses := []map[string]interface{}{
		{
			"license_key": "ANALYTICS-001",
			"email":       "user1@example.com",
			"hardware_id": "analytics-hw-001",
			"tier":        "professional",
		},
		{
			"license_key": "ANALYTICS-002",
			"email":       "user2@example.com",
			"hardware_id": "analytics-hw-002",
			"tier":        "professional",
		},
		{
			"license_key": "ANALYTICS-003",
			"email":       "user3@example.com",
			"hardware_id": "analytics-hw-003",
			"tier":        "developer",
		},
	}

	activationIDs := make([]string, len(licenses))

	for i, licenseData := range licenses {
		jsonData, _ := json.Marshal(licenseData)
		req := httptest.NewRequest("POST", "/activate", bytes.NewBuffer(jsonData))
		req.Header.Set("Content-Type", "application/json")

		w := httptest.NewRecorder()
		server.handleActivateLicense(w, req)
		assert.Equal(t, http.StatusOK, w.Code)

		var response map[string]interface{}
		_ = json.NewDecoder(w.Body).Decode(&response)
		activation := response["activation"].(map[string]interface{})
		activationIDs[i] = activation["activation_id"].(string)
	}

	// Step 2: Record usage events for each license
	usageEvents := []map[string]interface{}{
		{
			"license_key":   "ANALYTICS-001",
			"activation_id": activationIDs[0],
			"event_type":    "app_startup",
			"metadata":      map[string]interface{}{"version": "1.0.0"},
		},
		{
			"license_key":   "ANALYTICS-001",
			"activation_id": activationIDs[0],
			"event_type":    "context_query",
			"metadata":      map[string]interface{}{"duration_ms": 450},
		},
		{
			"license_key":   "ANALYTICS-002",
			"activation_id": activationIDs[1],
			"event_type":    "app_startup",
			"metadata":      map[string]interface{}{"version": "1.0.0"},
		},
	}

	for _, usageData := range usageEvents {
		jsonData, _ := json.Marshal(usageData)
		req := httptest.NewRequest("POST", "/usage", bytes.NewBuffer(jsonData))
		req.Header.Set("Content-Type", "application/json")

		w := httptest.NewRecorder()
		server.handleRecordUsage(w, req)
		assert.Equal(t, http.StatusOK, w.Code)
	}

	// Step 3: Get analytics and verify data
	req := httptest.NewRequest("GET", "/analytics?days=1", nil)
	w := httptest.NewRecorder()
	server.handleGetAnalytics(w, req)
	assert.Equal(t, http.StatusOK, w.Code)

	var response map[string]interface{}
	_ = json.NewDecoder(w.Body).Decode(&response)
	assert.True(t, response["success"].(bool))

	analytics := response["analytics"].(map[string]interface{})
	assert.Equal(t, float64(3), analytics["total_licenses"].(float64))
	assert.GreaterOrEqual(t, analytics["active_licenses"].(float64), float64(2))
}

// TestLicenseServer_SecurityEventGeneration tests security event generation
func TestLicenseServer_SecurityEventGeneration(t *testing.T) {
	config := getTestConfig()
	server, err := NewLicenseServer(config)
	require.NoError(t, err)
	defer server.tracker.Close()

	licenseKey := "SECURITY-TEST-001"

	// Activate license on first device
	payload1 := map[string]interface{}{
		"license_key": licenseKey,
		"email":       "security@example.com",
		"hardware_id": "security-hw-001",
		"tier":        "developer", // Only 1 activation allowed
	}

	jsonData, _ := json.Marshal(payload1)
	req := httptest.NewRequest("POST", "/activate", bytes.NewBuffer(jsonData))
	req.Header.Set("Content-Type", "application/json")

	w := httptest.NewRecorder()
	server.handleActivateLicense(w, req)
	assert.Equal(t, http.StatusOK, w.Code)

	// Try to activate on second device (should generate security event)
	payload2 := map[string]interface{}{
		"license_key": licenseKey,
		"email":       "security@example.com",
		"hardware_id": "security-hw-002",
		"tier":        "developer",
	}

	jsonData, _ = json.Marshal(payload2)
	req = httptest.NewRequest("POST", "/activate", bytes.NewBuffer(jsonData))
	req.Header.Set("Content-Type", "application/json")

	w = httptest.NewRecorder()
	server.handleActivateLicense(w, req)
	assert.Equal(t, http.StatusBadRequest, w.Code)

	// Check that security event was recorded
	req = httptest.NewRequest("GET", "/security?hours=1", nil)
	w = httptest.NewRecorder()
	server.handleSecurityEvents(w, req)
	assert.Equal(t, http.StatusOK, w.Code)

	var response map[string]interface{}
	_ = json.NewDecoder(w.Body).Decode(&response)
	assert.True(t, response["success"].(bool))

	events := response["events"].([]interface{})
	assert.NotEmpty(t, events, "Should have recorded security events")

	// Look for activation limit exceeded event
	found := false
	for _, event := range events {
		eventMap := event.(map[string]interface{})
		if eventMap["event_type"].(string) == "activation_limit_exceeded" {
			found = true
			assert.Equal(t, "high", eventMap["severity"].(string))
			break
		}
	}
	assert.True(t, found, "Should have found activation_limit_exceeded event")
}

// TestLicenseServer_DatabasePersistence tests data persistence across server restarts
func TestLicenseServer_DatabasePersistence(t *testing.T) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "test_persistence_server.db")
	defer func() { _ = os.Remove(dbPath) }()

	licenseKey := "PERSIST-SERVER-001"

	// Create first server instance and activate license
	{
		config := getTestConfig()
		// Override database path to use our test database
		server, err := NewLicenseServer(config)
		require.NoError(t, err)
		
		// Close default tracker and create one with our test path
		server.tracker.Close()
		server.tracker, err = license.NewLicenseTracker(dbPath)
		require.NoError(t, err)

		payload := map[string]interface{}{
			"license_key": licenseKey,
			"email":       "persist@example.com",
			"hardware_id": "persist-hw-001",
			"tier":        "professional",
		}

		jsonData, _ := json.Marshal(payload)
		req := httptest.NewRequest("POST", "/activate", bytes.NewBuffer(jsonData))
		req.Header.Set("Content-Type", "application/json")

		w := httptest.NewRecorder()
		server.handleActivateLicense(w, req)
		assert.Equal(t, http.StatusOK, w.Code)

		server.tracker.Close()
	}

	// Create second server instance and verify data persists
	{
		config := getTestConfig()
		server, err := NewLicenseServer(config)
		require.NoError(t, err)
		
		// Close default tracker and create one with our test path
		server.tracker.Close()
		server.tracker, err = license.NewLicenseTracker(dbPath)
		require.NoError(t, err)
		defer server.tracker.Close()

		req := httptest.NewRequest("GET", "/analytics?days=30", nil)
		w := httptest.NewRecorder()
		server.handleGetAnalytics(w, req)
		assert.Equal(t, http.StatusOK, w.Code)

		var response map[string]interface{}
		_ = json.NewDecoder(w.Body).Decode(&response)
		analytics := response["analytics"].(map[string]interface{})
		
		// Should still show the license we activated in the first instance
		assert.GreaterOrEqual(t, analytics["total_licenses"].(float64), float64(1))
	}
}

// Benchmark tests for the new endpoints
func BenchmarkLicenseServer_ActivateEndpoint(b *testing.B) {
	config := getTestConfig()
	server, err := NewLicenseServer(config)
	require.NoError(b, err)
	defer server.tracker.Close()

	payload := map[string]interface{}{
		"email":       "bench@example.com",
		"hardware_id": "bench-hw-001",
		"tier":        "professional",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		payload["license_key"] = fmt.Sprintf("BENCH-ACTIVATE-%d", i)
		payload["hardware_id"] = fmt.Sprintf("bench-hw-%d", i)

		jsonData, _ := json.Marshal(payload)
		req := httptest.NewRequest("POST", "/activate", bytes.NewBuffer(jsonData))
		req.Header.Set("Content-Type", "application/json")

		w := httptest.NewRecorder()
		server.handleActivateLicense(w, req)

		if w.Code != http.StatusOK {
			b.Fatalf("Activation failed with status %d", w.Code)
		}
	}
}

func BenchmarkLicenseServer_UsageEndpoint(b *testing.B) {
	config := getTestConfig()
	server, err := NewLicenseServer(config)
	require.NoError(b, err)
	defer server.tracker.Close()

	payload := map[string]interface{}{
		"license_key":   "BENCH-USAGE-001",
		"activation_id": "bench-activation-001",
		"event_type":    "benchmark_event",
		"metadata":      map[string]interface{}{"test": true},
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		jsonData, _ := json.Marshal(payload)
		req := httptest.NewRequest("POST", "/usage", bytes.NewBuffer(jsonData))
		req.Header.Set("Content-Type", "application/json")

		w := httptest.NewRecorder()
		server.handleRecordUsage(w, req)

		if w.Code != http.StatusOK {
			b.Fatalf("Usage recording failed with status %d", w.Code)
		}
	}
}
