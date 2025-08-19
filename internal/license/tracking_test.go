package license

import (
	"fmt"
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestLicenseTracker_NewLicenseTracker tests tracker initialization
func TestLicenseTracker_NewLicenseTracker(t *testing.T) {
	// Create temporary database
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "test_tracking.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(t, err)
	assert.NotNil(t, tracker)
	assert.NotNil(t, tracker.db)

	err = tracker.Close()
	assert.NoError(t, err)
}

// TestLicenseTracker_ActivateLicense tests license activation flow
func TestLicenseTracker_ActivateLicense(t *testing.T) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "test_activate.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(t, err)
	defer tracker.Close()

	tests := []struct {
		name         string
		licenseKey   string
		email        string
		hardwareID   string
		tier         LicenseTier
		ipAddress    string
		userAgent    string
		expectError  bool
		errorContains string
	}{
		{
			name:       "successful_developer_activation",
			licenseKey: "TEST-DEVL-LICN-0001",
			email:      "dev@example.com",
			hardwareID: "dev-hardware-001",
			tier:       TierDeveloper,
			ipAddress:  "192.168.1.100",
			userAgent:  "ContextLite/1.0.0",
			expectError: false,
		},
		{
			name:       "successful_professional_activation",
			licenseKey: "TEST-PROF-LICN-0001",
			email:      "pro@example.com",
			hardwareID: "pro-hardware-001",
			tier:       TierPro,
			ipAddress:  "192.168.1.101",
			userAgent:  "ContextLite/1.0.0",
			expectError: false,
		},
		{
			name:       "successful_enterprise_activation",
			licenseKey: "TEST-ENTR-LICN-0001",
			email:      "ent@example.com",
			hardwareID: "ent-hardware-001",
			tier:       TierEnterprise,
			ipAddress:  "192.168.1.102",
			userAgent:  "ContextLite/1.0.0",
			expectError: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			activation, err := tracker.ActivateLicense(
				tt.licenseKey, tt.email, tt.hardwareID,
				tt.ipAddress, tt.userAgent, tt.tier,
			)

			if tt.expectError {
				assert.Error(t, err)
				if tt.errorContains != "" {
					assert.Contains(t, err.Error(), tt.errorContains)
				}
				assert.Nil(t, activation)
			} else {
				assert.NoError(t, err)
				assert.NotNil(t, activation)
				assert.Equal(t, tt.licenseKey, activation.LicenseKey)
				assert.Equal(t, tt.email, activation.Email)
				assert.Equal(t, tt.hardwareID, activation.HardwareID)
				assert.Equal(t, tt.ipAddress, activation.IPAddress)
				assert.Equal(t, string(tt.tier), activation.Tier)
				assert.True(t, activation.IsActive)
				assert.NotEmpty(t, activation.ActivationID)
			}
		})
	}
}

// TestLicenseTracker_ActivationLimits tests activation limit enforcement
func TestLicenseTracker_ActivationLimits(t *testing.T) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "test_limits.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(t, err)
	defer tracker.Close()

	licenseKey := "TEST-LIMIT-CHECK-001"
	email := "limit@example.com"

	// Test developer tier limit (1 device)
	_, err = tracker.ActivateLicense(licenseKey, email, "hardware-1", "192.168.1.1", "test", TierDeveloper)
	assert.NoError(t, err)

	// Second activation should fail
	_, err = tracker.ActivateLicense(licenseKey, email, "hardware-2", "192.168.1.2", "test", TierDeveloper)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "activation limit exceeded")

	// Test professional tier limit (3 devices)
	proLicenseKey := "TEST-PRO-LIMIT-001"
	for i := 1; i <= 3; i++ {
		_, err = tracker.ActivateLicense(proLicenseKey, email, 
			fmt.Sprintf("pro-hardware-%d", i), "192.168.1.1", "test", TierPro)
		assert.NoError(t, err)
	}

	// Fourth activation should fail
	_, err = tracker.ActivateLicense(proLicenseKey, email, "pro-hardware-4", "192.168.1.1", "test", TierPro)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "activation limit exceeded")
}

// TestLicenseTracker_ValidateActivation tests activation validation
func TestLicenseTracker_ValidateActivation(t *testing.T) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "test_validate.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(t, err)
	defer tracker.Close()

	licenseKey := "TEST-VALIDATE-001"
	hardwareID := "validate-hardware-001"

	// Activate license first
	_, err = tracker.ActivateLicense(licenseKey, "test@example.com", hardwareID, "192.168.1.1", "test", TierPro)
	require.NoError(t, err)

	// Validate should succeed
	activation, err := tracker.ValidateActivation(licenseKey, hardwareID)
	assert.NoError(t, err)
	assert.NotNil(t, activation)
	assert.Equal(t, licenseKey, activation.LicenseKey)

	// Validate with wrong hardware should fail
	_, err = tracker.ValidateActivation(licenseKey, "wrong-hardware")
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "not activated on this hardware")

	// Validate non-existent license should fail
	_, err = tracker.ValidateActivation("NON-EXISTENT", hardwareID)
	assert.Error(t, err)
}

// TestLicenseTracker_RecordUsage tests usage event recording
func TestLicenseTracker_RecordUsage(t *testing.T) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "test_usage.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(t, err)
	defer tracker.Close()

	licenseKey := "TEST-USAGE-001"
	activationID := "activation-001"

	tests := []struct {
		name      string
		eventType string
		metadata  map[string]interface{}
		ipAddress string
	}{
		{
			name:      "app_startup",
			eventType: "app_startup",
			metadata: map[string]interface{}{
				"version": "1.0.0",
				"os":      "windows",
			},
			ipAddress: "192.168.1.100",
		},
		{
			name:      "context_query",
			eventType: "context_query",
			metadata: map[string]interface{}{
				"query_type":   "smt",
				"duration_ms":  450,
				"result_count": 23,
			},
			ipAddress: "192.168.1.100",
		},
		{
			name:      "feature_request",
			eventType: "feature_request",
			metadata: map[string]interface{}{
				"feature": "advanced_smt",
				"allowed": true,
			},
			ipAddress: "192.168.1.100",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tracker.RecordUsage(licenseKey, activationID, tt.eventType, tt.metadata, tt.ipAddress)
			assert.NoError(t, err)
		})
	}
}

// TestLicenseTracker_GetAnalytics tests analytics generation
func TestLicenseTracker_GetAnalytics(t *testing.T) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "test_analytics.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(t, err)
	defer tracker.Close()

	// Create test data
	licenseKeys := []string{"ANAL-001", "ANAL-002", "ANAL-003"}
	for i, key := range licenseKeys {
		_, err = tracker.ActivateLicense(
			key, fmt.Sprintf("user%d@example.com", i+1),
			fmt.Sprintf("hardware-%d", i+1), "192.168.1.1", "test", TierPro,
		)
		require.NoError(t, err)

		// Record some usage
		err = tracker.RecordUsage(key, fmt.Sprintf("activation-%d", i+1), "app_startup", nil, "192.168.1.1")
		require.NoError(t, err)
	}

	analytics, err := tracker.GetAnalytics(30)
	assert.NoError(t, err)
	assert.NotNil(t, analytics)
	assert.Equal(t, 3, analytics.TotalLicenses)
	assert.Equal(t, 3, analytics.ActiveLicenses)
}

// TestLicenseTracker_SecurityEvents tests security event logging
func TestLicenseTracker_SecurityEvents(t *testing.T) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "test_security.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(t, err)
	defer tracker.Close()

	// Try to exceed activation limit to trigger security event
	licenseKey := "SEC-TEST-001"
	_, err = tracker.ActivateLicense(licenseKey, "sec@example.com", "hw-1", "192.168.1.1", "test", TierDeveloper)
	require.NoError(t, err)

	// This should trigger a security event
	_, err = tracker.ActivateLicense(licenseKey, "sec@example.com", "hw-2", "192.168.1.2", "test", TierDeveloper)
	assert.Error(t, err)

	// Check security events
	events, err := tracker.GetSecurityEvents(24)
	assert.NoError(t, err)
	assert.NotEmpty(t, events)

	found := false
	for _, event := range events {
		if event.EventType == "activation_limit_exceeded" {
			found = true
			assert.Equal(t, "high", event.Severity)
			break
		}
	}
	assert.True(t, found, "Should have found activation_limit_exceeded event")
}

// TestLicenseTracker_DeactivateLicense tests license deactivation
func TestLicenseTracker_DeactivateLicense(t *testing.T) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "test_deactivate.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(t, err)
	defer tracker.Close()

	licenseKey := "DEACT-TEST-001"
	hardwareID := "deact-hardware-001"

	// Activate license
	_, err = tracker.ActivateLicense(licenseKey, "deact@example.com", hardwareID, "192.168.1.1", "test", TierPro)
	require.NoError(t, err)

	// Validate it works
	_, err = tracker.ValidateActivation(licenseKey, hardwareID)
	assert.NoError(t, err)

	// Deactivate license
	err = tracker.DeactivateLicense(licenseKey, hardwareID)
	assert.NoError(t, err)

	// Validation should now fail
	_, err = tracker.ValidateActivation(licenseKey, hardwareID)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "deactivated")
}

// TestLicenseTracker_ConcurrentAccess tests thread safety
func TestLicenseTracker_ConcurrentAccess(t *testing.T) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "test_concurrent.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(t, err)
	defer tracker.Close()

	// Run concurrent activations
	const numGoroutines = 10
	errors := make(chan error, numGoroutines)

	for i := 0; i < numGoroutines; i++ {
		go func(id int) {
			licenseKey := fmt.Sprintf("CONCURRENT-%03d", id)
			_, err := tracker.ActivateLicense(
				licenseKey, fmt.Sprintf("user%d@example.com", id),
				fmt.Sprintf("hardware-%d", id), "192.168.1.1", "test", TierPro,
			)
			errors <- err
		}(i)
	}

	// Collect results
	successCount := 0
	for i := 0; i < numGoroutines; i++ {
		err := <-errors
		if err == nil {
			successCount++
		}
	}

	assert.Equal(t, numGoroutines, successCount, "All concurrent activations should succeed")
}

// TestLicenseTracker_DatabasePersistence tests data persistence
func TestLicenseTracker_DatabasePersistence(t *testing.T) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "test_persistence.db")
	defer os.Remove(dbPath)

	licenseKey := "PERSIST-TEST-001"
	hardwareID := "persist-hardware-001"

	// Create tracker and add data
	{
		tracker, err := NewLicenseTracker(dbPath)
		require.NoError(t, err)

		_, err = tracker.ActivateLicense(licenseKey, "persist@example.com", hardwareID, "192.168.1.1", "test", TierPro)
		require.NoError(t, err)

		tracker.Close()
	}

	// Create new tracker instance and verify data persists
	{
		tracker, err := NewLicenseTracker(dbPath)
		require.NoError(t, err)
		defer tracker.Close()

		activation, err := tracker.ValidateActivation(licenseKey, hardwareID)
		assert.NoError(t, err)
		assert.NotNil(t, activation)
		assert.Equal(t, licenseKey, activation.LicenseKey)
	}
}

// Benchmark tests for performance
func BenchmarkLicenseTracker_ActivateLicense(b *testing.B) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "bench_activate.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(b, err)
	defer tracker.Close()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		licenseKey := fmt.Sprintf("BENCH-ACTIVATE-%d", i)
		_, err := tracker.ActivateLicense(
			licenseKey, "bench@example.com",
			fmt.Sprintf("hardware-%d", i), "192.168.1.1", "test", TierPro,
		)
		if err != nil {
			b.Fatal(err)
		}
	}
}

func BenchmarkLicenseTracker_RecordUsage(b *testing.B) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "bench_usage.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(b, err)
	defer tracker.Close()

	// Setup test license
	licenseKey := "BENCH-USAGE-001"
	activationID := "bench-activation-001"

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		err := tracker.RecordUsage(licenseKey, activationID, "benchmark_event", nil, "192.168.1.1")
		if err != nil {
			b.Fatal(err)
		}
	}
}

func BenchmarkLicenseTracker_ValidateActivation(b *testing.B) {
	tmpDir := os.TempDir()
	dbPath := filepath.Join(tmpDir, "bench_validate.db")
	defer os.Remove(dbPath)

	tracker, err := NewLicenseTracker(dbPath)
	require.NoError(b, err)
	defer tracker.Close()

	// Setup test license
	licenseKey := "BENCH-VALIDATE-001"
	hardwareID := "bench-hardware-001"
	_, err = tracker.ActivateLicense(licenseKey, "bench@example.com", hardwareID, "192.168.1.1", "test", TierPro)
	require.NoError(b, err)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, err := tracker.ValidateActivation(licenseKey, hardwareID)
		if err != nil {
			b.Fatal(err)
		}
	}
}
