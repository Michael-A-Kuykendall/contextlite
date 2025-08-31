package audit

import (
	"crypto/rand"
	"testing"
	"time"
)

func TestAuditLogger(t *testing.T) {
	// Create HMAC key for testing
	hmacKey := make([]byte, 64)
	rand.Read(hmacKey)
	
	logger := NewAuditLogger(hmacKey)
	
	// Test authentication event logging
	err := logger.LogAuthentication("john.doe", "SUCCESS", "192.168.1.100")
	if err != nil {
		t.Fatalf("Failed to log authentication event: %v", err)
	}
	
	// Test data access event logging
	err = logger.LogDataAccess("john.doe", "classified_document.pdf", "SUCCESS", "192.168.1.100")
	if err != nil {
		t.Fatalf("Failed to log data access event: %v", err)
	}
	
	// Test admin action logging
	err = logger.LogAdminAction("admin", "USER_CREATE", "user_database", "SUCCESS", "192.168.1.50")
	if err != nil {
		t.Fatalf("Failed to log admin action: %v", err)
	}
}

func TestAuditEventIntegrity(t *testing.T) {
	hmacKey := make([]byte, 64)
	rand.Read(hmacKey)
	
	logger := NewAuditLogger(hmacKey)
	
	// Create test event
	event := &AuditEvent{
		UserID:         "test.user",
		Action:         "TEST_ACTION",
		Resource:       "test_resource",
		Result:         "SUCCESS",
		IPAddress:      "192.168.1.200",
		Classification: "CONFIDENTIAL",
	}
	
	// Log the event (this adds MAC)
	err := logger.LogEvent(event)
	if err != nil {
		t.Fatalf("Failed to log event: %v", err)
	}
	
	// Verify event integrity
	if !logger.VerifyEvent(event) {
		t.Error("Event integrity verification failed")
	}
	
	// Test tamper detection
	originalAction := event.Action
	event.Action = "TAMPERED_ACTION"
	
	if logger.VerifyEvent(event) {
		t.Error("Tampered event should fail integrity verification")
	}
	
	// Restore original action
	event.Action = originalAction
	if !logger.VerifyEvent(event) {
		t.Error("Restored event should pass integrity verification")
	}
}

func TestAuditEventFields(t *testing.T) {
	hmacKey := make([]byte, 64)
	rand.Read(hmacKey)
	
	logger := NewAuditLogger(hmacKey)
	
	event := &AuditEvent{
		UserID:         "security.officer",
		Action:         "SECURITY_REVIEW",
		Resource:       "audit_logs",
		Result:         "COMPLETED",
		IPAddress:      "10.0.0.50",
		UserAgent:      "ContextLite-Audit/1.0",
		SessionID:      "sess_12345",
		Classification: "SECRET",
		Details: map[string]interface{}{
			"records_reviewed": 1500,
			"anomalies_found":  0,
			"compliance":       "CMMC_AU_6",
		},
	}
	
	err := logger.LogEvent(event)
	if err != nil {
		t.Fatalf("Failed to log detailed event: %v", err)
	}
	
	// Verify all required fields are present
	if event.Timestamp.IsZero() {
		t.Error("Timestamp should be automatically set")
	}
	
	if event.EventID == "" {
		t.Error("Event ID should be automatically generated")
	}
	
	if event.MAC == "" {
		t.Error("MAC should be generated for integrity protection")
	}
	
	// Verify timestamp is recent (within last minute)
	if time.Since(event.Timestamp) > time.Minute {
		t.Error("Event timestamp should be recent")
	}
}

func TestSecurityEventLogging(t *testing.T) {
	hmacKey := make([]byte, 64)
	rand.Read(hmacKey)
	
	logger := NewAuditLogger(hmacKey)
	
	// Test security event logging
	err := logger.LogSecurityEvent("system", "INTRUSION_ATTEMPT", "HIGH", "203.0.113.1")
	if err != nil {
		t.Fatalf("Failed to log security event: %v", err)
	}
	
	// Test configuration change logging
	err = logger.LogConfigChange("admin", "firewall_rules", "Added rule: DENY 203.0.113.0/24", "SUCCESS", "192.168.1.10")
	if err != nil {
		t.Fatalf("Failed to log config change: %v", err)
	}
}

func TestCMMCCompliance(t *testing.T) {
	hmacKey := make([]byte, 64)
	rand.Read(hmacKey)
	
	logger := NewAuditLogger(hmacKey)
	
	// Test AU-2: Audit events
	auditableEvents := []string{
		"AUTHENTICATION",
		"DATA_ACCESS", 
		"CONFIG_CHANGE",
		"SECURITY_EVENT",
		"ADMIN_ACTION",
	}
	
	for _, eventType := range auditableEvents {
		event := &AuditEvent{
			UserID:         "compliance.test",
			Action:         eventType,
			Resource:       "cmmc_validation",
			Result:         "SUCCESS",
			IPAddress:      "127.0.0.1",
			Classification: "UNCLASSIFIED",
			Details: map[string]interface{}{
				"compliance_test": true,
				"cmmc_control":    "AU-2",
			},
		}
		
		err := logger.LogEvent(event)
		if err != nil {
			t.Errorf("Failed to log %s event for CMMC compliance: %v", eventType, err)
		}
		
		// Verify AU-9: Protection of audit information
		if !logger.VerifyEvent(event) {
			t.Errorf("CMMC AU-9 compliance failed: event integrity not protected")
		}
	}
}
