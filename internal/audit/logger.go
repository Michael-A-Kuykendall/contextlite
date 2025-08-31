// Military-grade audit logging with tamper resistance for DOD compliance
package audit

import (
	"crypto/hmac"
	"crypto/sha512"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"log/slog"
	"os"
	"time"
)

// AuditEvent represents a single auditable event per CMMC requirements
type AuditEvent struct {
	Timestamp      time.Time              `json:"timestamp"`
	EventID        string                 `json:"event_id"`
	UserID         string                 `json:"user_id"`
	Action         string                 `json:"action"`
	Resource       string                 `json:"resource"`
	Result         string                 `json:"result"`
	IPAddress      string                 `json:"ip_address"`
	UserAgent      string                 `json:"user_agent"`
	SessionID      string                 `json:"session_id"`
	Classification string                 `json:"classification"`
	Details        map[string]interface{} `json:"details,omitempty"`
	MAC            string                 `json:"mac"` // Message Authentication Code for tamper resistance
}

// AuditLogger provides tamper-resistant audit logging compliant with AU-2, AU-3, AU-9
type AuditLogger struct {
	hmacKey []byte
	logger  *slog.Logger
}

// NewAuditLogger creates a new audit logger with HMAC protection
func NewAuditLogger(hmacKey []byte) *AuditLogger {
	// Create structured JSON logger for SIEM compatibility
	logger := slog.New(slog.NewJSONHandler(os.Stdout, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	
	return &AuditLogger{
		hmacKey: hmacKey,
		logger:  logger,
	}
}

// LogEvent logs an auditable event with integrity protection (AU-3, AU-9)
func (l *AuditLogger) LogEvent(event *AuditEvent) error {
	// Add timestamp if not set (AU-8)
	if event.Timestamp.IsZero() {
		event.Timestamp = time.Now().UTC()
	}
	
	// Generate unique event ID for audit trail
	if event.EventID == "" {
		event.EventID = fmt.Sprintf("audit-%d", time.Now().UnixNano())
	}
	
	// Serialize event for MAC calculation (exclude MAC field)
	data, err := json.Marshal(struct {
		*AuditEvent
		MAC string `json:"-"` // Exclude MAC from MAC calculation
	}{AuditEvent: event})
	if err != nil {
		return fmt.Errorf("failed to serialize audit event: %w", err)
	}
	
	// Create tamper-resistant MAC using HMAC-SHA512
	h := hmac.New(sha512.New, l.hmacKey)
	h.Write(data)
	event.MAC = hex.EncodeToString(h.Sum(nil))
	
	// Log with structured format for SIEM ingestion
	l.logger.Info("AUDIT_EVENT",
		"timestamp", event.Timestamp,
		"event_id", event.EventID,
		"user_id", event.UserID,
		"action", event.Action,
		"resource", event.Resource,
		"result", event.Result,
		"ip_address", event.IPAddress,
		"classification", event.Classification,
		"mac", event.MAC,
	)
	
	return nil
}

// VerifyEvent verifies the integrity of an audit event (AU-9)
func (l *AuditLogger) VerifyEvent(event *AuditEvent) bool {
	originalMAC := event.MAC
	event.MAC = "" // Clear MAC for verification
	
	data, err := json.Marshal(event)
	if err != nil {
		return false
	}
	
	h := hmac.New(sha512.New, l.hmacKey)
	h.Write(data)
	expectedMAC := hex.EncodeToString(h.Sum(nil))
	
	event.MAC = originalMAC // Restore MAC
	return hmac.Equal([]byte(originalMAC), []byte(expectedMAC))
}

// CMMC-compliant audit event creators

// LogAuthentication logs authentication events (IA-2, AU-2)
func (l *AuditLogger) LogAuthentication(userID, result, ipAddr string) error {
	return l.LogEvent(&AuditEvent{
		UserID:         userID,
		Action:         "AUTHENTICATION",
		Resource:       "AUTH_SYSTEM",
		Result:         result,
		IPAddress:      ipAddr,
		Classification: "UNCLASSIFIED",
		Details: map[string]interface{}{
			"auth_method": "JWT_MFA",
			"compliance":  "CMMC_IA_2",
		},
	})
}

// LogDataAccess logs CUI data access events (AC-3, AU-2)
func (l *AuditLogger) LogDataAccess(userID, resource, result, ipAddr string) error {
	return l.LogEvent(&AuditEvent{
		UserID:         userID,
		Action:         "DATA_ACCESS",
		Resource:       resource,
		Result:         result,
		IPAddress:      ipAddr,
		Classification: "CUI", // Controlled Unclassified Information
		Details: map[string]interface{}{
			"data_type":  "CUI",
			"compliance": "CMMC_AC_3",
		},
	})
}

// LogAdminAction logs administrative actions (AC-6, AU-2)
func (l *AuditLogger) LogAdminAction(userID, action, resource, result, ipAddr string) error {
	return l.LogEvent(&AuditEvent{
		UserID:         userID,
		Action:         action,
		Resource:       resource,
		Result:         result,
		IPAddress:      ipAddr,
		Classification: "CONFIDENTIAL",
		Details: map[string]interface{}{
			"privilege_level": "ADMIN",
			"compliance":      "CMMC_AC_6",
		},
	})
}

// LogSecurityEvent logs security-relevant events (SI-4, AU-2)
func (l *AuditLogger) LogSecurityEvent(userID, event, severity, ipAddr string) error {
	return l.LogEvent(&AuditEvent{
		UserID:         userID,
		Action:         "SECURITY_EVENT",
		Resource:       "SECURITY_MONITOR",
		Result:         event,
		IPAddress:      ipAddr,
		Classification: "CONFIDENTIAL",
		Details: map[string]interface{}{
			"severity":    severity,
			"compliance":  "CMMC_SI_4",
			"event_type":  "SECURITY_INCIDENT",
		},
	})
}

// LogConfigChange logs configuration changes (CM-3, AU-2)
func (l *AuditLogger) LogConfigChange(userID, resource, change, result, ipAddr string) error {
	return l.LogEvent(&AuditEvent{
		UserID:         userID,
		Action:         "CONFIG_CHANGE",
		Resource:       resource,
		Result:         result,
		IPAddress:      ipAddr,
		Classification: "CONFIDENTIAL",
		Details: map[string]interface{}{
			"change_details": change,
			"compliance":     "CMMC_CM_3",
		},
	})
}
