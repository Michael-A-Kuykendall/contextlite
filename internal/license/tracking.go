package license

import (
	"crypto/sha256"
	"database/sql"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"log"
	"sync"
	"time"

	_ "modernc.org/sqlite"
)

// truncateString safely truncates a string to the specified length
func truncateString(s string, length int) string {
	if len(s) <= length {
		return s
	}
	return s[:length]
}

// LicenseTracker handles comprehensive license tracking and analytics
type LicenseTracker struct {
	db             *sql.DB
	activationAPI  string
	deactivationAPI string
	mu             sync.RWMutex
}

// LicenseActivation represents a license activation record
type LicenseActivation struct {
	ID               int       `json:"id"`
	LicenseKey       string    `json:"license_key"`
	Email           string    `json:"email"`
	HardwareID      string    `json:"hardware_id"`
	ActivationID    string    `json:"activation_id"`
	IPAddress       string    `json:"ip_address"`
	UserAgent       string    `json:"user_agent"`
	ActivatedAt     time.Time `json:"activated_at"`
	LastSeen        time.Time `json:"last_seen"`
	IsActive        bool      `json:"is_active"`
	ActivationCount int       `json:"activation_count"`
	MaxActivations  int       `json:"max_activations"`
	CustomerID      string    `json:"customer_id"`
	Tier            string    `json:"tier"`
}

// UsageEvent represents usage analytics
type UsageEvent struct {
	ID           int       `json:"id"`
	LicenseKey   string    `json:"license_key"`
	ActivationID string    `json:"activation_id"`
	EventType    string    `json:"event_type"` // startup, query, build, etc.
	Timestamp    time.Time `json:"timestamp"`
	Metadata     string    `json:"metadata"` // JSON metadata
	IPAddress    string    `json:"ip_address"`
}

// SecurityEvent represents security-related events
type SecurityEvent struct {
	ID           int       `json:"id"`
	LicenseKey   string    `json:"license_key"`
	EventType    string    `json:"event_type"` // invalid_signature, hardware_mismatch, etc.
	Description  string    `json:"description"`
	IPAddress    string    `json:"ip_address"`
	UserAgent    string    `json:"user_agent"`
	Timestamp    time.Time `json:"timestamp"`
	Severity     string    `json:"severity"` // low, medium, high, critical
}

// LicenseAnalytics provides business intelligence
type LicenseAnalytics struct {
	TotalLicenses    int `json:"total_licenses"`
	ActiveLicenses   int `json:"active_licenses"`
	TrialConversions int `json:"trial_conversions"`
	DailyActiveUsers int `json:"daily_active_users"`
	Revenue          struct {
		Monthly int64 `json:"monthly"`
		Total   int64 `json:"total"`
	} `json:"revenue"`
	TopFeatures []FeatureUsage `json:"top_features"`
}

type FeatureUsage struct {
	Feature string `json:"feature"`
	Count   int    `json:"count"`
}

// NewLicenseTracker creates a new license tracker with SQLite backend
func NewLicenseTracker(dbPath string) (*LicenseTracker, error) {
	db, err := sql.Open("sqlite", dbPath)
	if err != nil {
		return nil, fmt.Errorf("failed to open database: %w", err)
	}

	tracker := &LicenseTracker{
		db:             db,
		activationAPI:  "https://api.contextlite.com/v1/activate",
		deactivationAPI: "https://api.contextlite.com/v1/deactivate",
	}

	if err := tracker.initDatabase(); err != nil {
		return nil, fmt.Errorf("failed to initialize database: %w", err)
	}

	return tracker, nil
}

// initDatabase creates the necessary tables
func (lt *LicenseTracker) initDatabase() error {
	schema := `
	CREATE TABLE IF NOT EXISTS license_activations (
		id INTEGER PRIMARY KEY AUTOINCREMENT,
		license_key TEXT NOT NULL,
		email TEXT NOT NULL,
		hardware_id TEXT NOT NULL,
		activation_id TEXT UNIQUE NOT NULL,
		ip_address TEXT,
		user_agent TEXT,
		activated_at DATETIME NOT NULL,
		last_seen DATETIME NOT NULL,
		is_active BOOLEAN DEFAULT 1,
		activation_count INTEGER DEFAULT 1,
		max_activations INTEGER DEFAULT 3,
		customer_id TEXT,
		tier TEXT,
		UNIQUE(license_key, hardware_id)
	);

	CREATE TABLE IF NOT EXISTS usage_events (
		id INTEGER PRIMARY KEY AUTOINCREMENT,
		license_key TEXT NOT NULL,
		activation_id TEXT NOT NULL,
		event_type TEXT NOT NULL,
		timestamp DATETIME NOT NULL,
		metadata TEXT,
		ip_address TEXT,
		FOREIGN KEY(activation_id) REFERENCES license_activations(activation_id)
	);

	CREATE TABLE IF NOT EXISTS security_events (
		id INTEGER PRIMARY KEY AUTOINCREMENT,
		license_key TEXT,
		event_type TEXT NOT NULL,
		description TEXT,
		ip_address TEXT,
		user_agent TEXT,
		timestamp DATETIME NOT NULL,
		severity TEXT DEFAULT 'medium'
	);

	CREATE INDEX IF NOT EXISTS idx_activations_license ON license_activations(license_key);
	CREATE INDEX IF NOT EXISTS idx_activations_hardware ON license_activations(hardware_id);
	CREATE INDEX IF NOT EXISTS idx_usage_license ON usage_events(license_key);
	CREATE INDEX IF NOT EXISTS idx_security_timestamp ON security_events(timestamp);
	`

	_, err := lt.db.Exec(schema)
	return err
}

// ActivateLicense records a license activation with comprehensive tracking
func (lt *LicenseTracker) ActivateLicense(licenseKey, email, hardwareID, ipAddress, userAgent string, tier LicenseTier) (*LicenseActivation, error) {
	lt.mu.Lock()
	defer lt.mu.Unlock()
	
	// Generate unique activation ID
	activationID := lt.generateActivationID(licenseKey, hardwareID)

	// Check if already activated on this hardware
	existing, err := lt.getActivation(licenseKey, hardwareID)
	if err == nil && existing != nil && existing.IsActive {
		// Update last seen
		existing.LastSeen = time.Now()
		lt.updateLastSeen(existing.ActivationID)
		return existing, nil
	}

	// If we have a deactivated license on this hardware, reactivate it
	if err == nil && existing != nil && !existing.IsActive {
		err = lt.reactivateLicense(licenseKey, hardwareID)
		if err != nil {
			return nil, fmt.Errorf("failed to reactivate license: %w", err)
		}
		existing.IsActive = true
		existing.LastSeen = time.Now()
		return existing, nil
	}

	// Check activation limits
	activationCount, err := lt.getActivationCount(licenseKey)
	if err != nil {
		return nil, fmt.Errorf("failed to check activation count: %w", err)
	}

	maxActivations := lt.getMaxActivations(tier)
	if activationCount >= maxActivations {
		lt.recordSecurityEvent(licenseKey, "activation_limit_exceeded",
			fmt.Sprintf("License already activated on %d devices (max: %d)", activationCount, maxActivations),
			ipAddress, userAgent, "high")
		return nil, fmt.Errorf("license activation limit exceeded (%d/%d)", activationCount, maxActivations)
	}

	// Create new activation
	activation := &LicenseActivation{
		LicenseKey:      licenseKey,
		Email:          email,
		HardwareID:     hardwareID,
		ActivationID:   activationID,
		IPAddress:      ipAddress,
		UserAgent:      userAgent,
		ActivatedAt:    time.Now(),
		LastSeen:       time.Now(),
		IsActive:       true,
		ActivationCount: activationCount + 1,
		MaxActivations: maxActivations,
		Tier:           string(tier),
	}

	err = lt.saveActivation(activation)
	if err != nil {
		return nil, fmt.Errorf("failed to save activation: %w", err)
	}

	// Record usage event
	lt.recordUsageEvent(licenseKey, activationID, "license_activated", "", ipAddress)

	log.Printf("License activated: %s on hardware %s (activation %d/%d)",
		truncateString(licenseKey, 8)+"...", truncateString(hardwareID, 8)+"...", activationCount+1, maxActivations)

	return activation, nil
}

// RecordUsage tracks feature usage for analytics
func (lt *LicenseTracker) RecordUsage(licenseKey, activationID, eventType string, metadata map[string]interface{}, ipAddress string) error {
	metadataJSON := ""
	if metadata != nil {
		data, _ := json.Marshal(metadata)
		metadataJSON = string(data)
	}

	return lt.recordUsageEvent(licenseKey, activationID, eventType, metadataJSON, ipAddress)
}

// ValidateActivation checks if a license activation is valid and updates last seen
func (lt *LicenseTracker) ValidateActivation(licenseKey, hardwareID string) (*LicenseActivation, error) {
	lt.mu.RLock()
	defer lt.mu.RUnlock()
	
	activation, err := lt.getActivation(licenseKey, hardwareID)
	if err != nil {
		lt.recordSecurityEvent(licenseKey, "validation_failed",
			fmt.Sprintf("Failed to validate activation: %v", err), "", "", "medium")
		return nil, err
	}

	if activation == nil {
		lt.recordSecurityEvent(licenseKey, "unauthorized_access",
			"License not activated on this hardware", "", "", "high")
		return nil, fmt.Errorf("license not activated on this hardware")
	}

	if !activation.IsActive {
		lt.recordSecurityEvent(licenseKey, "inactive_license_access",
			"Attempted to use deactivated license", "", "", "high")
		return nil, fmt.Errorf("license has been deactivated")
	}

	// Update last seen
	lt.updateLastSeen(activation.ActivationID)

	return activation, nil
}

// DeactivateLicense removes a license activation
func (lt *LicenseTracker) DeactivateLicense(licenseKey, hardwareID string) error {
	lt.mu.Lock()
	defer lt.mu.Unlock()
	
	query := `UPDATE license_activations SET is_active = 0 WHERE license_key = ? AND hardware_id = ?`
	_, err := lt.db.Exec(query, licenseKey, hardwareID)
	if err != nil {
		return err
	}

	lt.recordUsageEvent(licenseKey, "", "license_deactivated", "", "")
	return nil
}

// reactivateLicense reactivates a previously deactivated license
func (lt *LicenseTracker) reactivateLicense(licenseKey, hardwareID string) error {
	query := `UPDATE license_activations SET is_active = 1, last_seen = CURRENT_TIMESTAMP WHERE license_key = ? AND hardware_id = ?`
	_, err := lt.db.Exec(query, licenseKey, hardwareID)
	if err != nil {
		return err
	}

	lt.recordUsageEvent(licenseKey, "", "license_reactivated", "", "")
	return nil
}

// GetAnalytics provides comprehensive business analytics
func (lt *LicenseTracker) GetAnalytics(days int) (*LicenseAnalytics, error) {
	since := time.Now().AddDate(0, 0, -days)

	analytics := &LicenseAnalytics{}

	// Total licenses
	err := lt.db.QueryRow(`SELECT COUNT(DISTINCT license_key) FROM license_activations`).Scan(&analytics.TotalLicenses)
	if err != nil {
		return nil, err
	}

	// Active licenses (seen in last 30 days)
	err = lt.db.QueryRow(`
		SELECT COUNT(DISTINCT license_key) 
		FROM license_activations 
		WHERE is_active = 1 AND last_seen > ?
	`, time.Now().AddDate(0, 0, -30)).Scan(&analytics.ActiveLicenses)
	if err != nil {
		return nil, err
	}

	// Daily active users
	err = lt.db.QueryRow(`
		SELECT COUNT(DISTINCT license_key) 
		FROM usage_events 
		WHERE timestamp > ?
	`, time.Now().AddDate(0, 0, -1)).Scan(&analytics.DailyActiveUsers)
	if err != nil {
		return nil, err
	}

	// Top features
	rows, err := lt.db.Query(`
		SELECT event_type, COUNT(*) as count 
		FROM usage_events 
		WHERE timestamp > ? 
		GROUP BY event_type 
		ORDER BY count DESC 
		LIMIT 10
	`, since)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	for rows.Next() {
		var feature FeatureUsage
		err := rows.Scan(&feature.Feature, &feature.Count)
		if err != nil {
			continue
		}
		analytics.TopFeatures = append(analytics.TopFeatures, feature)
	}

	return analytics, nil
}

// Helper methods

func (lt *LicenseTracker) generateActivationID(licenseKey, hardwareID string) string {
	data := fmt.Sprintf("%s:%s:%d", licenseKey, hardwareID, time.Now().UnixNano())
	hash := sha256.Sum256([]byte(data))
	return hex.EncodeToString(hash[:16])
}

func (lt *LicenseTracker) getMaxActivations(tier LicenseTier) int {
	switch tier {
	case TierDeveloper:
		return 1
	case TierPro:
		return 3
	case TierEnterprise:
		return 10
	default:
		return 1
	}
}

func (lt *LicenseTracker) getActivation(licenseKey, hardwareID string) (*LicenseActivation, error) {
	query := `
		SELECT id, license_key, email, hardware_id, activation_id, ip_address, 
		       user_agent, activated_at, last_seen, is_active, activation_count, 
		       max_activations, customer_id, tier
		FROM license_activations 
		WHERE license_key = ? AND hardware_id = ?
	`

	activation := &LicenseActivation{}
	err := lt.db.QueryRow(query, licenseKey, hardwareID).Scan(
		&activation.ID, &activation.LicenseKey, &activation.Email,
		&activation.HardwareID, &activation.ActivationID, &activation.IPAddress,
		&activation.UserAgent, &activation.ActivatedAt, &activation.LastSeen,
		&activation.IsActive, &activation.ActivationCount, &activation.MaxActivations,
		&activation.CustomerID, &activation.Tier,
	)

	if err == sql.ErrNoRows {
		return nil, nil
	}

	return activation, err
}

func (lt *LicenseTracker) getActivationCount(licenseKey string) (int, error) {
	var count int
	err := lt.db.QueryRow(`SELECT COUNT(*) FROM license_activations WHERE license_key = ? AND is_active = 1`, licenseKey).Scan(&count)
	return count, err
}

func (lt *LicenseTracker) saveActivation(activation *LicenseActivation) error {
	query := `
		INSERT INTO license_activations 
		(license_key, email, hardware_id, activation_id, ip_address, user_agent, 
		 activated_at, last_seen, is_active, activation_count, max_activations, 
		 customer_id, tier) 
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
	`

	_, err := lt.db.Exec(query,
		activation.LicenseKey, activation.Email, activation.HardwareID,
		activation.ActivationID, activation.IPAddress, activation.UserAgent,
		activation.ActivatedAt, activation.LastSeen, activation.IsActive,
		activation.ActivationCount, activation.MaxActivations,
		activation.CustomerID, activation.Tier,
	)

	return err
}

func (lt *LicenseTracker) updateLastSeen(activationID string) error {
	query := `UPDATE license_activations SET last_seen = ? WHERE activation_id = ?`
	_, err := lt.db.Exec(query, time.Now(), activationID)
	return err
}

func (lt *LicenseTracker) recordUsageEvent(licenseKey, activationID, eventType, metadata, ipAddress string) error {
	query := `
		INSERT INTO usage_events (license_key, activation_id, event_type, timestamp, metadata, ip_address)
		VALUES (?, ?, ?, ?, ?, ?)
	`

	_, err := lt.db.Exec(query, licenseKey, activationID, eventType, time.Now(), metadata, ipAddress)
	return err
}

func (lt *LicenseTracker) recordSecurityEvent(licenseKey, eventType, description, ipAddress, userAgent, severity string) error {
	query := `
		INSERT INTO security_events (license_key, event_type, description, ip_address, user_agent, timestamp, severity)
		VALUES (?, ?, ?, ?, ?, ?, ?)
	`

	_, err := lt.db.Exec(query, licenseKey, eventType, description, ipAddress, userAgent, time.Now(), severity)
	return err
}

// GetSecurityEvents returns recent security events for monitoring
func (lt *LicenseTracker) GetSecurityEvents(hours int) ([]SecurityEvent, error) {
	since := time.Now().Add(-time.Duration(hours) * time.Hour)
	query := `
		SELECT id, license_key, event_type, description, ip_address, user_agent, timestamp, severity
		FROM security_events 
		WHERE timestamp > ? 
		ORDER BY timestamp DESC
	`

	rows, err := lt.db.Query(query, since)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	var events []SecurityEvent
	for rows.Next() {
		var event SecurityEvent
		err := rows.Scan(&event.ID, &event.LicenseKey, &event.EventType,
			&event.Description, &event.IPAddress, &event.UserAgent,
			&event.Timestamp, &event.Severity)
		if err != nil {
			continue
		}
		events = append(events, event)
	}

	return events, nil
}

// Close closes the database connection
func (lt *LicenseTracker) Close() error {
	return lt.db.Close()
}
