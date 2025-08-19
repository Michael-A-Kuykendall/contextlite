package license

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"time"
)

// TrackedLicenseManager handles license validation with server-side tracking
type TrackedLicenseManager struct {
	*LicenseManager
	serverURL    string
	activationID string
	httpClient   *http.Client
}

// ActivationResponse represents the server response for license activation
type ActivationResponse struct {
	Success    bool                `json:"success"`
	Activation *LicenseActivation  `json:"activation,omitempty"`
	Error      string              `json:"error,omitempty"`
	Message    string              `json:"message,omitempty"`
}

// NewTrackedLicenseManager creates a license manager with server tracking
func NewTrackedLicenseManager(serverURL string) *TrackedLicenseManager {
	return &TrackedLicenseManager{
		LicenseManager: NewLicenseManager(),
		serverURL:      strings.TrimSuffix(serverURL, "/"),
		httpClient: &http.Client{
			Timeout: 30 * time.Second,
		},
	}
}

// LoadLicenseWithActivation loads license and activates it with the server
func (tlm *TrackedLicenseManager) LoadLicenseWithActivation(licensePath string) error {
	// First load and validate the license locally
	if err := tlm.LicenseManager.LoadLicense(licensePath); err != nil {
		return fmt.Errorf("local license validation failed: %w", err)
	}

	// Get hardware fingerprint
	hardwareID, err := getHardwareFingerprint()
	if err != nil {
		return fmt.Errorf("failed to get hardware fingerprint: %w", err)
	}

	// Activate with server
	activation, err := tlm.activateWithServer(tlm.license, hardwareID)
	if err != nil {
		return fmt.Errorf("server activation failed: %w", err)
	}

	tlm.activationID = activation.ActivationID

	// Record activation locally for offline verification
	if err := tlm.saveActivationRecord(activation); err != nil {
		// Don't fail if we can't save locally, just log
		fmt.Printf("Warning: failed to save activation record: %v\n", err)
	}

	return nil
}

// activateWithServer activates the license on the tracking server
func (tlm *TrackedLicenseManager) activateWithServer(license *License, hardwareID string) (*LicenseActivation, error) {
	payload := map[string]interface{}{
		"license_key": license.Key,
		"email":       license.Email,
		"hardware_id": hardwareID,
		"tier":        string(license.Tier),
	}

	jsonData, err := json.Marshal(payload)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal activation request: %w", err)
	}

	req, err := http.NewRequest("POST", tlm.serverURL+"/activate", bytes.NewBuffer(jsonData))
	if err != nil {
		return nil, fmt.Errorf("failed to create activation request: %w", err)
	}

	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("User-Agent", fmt.Sprintf("ContextLite/%s (%s; %s)", "1.0.0", runtime.GOOS, runtime.GOARCH))

	resp, err := tlm.httpClient.Do(req)
	if err != nil {
		return nil, fmt.Errorf("activation request failed: %w", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read activation response: %w", err)
	}

	var activationResp ActivationResponse
	if err := json.Unmarshal(body, &activationResp); err != nil {
		return nil, fmt.Errorf("failed to parse activation response: %w", err)
	}

	if !activationResp.Success {
		return nil, fmt.Errorf("activation failed: %s", activationResp.Error)
	}

	return activationResp.Activation, nil
}

// RecordUsage sends usage events to the tracking server
func (tlm *TrackedLicenseManager) RecordUsage(eventType string, metadata map[string]interface{}) error {
	if tlm.activationID == "" {
		// No activation ID means offline mode - skip tracking
		return nil
	}

	payload := map[string]interface{}{
		"license_key":   tlm.license.Key,
		"activation_id": tlm.activationID,
		"event_type":    eventType,
		"metadata":      metadata,
	}

	jsonData, err := json.Marshal(payload)
	if err != nil {
		return fmt.Errorf("failed to marshal usage event: %w", err)
	}

	req, err := http.NewRequest("POST", tlm.serverURL+"/usage", bytes.NewBuffer(jsonData))
	if err != nil {
		return fmt.Errorf("failed to create usage request: %w", err)
	}

	req.Header.Set("Content-Type", "application/json")

	// Send async to avoid blocking
	go func() {
		resp, err := tlm.httpClient.Do(req)
		if err != nil {
			// Silently ignore network errors for usage tracking
			return
		}
		resp.Body.Close()
	}()

	return nil
}

// ValidateWithServer performs online license validation
func (tlm *TrackedLicenseManager) ValidateWithServer() error {
	if tlm.license == nil {
		return fmt.Errorf("no license loaded")
	}

	hardwareID, err := getHardwareFingerprint()
	if err != nil {
		return fmt.Errorf("failed to get hardware fingerprint: %w", err)
	}

	// Try to load existing activation
	if tlm.activationID == "" {
		activation, err := tlm.loadActivationRecord()
		if err == nil && activation != nil {
			tlm.activationID = activation.ActivationID
		}
	}

	// For now, just record a validation event
	metadata := map[string]interface{}{
		"hardware_id": hardwareID,
		"validation_time": time.Now().Format(time.RFC3339),
	}

	return tlm.RecordUsage("license_validation", metadata)
}

// DeactivateFromServer deactivates the license on the server
func (tlm *TrackedLicenseManager) DeactivateFromServer() error {
	if tlm.license == nil {
		return fmt.Errorf("no license loaded")
	}

	hardwareID, err := getHardwareFingerprint()
	if err != nil {
		return fmt.Errorf("failed to get hardware fingerprint: %w", err)
	}

	payload := map[string]interface{}{
		"license_key": tlm.license.Key,
		"hardware_id": hardwareID,
	}

	jsonData, err := json.Marshal(payload)
	if err != nil {
		return fmt.Errorf("failed to marshal deactivation request: %w", err)
	}

	req, err := http.NewRequest("POST", tlm.serverURL+"/deactivate", bytes.NewBuffer(jsonData))
	if err != nil {
		return fmt.Errorf("failed to create deactivation request: %w", err)
	}

	req.Header.Set("Content-Type", "application/json")

	resp, err := tlm.httpClient.Do(req)
	if err != nil {
		return fmt.Errorf("deactivation request failed: %w", err)
	}
	defer resp.Body.Close()

	// Clear local activation record
	tlm.activationID = ""
	tlm.clearActivationRecord()

	return nil
}

// saveActivationRecord saves activation info locally for offline use
func (tlm *TrackedLicenseManager) saveActivationRecord(activation *LicenseActivation) error {
	homeDir, err := os.UserHomeDir()
	if err != nil {
		return err
	}

	contextDir := filepath.Join(homeDir, ".contextlite")
	os.MkdirAll(contextDir, 0755)

	activationPath := filepath.Join(contextDir, "activation.json")
	
	data, err := json.MarshalIndent(activation, "", "  ")
	if err != nil {
		return err
	}

	return os.WriteFile(activationPath, data, 0644)
}

// loadActivationRecord loads activation info from local storage
func (tlm *TrackedLicenseManager) loadActivationRecord() (*LicenseActivation, error) {
	homeDir, err := os.UserHomeDir()
	if err != nil {
		return nil, err
	}

	activationPath := filepath.Join(homeDir, ".contextlite", "activation.json")
	
	data, err := os.ReadFile(activationPath)
	if err != nil {
		return nil, err
	}

	var activation LicenseActivation
	if err := json.Unmarshal(data, &activation); err != nil {
		return nil, err
	}

	return &activation, nil
}

// clearActivationRecord removes local activation record
func (tlm *TrackedLicenseManager) clearActivationRecord() error {
	homeDir, err := os.UserHomeDir()
	if err != nil {
		return err
	}

	activationPath := filepath.Join(homeDir, ".contextlite", "activation.json")
	return os.Remove(activationPath)
}

// Enhanced feature gate with tracking integration
type TrackedFeatureGate struct {
	*EnhancedFeatureGate
	tracker *TrackedLicenseManager
}

// NewTrackedFeatureGate creates a feature gate with usage tracking
func NewTrackedFeatureGate(serverURL string) *TrackedFeatureGate {
	enhancedGate := NewEnhancedFeatureGate()
	tracker := NewTrackedLicenseManager(serverURL)
	
	// Try to load license with activation
	licenseLocations := []string{
		"license.json",
		"contextlite-license.json",
		filepath.Join(os.Getenv("HOME"), ".contextlite", "license.json"),
		filepath.Join(os.Getenv("USERPROFILE"), ".contextlite", "license.json"),
	}
	
	for _, location := range licenseLocations {
		if err := tracker.LoadLicenseWithActivation(location); err == nil {
			break
		}
	}
	
	return &TrackedFeatureGate{
		EnhancedFeatureGate: enhancedGate,
		tracker:             tracker,
	}
}

// RequireFeature with usage tracking
func (tfg *TrackedFeatureGate) RequireFeature(feature string) error {
	// Record feature usage attempt
	metadata := map[string]interface{}{
		"feature": feature,
		"tier":    tfg.GetTier(),
		"allowed": tfg.IsEnabled(feature),
	}
	
	tfg.tracker.RecordUsage("feature_request", metadata)
	
	// Call parent implementation
	return tfg.EnhancedFeatureGate.RequireFeature(feature)
}

// TrackStartup records application startup event
func (tfg *TrackedFeatureGate) TrackStartup() {
	metadata := map[string]interface{}{
		"version": "1.0.0",
		"os":      runtime.GOOS,
		"arch":    runtime.GOARCH,
		"tier":    tfg.GetTier(),
	}
	
	tfg.tracker.RecordUsage("app_startup", metadata)
}

// TrackQuery records context query events
func (tfg *TrackedFeatureGate) TrackQuery(queryType string, duration time.Duration, resultCount int) {
	metadata := map[string]interface{}{
		"query_type":   queryType,
		"duration_ms":  duration.Milliseconds(),
		"result_count": resultCount,
		"tier":         tfg.GetTier(),
	}
	
	tfg.tracker.RecordUsage("context_query", metadata)
}

// TrackError records error events for debugging
func (tfg *TrackedFeatureGate) TrackError(errorType string, errorMessage string) {
	metadata := map[string]interface{}{
		"error_type":    errorType,
		"error_message": errorMessage,
		"tier":          tfg.GetTier(),
	}
	
	tfg.tracker.RecordUsage("error_event", metadata)
}

// GetActivationID returns the current activation ID for debugging
func (tfg *TrackedFeatureGate) GetActivationID() string {
	return tfg.tracker.activationID
}

// ValidateOnline performs online license validation
func (tfg *TrackedFeatureGate) ValidateOnline() error {
	return tfg.tracker.ValidateWithServer()
}
