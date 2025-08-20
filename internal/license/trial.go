package license

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"time"
)

// TrialStatus represents the current trial state
type TrialStatus string

const (
	TrialStatusActive  TrialStatus = "active"
	TrialStatusExpired TrialStatus = "expired"
	TrialStatusNew     TrialStatus = "new"
)

// TrialManager handles 14-day trial tracking
type TrialManager struct {
	trialFile string
	hwID      string
}

// TrialInfo contains trial tracking data
type TrialInfo struct {
	StartDate     time.Time `json:"start_date"`
	HardwareID    string    `json:"hardware_id"`
	InstallID     string    `json:"install_id"`
	TrialDays     int       `json:"trial_days"`
	ExpiresAt     time.Time `json:"expires_at"`
	FirstRun      bool      `json:"first_run"`
	UsageCount    int       `json:"usage_count"`
}

// NewTrialManager creates a new trial manager
func NewTrialManager() *TrialManager {
	homeDir, _ := os.UserHomeDir()
	contextDir := filepath.Join(homeDir, ".contextlite")
	os.MkdirAll(contextDir, 0755)
	
	trialPath := filepath.Join(contextDir, "trial.json")
	
	hwID, _ := getHardwareFingerprint()
	
	return &TrialManager{
		trialFile: trialPath,
		hwID:      hwID,
	}
}

// StartOrGetTrial initializes or retrieves existing trial
func (tm *TrialManager) StartOrGetTrial() (*TrialInfo, error) {
	// Check if trial exists
	if trial, err := tm.loadExistingTrial(); err == nil {
		// Validate hardware binding
		if trial.HardwareID != tm.hwID {
			return nil, fmt.Errorf("trial is bound to different hardware")
		}
		
		// Increment usage count
		trial.UsageCount++
		tm.saveTrial(trial)
		
		return trial, nil
	}
	
	// Start new trial
	trial := &TrialInfo{
		StartDate:  time.Now(),
		HardwareID: tm.hwID,
		InstallID:  tm.generateInstallID(),
		TrialDays:  14,
		ExpiresAt:  time.Now().AddDate(0, 0, 14),
		FirstRun:   true,
		UsageCount: 1,
	}
	
	if err := tm.saveTrial(trial); err != nil {
		return nil, fmt.Errorf("failed to save trial info: %w", err)
	}
	
	return trial, nil
}

// GetTrialStatus returns current trial status
func (tm *TrialManager) GetTrialStatus() (TrialStatus, *TrialInfo, error) {
	trial, err := tm.loadExistingTrial()
	if err != nil {
		return TrialStatusNew, nil, nil
	}
	
	// Validate hardware binding
	if trial.HardwareID != tm.hwID {
		return TrialStatusExpired, trial, fmt.Errorf("trial bound to different hardware")
	}
	
	if time.Now().After(trial.ExpiresAt) {
		return TrialStatusExpired, trial, nil
	}
	
	return TrialStatusActive, trial, nil
}

// IsTrialActive checks if trial is currently active
func (tm *TrialManager) IsTrialActive() bool {
	status, _, _ := tm.GetTrialStatus()
	return status == TrialStatusActive || status == TrialStatusNew
}

// DaysRemaining returns days left in trial
func (tm *TrialManager) DaysRemaining() int {
	trial, err := tm.loadExistingTrial()
	if err != nil {
		return 14 // New installation
	}
	
	remaining := time.Until(trial.ExpiresAt).Hours() / 24
	if remaining < 0 {
		return 0
	}
	return int(remaining)
}

// GetTrialInfo returns detailed trial information
func (tm *TrialManager) GetTrialInfo() map[string]interface{} {
	status, trial, err := tm.GetTrialStatus()
	
	info := map[string]interface{}{
		"status":      string(status),
		"is_active":   status == TrialStatusActive || status == TrialStatusNew,
		"days_total":  14,
	}
	
	if err != nil {
		info["error"] = err.Error()
		info["days_remaining"] = 0
		return info
	}
	
	if trial != nil {
		info["days_remaining"] = tm.DaysRemaining()
		info["start_date"] = trial.StartDate.Format("2006-01-02")
		info["expires_at"] = trial.ExpiresAt.Format("2006-01-02")
		info["usage_count"] = trial.UsageCount
		info["first_run"] = trial.FirstRun
		info["install_id"] = trial.InstallID[:8] + "..." // Partial ID for privacy
	} else {
		info["days_remaining"] = 14
	}
	
	return info
}

// loadExistingTrial loads trial data from disk
func (tm *TrialManager) loadExistingTrial() (*TrialInfo, error) {
	data, err := os.ReadFile(tm.trialFile)
	if err != nil {
		return nil, err
	}
	
	var trial TrialInfo
	if err := json.Unmarshal(data, &trial); err != nil {
		return nil, err
	}
	
	return &trial, nil
}

// saveTrial saves trial data to disk
func (tm *TrialManager) saveTrial(trial *TrialInfo) error {
	data, err := json.MarshalIndent(trial, "", "  ")
	if err != nil {
		return err
	}
	
	return os.WriteFile(tm.trialFile, data, 0644)
}

// generateInstallID creates a unique installation identifier
func (tm *TrialManager) generateInstallID() string {
	timestamp := time.Now().Unix()
	combined := fmt.Sprintf("%s:%d:%s", tm.hwID, timestamp, "contextlite-trial")
	hash := sha256.Sum256([]byte(combined))
	return hex.EncodeToString(hash[:16])
}

// LicenseFeatureGate with trial support
type EnhancedFeatureGate struct {
	tier         LicenseTier
	status       string
	message      string
	trialManager *TrialManager
	license      *License
}

// NewEnhancedFeatureGate creates feature gate with trial support
func NewEnhancedFeatureGate() *EnhancedFeatureGate {
	trialMgr := NewTrialManager()
	
	// 1. Check for valid license first
	licenseLocations := []string{
		"license.json",
		"contextlite-license.json",
		filepath.Join(os.Getenv("HOME"), ".contextlite", "license.json"),
		filepath.Join(os.Getenv("USERPROFILE"), ".contextlite", "license.json"),
	}
	
	lm := NewLicenseManager()
	for _, location := range licenseLocations {
		if err := lm.LoadLicense(location); err == nil {
			return &EnhancedFeatureGate{
				tier:    lm.GetTier(),
				status:  "licensed",
				message: fmt.Sprintf("Licensed: %s", lm.GetTier()),
				license: lm.license,
			}
		}
	}
	
	// 2. Check trial status
	trialStatus, _, err := trialMgr.GetTrialStatus()
	
	if err != nil && trialStatus != TrialStatusNew {
		return &EnhancedFeatureGate{
			tier:         TierDeveloper,
			status:       "error",
			message:      fmt.Sprintf("Trial error: %v", err),
			trialManager: trialMgr,
		}
	}
	
	switch trialStatus {
	case TrialStatusNew:
		// Start new trial
		if _, err := trialMgr.StartOrGetTrial(); err != nil {
			return &EnhancedFeatureGate{
				tier:         TierDeveloper,
				status:       "error",
				message:      "Failed to start trial",
				trialManager: trialMgr,
			}
		}
		return &EnhancedFeatureGate{
			tier:         TierPro, // Full features during trial!
			status:       "trial_started",
			message:      "Trial started: 14 days of full features",
			trialManager: trialMgr,
		}
		
	case TrialStatusActive:
		remaining := trialMgr.DaysRemaining()
		return &EnhancedFeatureGate{
			tier:         TierPro, // Full features during trial!
			status:       "trial_active",
			message:      fmt.Sprintf("Trial active: %d days remaining", remaining),
			trialManager: trialMgr,
		}
		
	case TrialStatusExpired:
		return &EnhancedFeatureGate{
			tier:         TierDeveloper, // Fallback to limited features
			status:       "trial_expired",
			message:      "Trial expired. Purchase license to continue with full features.",
			trialManager: trialMgr,
		}
	}
	
	// Fallback
	return &EnhancedFeatureGate{
		tier:         TierDeveloper,
		status:       "unknown",
		message:      "Unknown license state",
		trialManager: trialMgr,
	}
}

// GetTier returns current access tier
func (fg *EnhancedFeatureGate) GetTier() string {
	return string(fg.tier)
}

// GetStatus returns detailed status information
func (fg *EnhancedFeatureGate) GetStatus() map[string]interface{} {
	status := map[string]interface{}{
		"tier":    string(fg.tier),
		"status":  fg.status,
		"message": fg.message,
	}
	
	if fg.trialManager != nil {
		trialInfo := fg.trialManager.GetTrialInfo()
		status["trial"] = trialInfo
	}
	
	if fg.license != nil {
		status["license"] = map[string]interface{}{
			"email":        fg.license.Email,
			"issued_at":    fg.license.IssuedAt.Format("2006-01-02"),
			"max_documents": fg.license.MaxDocuments,
			"features":     fg.license.Features,
		}
	}
	
	return status
}

// TrialDaysRemaining returns days left in trial (0 if no trial)
func (fg *EnhancedFeatureGate) TrialDaysRemaining() int {
	if fg.trialManager == nil {
		return 0
	}
	return fg.trialManager.DaysRemaining()
}

// IsEnabled checks if a feature is available
func (fg *EnhancedFeatureGate) IsEnabled(feature string) bool {
	features := getDefaultFeatures(fg.tier)
	for _, f := range features {
		if f == feature {
			return true
		}
	}
	return false
}

// RequireFeature returns error if feature not available
func (fg *EnhancedFeatureGate) RequireFeature(feature string) error {
	if !fg.IsEnabled(feature) {
		if fg.status == "trial_expired" {
			return fmt.Errorf("feature '%s' requires active license (trial expired)", feature)
		}
		return fmt.Errorf("feature '%s' requires %s license or higher", feature, TierPro)
	}
	return nil
}

// RequireProfessional ensures Professional+ license
func (fg *EnhancedFeatureGate) RequireProfessional() error {
	if fg.tier == TierDeveloper && fg.status == "trial_expired" {
		return fmt.Errorf("this feature requires Professional license or higher (trial expired)")
	}
	if fg.tier == TierDeveloper && fg.status != "trial_active" && fg.status != "trial_started" {
		return fmt.Errorf("this feature requires Professional license or higher")
	}
	return nil
}

// RequireEnterprise ensures Enterprise license
func (fg *EnhancedFeatureGate) RequireEnterprise() error {
	if fg.tier != TierEnterprise {
		return fmt.Errorf("this feature requires Enterprise license")
	}
	return nil
}

// ValidateCustomMCP validates custom MCP feature access
func (fg *EnhancedFeatureGate) ValidateCustomMCP() error {
	return fg.RequireEnterprise()
}

// ValidateMultiTenant validates multi-tenant feature access  
func (fg *EnhancedFeatureGate) ValidateMultiTenant() error {
	return fg.RequireEnterprise()
}

// CheckAccess validates access to system features
func (fg *EnhancedFeatureGate) CheckAccess(operation string) error {
	switch fg.status {
	case "trial_expired":
		return fmt.Errorf("trial expired - purchase license to continue: https://contextlite.com/purchase")
	case "error":
		return fmt.Errorf("license validation error: %s", fg.message)
	case "licensed", "trial_active", "trial_started":
		return nil // Full access
	default:
		return nil // Allow access for unknown states (graceful degradation)
	}
}
