package license

import (
	"crypto"
	"crypto/rand"
	"crypto/rsa"
	"crypto/sha256"
	"crypto/x509"
	"encoding/base64"
	"encoding/json"
	"encoding/pem"
	"fmt"
	mathrand "math/rand"
	"net"
	"os"
	"path/filepath"
	"runtime"
	"time"

	"github.com/denisbrodbeck/machineid"
)

// LicenseTier represents the license level
type LicenseTier string

const (
	TierDeveloper  LicenseTier = "developer"
	TierPro        LicenseTier = "professional"
	TierEnterprise LicenseTier = "enterprise"
)

// License represents a software license
type License struct {
	Key          string      `json:"key"`
	Email        string      `json:"email"`
	Tier         LicenseTier `json:"tier"`
	IssuedAt     time.Time   `json:"issued_at"`
	ExpiresAt    *time.Time  `json:"expires_at,omitempty"` // nil for perpetual
	MaxDocuments int         `json:"max_documents"`
	MaxUsers     int         `json:"max_users"`
	Features     []string    `json:"features"`
	HardwareID   string      `json:"hardware_id"`
	Signature    string      `json:"signature"`
}

// LicenseManager handles license validation and enforcement
type LicenseManager struct {
	publicKey  *rsa.PublicKey
	license    *License
	lastCheck  time.Time
	gracePeriod time.Duration
}

// NewLicenseManager creates a new license manager
func NewLicenseManager() *LicenseManager {
	return &LicenseManager{
		publicKey:   getPublicKey(),
		gracePeriod: 14 * 24 * time.Hour, // 14 days
	}
}

// LoadLicense loads and validates a license from file
func (lm *LicenseManager) LoadLicense(licensePath string) error {
	data, err := os.ReadFile(licensePath)
	if err != nil {
		return fmt.Errorf("failed to read license file: %w", err)
	}

	var license License
	if err := json.Unmarshal(data, &license); err != nil {
		return fmt.Errorf("failed to parse license: %w", err)
	}

	if err := lm.validateLicense(&license); err != nil {
		return fmt.Errorf("license validation failed: %w", err)
	}

	lm.license = &license
	lm.lastCheck = time.Now()
	return nil
}

// validateLicense performs comprehensive license validation
func (lm *LicenseManager) validateLicense(license *License) error {
	// 1. Verify signature
	if err := lm.verifySignature(license); err != nil {
		return fmt.Errorf("signature verification failed: %w", err)
	}

	// 2. Check hardware binding
	currentHW, err := getHardwareFingerprint()
	if err != nil {
		return fmt.Errorf("failed to get hardware fingerprint: %w", err)
	}

	if license.HardwareID != "" && license.HardwareID != currentHW {
		return fmt.Errorf("license is bound to different hardware")
	}

	// 3. Check expiration
	if license.ExpiresAt != nil && time.Now().After(*license.ExpiresAt) {
		return fmt.Errorf("license has expired")
	}

	// 4. Validate tier-specific limits
	if err := lm.validateTierLimits(license); err != nil {
		return fmt.Errorf("tier validation failed: %w", err)
	}

	return nil
}

// verifySignature verifies the license signature
func (lm *LicenseManager) verifySignature(license *License) error {
	// Create verification payload (excluding signature)
	payload := fmt.Sprintf("%s:%s:%s:%d:%d:%d:%s",
		license.Key, license.Email, license.Tier,
		license.IssuedAt.Unix(), license.MaxDocuments,
		license.MaxUsers, license.HardwareID)

	// Decode signature
	signature, err := base64.StdEncoding.DecodeString(license.Signature)
	if err != nil {
		return fmt.Errorf("invalid signature encoding: %w", err)
	}

	// Hash payload
	hash := sha256.Sum256([]byte(payload))

	// Verify signature
	err = rsa.VerifyPKCS1v15(lm.publicKey, crypto.SHA256, hash[:], signature)
	if err != nil {
		return fmt.Errorf("signature verification failed: %w", err)
	}

	return nil
}

// validateTierLimits enforces tier-specific limitations
func (lm *LicenseManager) validateTierLimits(license *License) error {
	switch license.Tier {
	case TierDeveloper:
		if license.MaxDocuments > 10000 {
			return fmt.Errorf("developer tier limited to 10,000 documents")
		}
		if license.MaxUsers > 1 {
			return fmt.Errorf("developer tier limited to single user")
		}
	case TierPro:
		if license.MaxDocuments > 0 && license.MaxDocuments < 10001 {
			return fmt.Errorf("professional tier requires unlimited documents")
		}
		if license.MaxUsers > 10 {
			return fmt.Errorf("professional tier limited to 10 users")
		}
	case TierEnterprise:
		// Enterprise has no limits
	default:
		return fmt.Errorf("unknown license tier: %s", license.Tier)
	}
	return nil
}

// GetFeatures returns available features for current license
func (lm *LicenseManager) GetFeatures() []string {
	if lm.license == nil {
		return getDeveloperFeatures()
	}

	switch lm.license.Tier {
	case TierDeveloper:
		return getDeveloperFeatures()
	case TierPro:
		return getProFeatures()
	case TierEnterprise:
		return getEnterpriseFeatures()
	default:
		return getDeveloperFeatures()
	}
}

// HasFeature checks if a specific feature is available
func (lm *LicenseManager) HasFeature(feature string) bool {
	features := lm.GetFeatures()
	for _, f := range features {
		if f == feature {
			return true
		}
	}
	return false
}

// IsInGracePeriod checks if we're in the grace period for unlicensed usage
func (lm *LicenseManager) IsInGracePeriod() bool {
	if lm.license != nil {
		return false // Licensed, no grace period needed
	}

	// Check if first run file exists
	firstRunPath := getFirstRunPath()
	if _, err := os.Stat(firstRunPath); os.IsNotExist(err) {
		// Create first run marker
		os.WriteFile(firstRunPath, []byte(time.Now().Format(time.RFC3339)), 0644)
		return true
	}

	// Read first run time
	data, err := os.ReadFile(firstRunPath)
	if err != nil {
		return false
	}

	firstRun, err := time.Parse(time.RFC3339, string(data))
	if err != nil {
		return false
	}

	return time.Since(firstRun) < lm.gracePeriod
}

// GetMaxDocuments returns document limit for current license
func (lm *LicenseManager) GetMaxDocuments() int {
	if lm.license == nil {
		if lm.IsInGracePeriod() {
			return 10000 // Grace period allows developer limits
		}
		return 1000 // Unlicensed severely limited
	}
	return lm.license.MaxDocuments
}

// GetTier returns the current license tier
func (lm *LicenseManager) GetTier() LicenseTier {
	if lm.license == nil {
		if lm.IsInGracePeriod() {
			return TierDeveloper // Grace period gets developer features
		}
		return TierDeveloper // Default to most restrictive
	}
	return lm.license.Tier
}

// Feature definitions
func getDeveloperFeatures() []string {
	return []string{
		"basic_search",
		"rest_api",
		"sqlite_storage",
		"single_workspace",
	}
}

func getProFeatures() []string {
	features := getDeveloperFeatures()
	return append(features,
		"unlimited_workspaces",
		"advanced_smt",
		"7d_scoring",
		"caching",
		"priority_support",
	)
}

func getEnterpriseFeatures() []string {
	features := getProFeatures()
	return append(features,
		"multi_tenant",
		"sso_ldap",
		"custom_mcp",
		"white_label",
		"source_access",
		"sla_support",
		"custom_integrations",
		"team_deployment",
		"on_premise",
		"analytics",
		"audit_trails",
		"compliance_reporting",
	)
}

// Hardware fingerprinting
func getHardwareFingerprint() (string, error) {
	// Get machine ID (cross-platform)
	machineID, err := machineid.ID()
	if err != nil {
		return "", err
	}

	// Get additional hardware info
	hostname, _ := os.Hostname()
	
	// Get primary network interface MAC
	interfaces, err := net.Interfaces()
	var mac string
	if err == nil {
		for _, iface := range interfaces {
			if iface.Flags&net.FlagUp != 0 && iface.Flags&net.FlagLoopback == 0 {
				mac = iface.HardwareAddr.String()
				break
			}
		}
	}

	// Combine for fingerprint
	combined := fmt.Sprintf("%s:%s:%s:%s", machineID, hostname, mac, runtime.GOOS)
	hash := sha256.Sum256([]byte(combined))
	return base64.StdEncoding.EncodeToString(hash[:]), nil
}

func getFirstRunPath() string {
	homeDir, _ := os.UserHomeDir()
	return fmt.Sprintf("%s/.contextlite_first_run", homeDir)
}

// Embedded public key for license verification
func getPublicKey() *rsa.PublicKey {
	// Production RSA public key for license verification
pubKeyPEM := `-----BEGIN PUBLIC KEY-----
MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAzoehpns722oiWSXLiVMd
Q412F/nO5EIraHXlbcPI7nF0BLu4F7TNP4U5qUhOkIjQr50OWvBQoxw8Nn7HfYdR
HJAmPmLJn7FLiNz+AuFw9+c8vVjmkfqTt1cmGjZ7Tzb0sFJTzCH4l86MYsh5/Rc0
5RhOJ08yql6jSLYs/GeWhh0CgWRvmd1ZMpfZcwPAslcG4JP6hY0pOiO6/dLwoxOV
17R+FR7/CDGHiYCLJ4jk7yVHAF9NBrZu4KpxzP6Dn8fhrArRnyOhaJaXLFDGD36w
pPm32QZ1R6AQjnPFHBL3qGCznguNUvkWCLTYN15BXU90A87cMufYMAAdjERAveps
FQIDAQAB
-----END PUBLIC KEY-----`

	block, _ := pem.Decode([]byte(pubKeyPEM))
	if block == nil {
		panic("failed to parse public key PEM")
	}

	pub, err := x509.ParsePKIXPublicKey(block.Bytes)
	if err != nil {
		panic(fmt.Sprintf("failed to parse public key: %v", err))
	}

	return pub.(*rsa.PublicKey)
}

// License generation (for your license server)
func GenerateBasicLicense(email string, tier LicenseTier, hardwareID string, privateKey *rsa.PrivateKey) (*License, error) {
	license := &License{
		Key:          generateLicenseKey(),
		Email:        email,
		Tier:         tier,
		IssuedAt:     time.Now(),
		HardwareID:   hardwareID,
	}

	// Set tier-specific limits
	switch tier {
	case TierDeveloper:
		license.MaxDocuments = 10000
		license.MaxUsers = 1
		license.Features = getDeveloperFeatures()
	case TierPro:
		license.MaxDocuments = 0 // 0 = unlimited
		license.MaxUsers = 10
		license.Features = getProFeatures()
	case TierEnterprise:
		license.MaxDocuments = 0 // unlimited
		license.MaxUsers = 0 // unlimited
		license.Features = getEnterpriseFeatures()
	}

	// Generate signature
	payload := fmt.Sprintf("%s:%s:%s:%d:%d:%d:%s",
		license.Key, license.Email, license.Tier,
		license.IssuedAt.Unix(), license.MaxDocuments,
		license.MaxUsers, license.HardwareID)

	hash := sha256.Sum256([]byte(payload))
	signature, err := rsa.SignPKCS1v15(rand.Reader, privateKey, crypto.SHA256, hash[:])
	if err != nil {
		return nil, fmt.Errorf("failed to sign license: %w", err)
	}

	license.Signature = base64.StdEncoding.EncodeToString(signature)
	return license, nil
}

func generateLicenseKey() string {
	// Generate a readable license key (XXXX-XXXX-XXXX-XXXX format)
	chars := "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
	key := make([]byte, 19) // 16 chars + 3 dashes
	
	for i := 0; i < 4; i++ {
		for j := 0; j < 4; j++ {
			key[i*5+j] = chars[mathrand.Intn(len(chars))]
		}
		if i < 3 {
			key[i*5+4] = '-'
		}
	}
	
	return string(key)
}

// GenerateLicense creates a new signed license for the given parameters
func GenerateLicense(email string, tier LicenseTier, hardwareID string, privateKey *rsa.PrivateKey) (string, error) {
	now := time.Now()
	
	// Create license data
	license := &License{
		Key:         generateLicenseKey(),
		Email:       email,
		Tier:        tier,
		IssuedAt:    now,
		ExpiresAt:   &[]time.Time{now.AddDate(1, 0, 0)}[0], // 1 year expiration
		HardwareID:  hardwareID,
		Features:    getDefaultFeatures(tier),
	}
	
	// Set tier-specific limits
	switch tier {
	case TierDeveloper:
		license.MaxDocuments = 1000
		license.MaxUsers = 1
	case TierPro:
		license.MaxDocuments = 100000
		license.MaxUsers = 10
	case TierEnterprise:
		license.MaxDocuments = 0 // unlimited
		license.MaxUsers = 0     // unlimited
	}
	
	// Generate signature
	payload := fmt.Sprintf("%s:%s:%s:%d:%d:%d:%s",
		license.Key, license.Email, license.Tier,
		license.IssuedAt.Unix(), license.MaxDocuments,
		license.MaxUsers, license.HardwareID)

	hash := sha256.Sum256([]byte(payload))
	signature, err := rsa.SignPKCS1v15(rand.Reader, privateKey, crypto.SHA256, hash[:])
	if err != nil {
		return "", fmt.Errorf("failed to sign license: %w", err)
	}

	license.Signature = base64.StdEncoding.EncodeToString(signature)
	
	// Convert license to JSON and encode as base64 for transport
	licenseJSON, err := json.Marshal(license)
	if err != nil {
		return "", fmt.Errorf("failed to marshal license: %w", err)
	}
	
	return base64.StdEncoding.EncodeToString(licenseJSON), nil
}

// getDefaultFeatures returns default features for a given tier
func getDefaultFeatures(tier LicenseTier) []string {
	switch tier {
	case TierDeveloper:
		return getDeveloperFeatures()
	case TierPro:
		return getProFeatures()
	case TierEnterprise:
		return getEnterpriseFeatures()
	default:
		return getDeveloperFeatures()
	}
}

// LicenseFeatureGate implements the FeatureGate interface
type LicenseFeatureGate struct {
	tier LicenseTier
}

// NewFeatureGate creates a new feature gate based on current license
func NewFeatureGate() *LicenseFeatureGate {
	// Try to load license from common locations
	licenseLocations := []string{
		"license.json",
		"contextlite-license.json",
		filepath.Join(os.Getenv("HOME"), ".contextlite", "license.json"),
		filepath.Join(os.Getenv("USERPROFILE"), ".contextlite", "license.json"),
	}
	
	lm := NewLicenseManager()
	for _, location := range licenseLocations {
		if err := lm.LoadLicense(location); err == nil {
			return &LicenseFeatureGate{
				tier: lm.GetTier(),
			}
		}
	}
	
	// No license found - default to developer tier
	return &LicenseFeatureGate{
		tier: TierDeveloper,
	}
}

// IsEnabled checks if a feature is enabled for current license
func (fg *LicenseFeatureGate) IsEnabled(feature string) bool {
	features := getDefaultFeatures(fg.tier)
	for _, f := range features {
		if f == feature {
			return true
		}
	}
	return false
}

// RequireFeature returns error if feature not available
func (fg *LicenseFeatureGate) RequireFeature(feature string) error {
	if !fg.IsEnabled(feature) {
		return fmt.Errorf("feature '%s' requires %s license or higher", feature, TierPro)
	}
	return nil
}

// RequireProfessional ensures Professional+ license
func (fg *LicenseFeatureGate) RequireProfessional() error {
	if fg.tier == TierDeveloper {
		return fmt.Errorf("this feature requires Professional license or higher")
	}
	return nil
}

// RequireEnterprise ensures Enterprise license
func (fg *LicenseFeatureGate) RequireEnterprise() error {
	if fg.tier != TierEnterprise {
		return fmt.Errorf("this feature requires Enterprise license")
	}
	return nil
}

// GetTier returns current license tier
func (fg *LicenseFeatureGate) GetTier() string {
	return string(fg.tier)
}

// ValidateCustomMCP validates custom MCP feature access
func (fg *LicenseFeatureGate) ValidateCustomMCP() error {
	return fg.RequireEnterprise()
}

// ValidateMultiTenant validates multi-tenant feature access  
func (fg *LicenseFeatureGate) ValidateMultiTenant() error {
	return fg.RequireEnterprise()
}

// ValidateLicense validates a license string using RSA public key verification
func ValidateLicense(licenseString string, publicKey *rsa.PublicKey) (bool, error) {
	// Parse the license JSON
	var license License
	if err := json.Unmarshal([]byte(licenseString), &license); err != nil {
		return false, fmt.Errorf("invalid license JSON: %w", err)
	}
	
	// Create verification payload (excluding signature)
	licenseData := map[string]interface{}{
		"key":           license.Key,
		"email":         license.Email,
		"tier":          license.Tier,
		"issued_at":     license.IssuedAt,
		"expires_at":    license.ExpiresAt,
		"max_documents": license.MaxDocuments,
		"max_users":     license.MaxUsers,
		"hardware_id":   license.HardwareID,
		"features":      license.Features,
	}
	
	// Create hash of license data
	dataBytes, _ := json.Marshal(licenseData)
	hash := sha256.Sum256(dataBytes)
	
	// Decode signature
	signature, err := base64.StdEncoding.DecodeString(license.Signature)
	if err != nil {
		return false, fmt.Errorf("invalid signature encoding: %w", err)
	}
	
	// Verify signature
	err = rsa.VerifyPKCS1v15(publicKey, crypto.SHA256, hash[:], signature)
	if err != nil {
		return false, fmt.Errorf("signature verification failed: %w", err)
	}
	
	// Check expiration
	if license.ExpiresAt != nil && time.Now().After(*license.ExpiresAt) {
		return false, fmt.Errorf("license expired on %v", *license.ExpiresAt)
	}
	
	return true, nil
}
