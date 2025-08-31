// JWT authentication with multi-factor support for DOD compliance
package jwt

import (
	"crypto/rand"
	"encoding/hex"
	"errors"
	"fmt"
	"time"

	"github.com/golang-jwt/jwt/v5"
	"github.com/pquerna/otp/totp"
)

var (
	ErrInvalidToken   = errors.New("invalid token")
	ErrTokenExpired   = errors.New("token expired")
	ErrInvalidTOTP    = errors.New("invalid TOTP code")
	ErrAccountLocked  = errors.New("account locked due to failed attempts")
	ErrInsufficientClearance = errors.New("insufficient security clearance")
)

// JWTClaims represents the claims in a JWT token (CMMC IA-2)
type JWTClaims struct {
	UserID        string   `json:"user_id"`
	Roles         []string `json:"roles"`
	Clearance     string   `json:"clearance"`      // Security clearance level
	MFAVerified   bool     `json:"mfa_verified"`   // Multi-factor verification status
	CACVerified   bool     `json:"cac_verified"`   // CAC/PIV card verification
	LastActivity  int64    `json:"last_activity"`  // Last activity timestamp
	jwt.RegisteredClaims
}

// JWTAuthenticator handles JWT-based authentication (CMMC IA-2, IA-5)
type JWTAuthenticator struct {
	secret        []byte
	lockoutCount  map[string]int
	lastAttempt   map[string]time.Time
	maxAttempts   int
	lockoutPeriod time.Duration
}

// NewJWTAuthenticator creates a new JWT authenticator with FIPS-compliant secrets
func NewJWTAuthenticator() (*JWTAuthenticator, error) {
	secret := make([]byte, 64) // 512-bit secret for HMAC-SHA512
	if _, err := rand.Read(secret); err != nil {
		return nil, fmt.Errorf("failed to generate JWT secret: %w", err)
	}
	
	return &JWTAuthenticator{
		secret:        secret,
		lockoutCount:  make(map[string]int),
		lastAttempt:   make(map[string]time.Time),
		maxAttempts:   5,  // CMMC AC-7: Unsuccessful logon attempts
		lockoutPeriod: 30 * time.Minute, // 30-minute lockout
	}, nil
}

// GenerateToken creates a new JWT token for the user (CMMC IA-2)
func (j *JWTAuthenticator) GenerateToken(userID string, roles []string, clearance string) (string, error) {
	claims := &JWTClaims{
		UserID:       userID,
		Roles:        roles,
		Clearance:    clearance,
		MFAVerified:  false, // Must be verified separately
		CACVerified:  false, // CAC/PIV verification status
		LastActivity: time.Now().Unix(),
		RegisteredClaims: jwt.RegisteredClaims{
			ExpiresAt: jwt.NewNumericDate(time.Now().Add(1 * time.Hour)),   // Short initial expiry
			IssuedAt:  jwt.NewNumericDate(time.Now()),
			NotBefore: jwt.NewNumericDate(time.Now()),
			Issuer:    "contextlite-dod",
			Subject:   userID,
			ID:        generateTokenID(),
		},
	}
	
	token := jwt.NewWithClaims(jwt.SigningMethodHS512, claims)
	return token.SignedString(j.secret)
}

// ValidateToken validates and parses a JWT token (CMMC IA-2)
func (j *JWTAuthenticator) ValidateToken(tokenString string) (*JWTClaims, error) {
	token, err := jwt.ParseWithClaims(tokenString, &JWTClaims{}, func(token *jwt.Token) (interface{}, error) {
		// Ensure HMAC-SHA512 signing method
		if _, ok := token.Method.(*jwt.SigningMethodHMAC); !ok {
			return nil, fmt.Errorf("unexpected signing method: %v", token.Header["alg"])
		}
		return j.secret, nil
	})
	
	if err != nil {
		return nil, ErrInvalidToken
	}
	
	if claims, ok := token.Claims.(*JWTClaims); ok && token.Valid {
		// Check token expiration
		if time.Now().After(claims.ExpiresAt.Time) {
			return nil, ErrTokenExpired
		}
		
		// Check session timeout (AC-11, AC-12)
		lastActivity := time.Unix(claims.LastActivity, 0)
		if time.Since(lastActivity) > 2*time.Hour {
			return nil, ErrTokenExpired
		}
		
		return claims, nil
	}
	
	return nil, ErrInvalidToken
}

// VerifyTOTP verifies a TOTP code for multi-factor authentication (IA-5)
func (j *JWTAuthenticator) VerifyTOTP(userID, totpCode, secret string) error {
	// Check if account is locked (AC-7)
	if j.IsAccountLocked(userID) {
		return ErrAccountLocked
	}
	
	// Validate TOTP with current time
	valid := totp.Validate(totpCode, secret)
	
	if !valid {
		j.recordFailedAttempt(userID)
		return ErrInvalidTOTP
	}
	
	// Reset lockout count on successful verification
	j.lockoutCount[userID] = 0
	return nil
}

// UpdateMFAStatus updates the MFA verification status in a token
func (j *JWTAuthenticator) UpdateMFAStatus(tokenString string, mfaVerified, cacVerified bool) (string, error) {
	claims, err := j.ValidateToken(tokenString)
	if err != nil {
		return "", err
	}
	
	claims.MFAVerified = mfaVerified
	claims.CACVerified = cacVerified
	claims.LastActivity = time.Now().Unix()
	
	// Extend expiry for fully authenticated users
	if mfaVerified && cacVerified {
		claims.ExpiresAt = jwt.NewNumericDate(time.Now().Add(8 * time.Hour))
	} else if mfaVerified {
		claims.ExpiresAt = jwt.NewNumericDate(time.Now().Add(4 * time.Hour))
	}
	
	token := jwt.NewWithClaims(jwt.SigningMethodHS512, claims)
	return token.SignedString(j.secret)
}

// ValidateClearanceLevel checks if user has sufficient clearance (AC-3)
func (j *JWTAuthenticator) ValidateClearanceLevel(claims *JWTClaims, requiredClearance string) error {
	clearanceLevels := map[string]int{
		"UNCLASSIFIED": 1,
		"CUI":          2,
		"CONFIDENTIAL": 3,
		"SECRET":       4,
		"TOP_SECRET":   5,
	}
	
	userLevel, exists := clearanceLevels[claims.Clearance]
	if !exists {
		return ErrInsufficientClearance
	}
	
	requiredLevel, exists := clearanceLevels[requiredClearance]
	if !exists {
		return ErrInsufficientClearance
	}
	
	if userLevel < requiredLevel {
		return ErrInsufficientClearance
	}
	
	return nil
}

// IsAccountLocked checks if an account is locked due to failed attempts (AC-7)
func (j *JWTAuthenticator) IsAccountLocked(userID string) bool {
	count := j.lockoutCount[userID]
	lastAttempt := j.lastAttempt[userID]
	
	// Check if lockout period has expired
	if time.Since(lastAttempt) > j.lockoutPeriod {
		j.lockoutCount[userID] = 0
		return false
	}
	
	return count >= j.maxAttempts
}

// UnlockAccount manually unlocks an account (admin function)
func (j *JWTAuthenticator) UnlockAccount(userID string) {
	j.lockoutCount[userID] = 0
	delete(j.lastAttempt, userID)
}

// recordFailedAttempt records a failed authentication attempt
func (j *JWTAuthenticator) recordFailedAttempt(userID string) {
	j.lockoutCount[userID]++
	j.lastAttempt[userID] = time.Now()
}

// RefreshToken creates a new token with updated activity timestamp
func (j *JWTAuthenticator) RefreshToken(tokenString string) (string, error) {
	claims, err := j.ValidateToken(tokenString)
	if err != nil {
		return "", err
	}
	
	claims.LastActivity = time.Now().Unix()
	claims.ExpiresAt = jwt.NewNumericDate(time.Now().Add(8 * time.Hour))
	claims.ID = generateTokenID() // New token ID
	
	token := jwt.NewWithClaims(jwt.SigningMethodHS512, claims)
	return token.SignedString(j.secret)
}

// generateTokenID creates a unique token identifier
func generateTokenID() string {
	bytes := make([]byte, 16)
	rand.Read(bytes)
	return hex.EncodeToString(bytes)
}

// GetLockoutStatus returns the current lockout status for a user
func (j *JWTAuthenticator) GetLockoutStatus(userID string) (attempts int, locked bool, timeRemaining time.Duration) {
	attempts = j.lockoutCount[userID]
	locked = j.IsAccountLocked(userID)
	
	if locked {
		lastAttempt := j.lastAttempt[userID]
		timeRemaining = j.lockoutPeriod - time.Since(lastAttempt)
		if timeRemaining < 0 {
			timeRemaining = 0
		}
	}
	
	return
}
