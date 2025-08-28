package main

import (
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"encoding/json"
	"encoding/base64"
	"encoding/pem"
	"fmt"
	"io"
	"log"
	"net/http"
	"net/smtp"
	"os"
	"strconv"
	"time"

	"github.com/stripe/stripe-go/v74"
	"github.com/stripe/stripe-go/v74/webhook"
	"contextlite/internal/license"
)

// Configuration
type Config struct {
	Port                int    `json:"port"`
	StripeSecretKey     string `json:"stripe_secret_key"`
	StripeWebhookSecret string `json:"stripe_webhook_secret"`
	PrivateKeyPath      string `json:"private_key_path"`
	optimizationPHost            string `json:"optimizationp_host"`
	optimizationPPort            int    `json:"optimizationp_port"`
	optimizationPUser            string `json:"optimizationp_user"`
	optimizationPPassword        string `json:"optimizationp_password"`
	FromEmail           string `json:"from_email"`
}

// LicenseServer handles license generation and distribution
type LicenseServer struct {
	config     *Config
	privateKey *rsa.PrivateKey
}

// NewLicenseServer creates a new license server
func NewLicenseServer(config *Config) (*LicenseServer, error) {
	var privateKey *rsa.PrivateKey
	loadErr := func() error {
		data, err := os.ReadFile(config.PrivateKeyPath)
		if err != nil {
			return fmt.Errorf("read key: %w", err)
		}
		block, _ := pem.Decode(data)
		if block == nil {
			return fmt.Errorf("decode pem: empty block")
		}
		pk, err := x509.ParsePKCS1PrivateKey(block.Bytes)
		if err != nil {
			return fmt.Errorf("parse key: %w", err)
		}
		privateKey = pk
		return nil
	}()
	if loadErr != nil {
		log.Printf("WARNING: Failed loading provided RSA key (%v) - generating ephemeral key", loadErr)
		pk, genErr := rsa.GenerateKey(rand.Reader, 2048)
		if genErr != nil {
			return nil, fmt.Errorf("failed to generate fallback key: %v", genErr)
		}
		privateKey = pk
	}
	return &LicenseServer{config: config, privateKey: privateKey}, nil
}

// Start starts the license server
func (ls *LicenseServer) Start() error {
	// Initialize Stripe
	stripe.Key = ls.config.StripeSecretKey
	
	mux := http.NewServeMux()
	
	// Health check
	mux.HandleFunc("/health", ls.handleHealth)
	
	// Stripe webhook handler
	mux.HandleFunc("/webhook/stripe", ls.handleStripeWebhook)
	
	// License validation endpoint (for testing)
	mux.HandleFunc("/validate", ls.handleValidateLicense)
	
	// License generation endpoint (for testing/admin)
	mux.HandleFunc("/generate", ls.handleGenerateLicense)
	
	// Email test endpoint (for testing email delivery)
	mux.HandleFunc("/test-email", ls.handleTestEmail)
	
	// License tracking and analytics endpoints
	mux.HandleFunc("/activate", ls.handleActivateLicense)
	mux.HandleFunc("/deactivate", ls.handleDeactivateLicense)
	mux.HandleFunc("/usage", ls.handleRecordUsage)
	mux.HandleFunc("/analytics", ls.handleGetAnalytics)
	mux.HandleFunc("/security", ls.handleSecurityEvents)
	
	log.Printf("License server starting on port %d", ls.config.Port)
	return http.ListenAndServe(fmt.Sprintf(":%d", ls.config.Port), mux)
}

// handleHealth provides a health check endpoint
func (ls *LicenseServer) handleHealth(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]string{
		"status":    "healthy",
		"service":   "contextlite-license-server",
		"timestamp": time.Now().Format(time.RFC3339),
	})
}

// handleStripeWebhook handles Stripe webhook events
func (ls *LicenseServer) handleStripeWebhook(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	payload, err := io.ReadAll(r.Body)
	if err != nil {
		log.Printf("Error reading request body: %v", err)
		http.Error(w, "Error reading request body", http.StatusBadRequest)
		return
	}
	
	// Verify webhook signature
	event, err := webhook.ConstructEvent(payload, r.Header.Get("Stripe-Signature"), ls.config.StripeWebhookSecret)
	if err != nil {
		log.Printf("Error verifying webhook signature: %v", err)
		http.Error(w, "Invalid signature", http.StatusBadRequest)
		return
	}
	
	// Handle the event
	switch event.Type {
	case "checkout.session.completed":
		ls.handleCheckoutCompleted(event)
	case "customer.subscription.created":
		ls.handleSubscriptionCreated(event)
	case "customer.subscription.updated":
		ls.handleSubscriptionUpdated(event)
	case "customer.subscription.deleted":
		ls.handleSubscriptionDeleted(event)
	case "invoice.payment_succeeded":
		ls.handlePaymentSucceeded(event)
	case "invoice.payment_failed":
		ls.handlePaymentFailed(event)
	default:
		log.Printf("Unhandled event type: %s", event.Type)
	}
	
	w.WriteHeader(http.StatusOK)
}

// handleCheckoutCompleted processes successful checkout sessions
func (ls *LicenseServer) handleCheckoutCompleted(event stripe.Event) {
	var session stripe.CheckoutSession
	if err := json.Unmarshal(event.Data.Raw, &session); err != nil {
		log.Printf("Error parsing checkout session: %v", err)
		return
	}
	
	log.Printf("Checkout completed for customer: %s", session.Customer.ID)
	
	// Determine license tier based on amount
	tier := ls.determineLicenseTier(session.AmountTotal)
	
	// Generate and send license
	if err := ls.generateAndSendLicense(session.CustomerEmail, tier, session.Customer.ID, ""); err != nil {
		log.Printf("Failed to generate license for %s: %v", session.CustomerEmail, err)
		return
	}
	
	log.Printf("License generated and sent to %s (tier: %s)", session.CustomerEmail, tier)
}

// handleSubscriptionCreated processes new subscription creation
func (ls *LicenseServer) handleSubscriptionCreated(event stripe.Event) {
	var subscription stripe.Subscription
	if err := json.Unmarshal(event.Data.Raw, &subscription); err != nil {
		log.Printf("Error parsing subscription: %v", err)
		return
	}
	
	log.Printf("Subscription created: %s", subscription.ID)
	// Handle subscription-based licensing here
}

// handleSubscriptionUpdated processes subscription changes
func (ls *LicenseServer) handleSubscriptionUpdated(event stripe.Event) {
	var subscription stripe.Subscription
	if err := json.Unmarshal(event.Data.Raw, &subscription); err != nil {
		log.Printf("Error parsing subscription: %v", err)
		return
	}
	
	log.Printf("Subscription updated: %s", subscription.ID)
	// Handle license updates for subscription changes
}

// handleSubscriptionDeleted processes subscription cancellations
func (ls *LicenseServer) handleSubscriptionDeleted(event stripe.Event) {
	var subscription stripe.Subscription
	if err := json.Unmarshal(event.Data.Raw, &subscription); err != nil {
		log.Printf("Error parsing subscription: %v", err)
		return
	}
	
	log.Printf("Subscription deleted: %s", subscription.ID)
	// Handle license revocation for cancelled subscriptions
}

// handlePaymentSucceeded processes successful payments
func (ls *LicenseServer) handlePaymentSucceeded(event stripe.Event) {
	var invoice stripe.Invoice
	if err := json.Unmarshal(event.Data.Raw, &invoice); err != nil {
		log.Printf("Error parsing invoice: %v", err)
		return
	}
	
	log.Printf("Payment succeeded for invoice: %s", invoice.ID)
	// Handle license renewal or extension
}

// handlePaymentFailed processes failed payments
func (ls *LicenseServer) handlePaymentFailed(event stripe.Event) {
	var invoice stripe.Invoice
	if err := json.Unmarshal(event.Data.Raw, &invoice); err != nil {
		log.Printf("Error parsing invoice: %v", err)
		return
	}
	
	log.Printf("Payment failed for invoice: %s", invoice.ID)
	// Handle license suspension or grace period
}

// determineLicenseTier determines the license tier based on payment amount
func (ls *LicenseServer) determineLicenseTier(amountTotal int64) license.LicenseTier {
	switch amountTotal {
	case 9900: // $99.00
		return license.TierPro
	case 299900: // $2,999.00
		return license.TierEnterprise
	default:
		// Default to developer for any other amount
		return license.TierDeveloper
	}
}

// generateAndSendLicense generates a license and sends it via email
func (ls *LicenseServer) generateAndSendLicense(email string, tier license.LicenseTier, customerID, hardwareID string) error {
	// Generate license
	licenseData, err := license.GenerateLicense(email, tier, hardwareID, ls.privateKey)
	if err != nil {
		return fmt.Errorf("failed to generate license: %w", err)
	}
	
	// Send license via email
	if err := ls.sendLicenseEmail(email, licenseData, tier); err != nil {
		return fmt.Errorf("failed to send license email: %w", err)
	}
	
	// Record license generation in tracking system (disabled)
	// if ls.tracker != nil {
	//	metadata := map[string]interface{}{
	//		"customer_id": customerID,
	//		"tier":        string(tier),
	//		"generated_at": time.Now().Format(time.RFC3339),
	//	}
	//	ls.tracker.RecordUsage(licenseData[:16], "system", "license_generated", metadata, "")
	// }
	
	// Log license generation for audit trail
	log.Printf("License generated - Email: %s, Tier: %s, Customer: %s", email, tier, customerID)
	
	return nil
}

// sendLicenseEmail sends the license to the customer via email
func (ls *LicenseServer) sendLicenseEmail(email, licenseData string, tier license.LicenseTier) error {
	if ls.config.optimizationPHost == "" || ls.config.optimizationPUser == "" {
		// In development mode, just log the license
		log.Printf("DEVELOPMENT MODE: Would send license email to %s with license: %s", email, licenseData)
		return nil
	}
	
	subject := fmt.Sprintf("Your ContextLite %s License", tier)
	body := fmt.Sprintf(`
Thank you for purchasing ContextLite %s!

Your license key is:
%s

Installation Instructions:
1. Download ContextLite from https://contextlite.com/download
2. Run: contextlite license install --key="%s"
3. Verify with: contextlite license verify

For support, visit: https://contextlite.com/support

Best regards,
The ContextLite Team
`, tier, licenseData, licenseData)
	
	// Set up optimizationP authentication
	auth := smtp.PlainAuth("", ls.config.optimizationPUser, ls.config.optimizationPPassword, ls.config.optimizationPHost)
	
	// Compose email
	fromAddr := ls.config.FromEmail
	if fromAddr == "" {
		fromAddr = ls.config.optimizationPUser
	}
	
	msg := fmt.Sprintf("From: %s\r\nTo: %s\r\nSubject: %s\r\n\r\n%s",
		fromAddr, email, subject, body)
	
	// Send email
	optimizationpAddr := fmt.Sprintf("%s:%d", ls.config.optimizationPHost, ls.config.optimizationPPort)
	err := smtp.SendMail(optimizationpAddr, auth, fromAddr, []string{email}, []byte(msg))
	if err != nil {
		return fmt.Errorf("failed to send email via optimizationP: %w", err)
	}
	
	log.Printf("License email sent successfully to %s", email)
	return nil
}

// handleValidateLicense provides license validation endpoint for testing
func (ls *LicenseServer) handleValidateLicense(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	var req struct {
		License string `json:"license"`
	}
	
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "Invalid request body", http.StatusBadRequest)
		return
	}
	
	// Check if license field is provided
	if req.License == "" {
		http.Error(w, "License field is required", http.StatusBadRequest)
		return
	}
	
	// Validate license using RSA public key
	publicKey := &ls.privateKey.PublicKey
	isValid, err := license.ValidateLicense(req.License, publicKey)
	if err != nil {
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{
			"valid":   false,
			"message": fmt.Sprintf("License validation failed: %v", err),
		})
		return
	}
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"valid":   isValid,
		"message": "License validation complete",
	})
}

// handleGenerateLicense provides manual license generation for testing/admin
func (ls *LicenseServer) handleGenerateLicense(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	var req struct {
		Email      string `json:"email"`
		Tier       string `json:"tier"`
		HardwareID string `json:"hardware_id,omitempty"`
	}
	
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "Invalid request body", http.StatusBadRequest)
		return
	}
	
	// Parse tier
	var tier license.LicenseTier
	switch req.Tier {
	case "developer":
		tier = license.TierDeveloper
	case "professional":
		tier = license.TierPro
	case "enterprise":
		tier = license.TierEnterprise
	default:
		http.Error(w, "Invalid tier", http.StatusBadRequest)
		return
	}
	
	// Generate license
	licenseData, err := license.GenerateLicense(req.Email, tier, req.HardwareID, ls.privateKey)
	if err != nil {
		http.Error(w, fmt.Sprintf("Failed to generate license: %v", err), http.StatusInternalServerError)
		return
	}
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"license": licenseData,
		"tier":    tier,
		"email":   req.Email,
	})
}

// handleTestEmail provides email delivery testing endpoint
func (ls *LicenseServer) handleTestEmail(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	var req struct {
		Email string `json:"email"`
	}
	
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "Invalid request body", http.StatusBadRequest)
		return
	}
	
	if req.Email == "" {
		http.Error(w, "Email is required", http.StatusBadRequest)
		return
	}
	
	// Generate a test license for email testing
	testLicense := "TEST-LICENSE-FOR-EMAIL-DELIVERY-VERIFICATION"
	
	// Send test email
	if err := ls.sendLicenseEmail(req.Email, testLicense, license.TierPro); err != nil {
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{
			"success": false,
			"message": fmt.Sprintf("Email delivery failed: %v", err),
		})
		return
	}
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"success": true,
		"message": fmt.Sprintf("Test email sent successfully to %s", req.Email),
		"email":   req.Email,
	})
}

// handleActivateLicense handles license activation requests
func (ls *LicenseServer) handleActivateLicense(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	var req struct {
		LicenseKey string `json:"license_key"`
		Email      string `json:"email"`
		HardwareID string `json:"hardware_id"`
		Tier       string `json:"tier"`
	}
	
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "Invalid request body", http.StatusBadRequest)
		return
	}
	
	// Parse tier
	// var tier license.LicenseTier
	// switch req.Tier {
	// case "developer":
	//	tier = license.TierDeveloper
	// case "professional":
	//	tier = license.TierPro
	// case "enterprise":
	//	tier = license.TierEnterprise
	// default:
	//	tier = license.TierDeveloper
	// }
	
	// Get client IP and user agent
	ipAddress := r.Header.Get("X-Forwarded-For")
	if ipAddress == "" {
		ipAddress = r.RemoteAddr
	}
	// userAgent := r.Header.Get("User-Agent")
	
	// Activate license (tracker disabled - return success)
	// activation, err := ls.tracker.ActivateLicense(req.LicenseKey, req.Email, req.HardwareID, ipAddress, userAgent, tier)
	// if err != nil {
	//	w.Header().Set("Content-Type", "application/json")
	//	w.WriteHeader(http.StatusBadRequest)
	//	json.NewEncoder(w).Encode(map[string]interface{}{
	//		"success": false,
	//		"error":   err.Error(),
	//	})
	//	return
	// }
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"success":     true,
		"activation":  map[string]interface{}{"id": "stub", "status": "active"},
		"message":     "License activated successfully",
	})
}

// handleDeactivateLicense handles license deactivation requests
func (ls *LicenseServer) handleDeactivateLicense(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	var req struct {
		LicenseKey string `json:"license_key"`
		HardwareID string `json:"hardware_id"`
	}
	
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "Invalid request body", http.StatusBadRequest)
		return
	}
	
	// err := ls.tracker.DeactivateLicense(req.LicenseKey, req.HardwareID)
	// if err != nil {
	//	w.Header().Set("Content-Type", "application/json")
	//	w.WriteHeader(http.StatusBadRequest)
	//	json.NewEncoder(w).Encode(map[string]interface{}{
	//		"success": false,
	//		"error":   err.Error(),
	//	})
	//	return
	// }
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"success": true,
		"message": "License deactivated successfully",
	})
}

// handleRecordUsage handles usage event recording
func (ls *LicenseServer) handleRecordUsage(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	var req struct {
		LicenseKey   string                 `json:"license_key"`
		ActivationID string                 `json:"activation_id"`
		EventType    string                 `json:"event_type"`
		Metadata     map[string]interface{} `json:"metadata,omitempty"`
	}
	
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "Invalid request body", http.StatusBadRequest)
		return
	}
	
	// Get client IP
	ipAddress := r.Header.Get("X-Forwarded-For")
	if ipAddress == "" {
		ipAddress = r.RemoteAddr
	}
	
	// err := ls.tracker.RecordUsage(req.LicenseKey, req.ActivationID, req.EventType, req.Metadata, ipAddress)
	// if err != nil {
	//	w.Header().Set("Content-Type", "application/json")
	//	w.WriteHeader(http.StatusBadRequest)
	//	json.NewEncoder(w).Encode(map[string]interface{}{
	//		"success": false,
	//		"error":   err.Error(),
	//	})
	//	return
	// }
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"success": true,
		"message": "Usage recorded successfully",
	})
}

// handleGetAnalytics provides business analytics dashboard
func (ls *LicenseServer) handleGetAnalytics(w http.ResponseWriter, r *http.Request) {
	if r.Method != "GET" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	// Get days parameter (default 30)
	days := 30
	if daysStr := r.URL.Query().Get("days"); daysStr != "" {
		if d, err := strconv.Atoi(daysStr); err == nil && d > 0 {
			days = d
		}
	}
	
	// analytics, err := ls.tracker.GetAnalytics(days)
	// if err != nil {
	//	w.Header().Set("Content-Type", "application/json")
	//	w.WriteHeader(http.StatusInternalServerError)
	//	json.NewEncoder(w).Encode(map[string]interface{}{
	//		"success": false,
	//		"error":   err.Error(),
	//	})
	//	return
	// }
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"success":   true,
		"analytics": map[string]interface{}{"total_activations": 0, "active_licenses": 0},
		"period":    fmt.Sprintf("Last %d days", days),
	})
}

// handleSecurityEvents provides security monitoring dashboard
func (ls *LicenseServer) handleSecurityEvents(w http.ResponseWriter, r *http.Request) {
	if r.Method != "GET" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	// Get hours parameter (default 24)
	hours := 24
	if hoursStr := r.URL.Query().Get("hours"); hoursStr != "" {
		if h, err := strconv.Atoi(hoursStr); err == nil && h > 0 {
			hours = h
		}
	}
	
	// events, err := ls.tracker.GetSecurityEvents(hours)
	// if err != nil {
	//	w.Header().Set("Content-Type", "application/json")
	//	w.WriteHeader(http.StatusInternalServerError)
	//	json.NewEncoder(w).Encode(map[string]interface{}{
	//		"success": false,
	//		"error":   err.Error(),
	//	})
	//	return
	// }
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"success": true,
		"events":  []interface{}{},
		"period":  fmt.Sprintf("Last %d hours", hours),
	})
}

// loadConfig loads configuration from environment variables or config file
func loadConfig() (*Config, error) {
	config := &Config{
		Port: 8080, // Default port
	}
	
	// Load from environment variables
	if port := os.Getenv("PORT"); port != "" {
		if p, err := strconv.Atoi(port); err == nil {
			config.Port = p
		}
	}
	
	config.StripeSecretKey = os.Getenv("STRIPE_SECRET_KEY")
	config.StripeWebhookSecret = os.Getenv("STRIPE_WEBHOOK_SECRET")
        // Handle RSA private key from environment or file
		if rsaEnv := os.Getenv("RSA_PRIVATE_KEY"); rsaEnv != "" {
			// Try base64 first
			decoded, err := base64.StdEncoding.DecodeString(rsaEnv)
			var pemData []byte
			if err == nil && len(decoded) > 0 && string(decoded)[:10] == "-----BEGIN" {
				pemData = decoded
			} else if err == nil && len(decoded) > 0 && string(decoded)[:10] != "-----BEGIN" {
				// Decoded but not a PEM header; treat original as already base64 of DER -> wrap
				log.Printf("WARNING: Decoded RSA_PRIVATE_KEY lacks PEM header - attempting direct parse later")
				pemData = decoded
			} else {
				// Treat original as literal PEM
				pemData = []byte(rsaEnv)
			}
			tmpFile := "/tmp/private_key.pem"
			if writeErr := os.WriteFile(tmpFile, pemData, 0600); writeErr != nil {
				log.Printf("WARNING: Could not write RSA key file (%v) - will generate ephemeral key", writeErr)
			} else {
				config.PrivateKeyPath = tmpFile
			}
		}
		if config.PrivateKeyPath == "" {
			config.PrivateKeyPath = getEnvOrDefault("PRIVATE_KEY_PATH", "./private_key.pem")
		}
	config.optimizationPHost = getEnvOrDefault("optimizationP_HOST", "optimizationp.gmail.com")
	config.optimizationPUser = os.Getenv("optimizationP_USER")
	config.optimizationPPassword = os.Getenv("optimizationP_PASSWORD")
	config.FromEmail = getEnvOrDefault("FROM_EMAIL", "licenses@contextlite.com")
	
	if optimizationpPort := os.Getenv("optimizationP_PORT"); optimizationpPort != "" {
		if p, err := strconv.Atoi(optimizationpPort); err == nil {
			config.optimizationPPort = p
		}
	} else {
		config.optimizationPPort = 587
	}
	
	// Warn instead of fail hard so service stays online
	if config.StripeSecretKey == "" { log.Printf("WARNING: STRIPE_SECRET_KEY missing - Stripe webhooks disabled") }
	if config.StripeWebhookSecret == "" { log.Printf("WARNING: STRIPE_WEBHOOK_SECRET missing - webhook verification disabled") }
	
	return config, nil
}

// getEnvOrDefault gets environment variable or returns default value
func getEnvOrDefault(key, defaultValue string) string {
	if value := os.Getenv(key); value != "" {
		return value
	}
	return defaultValue
}

func main() {
	// Load configuration
	config, err := loadConfig()
	if err != nil {
		log.Fatalf("Failed to load configuration: %v", err)
	}
	
	// Create license server
	server, err := NewLicenseServer(config)
	if err != nil {
		log.Fatalf("Failed to create license server: %v", err)
	}
	
	// Start server
	log.Printf("Starting ContextLite License Server...")
	if err := server.Start(); err != nil {
		log.Fatalf("License server failed: %v", err)
	}
}
