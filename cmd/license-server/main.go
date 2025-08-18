package main

import (
	"crypto/rsa"
	"crypto/x509"
	"encoding/json"
        "encoding/base64"
	"encoding/pem"
	"fmt"
	"io"
	"log"
	"net/http"
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
	// Load RSA private key
	privateKeyData, err := os.ReadFile(config.PrivateKeyPath)
	if err != nil {
		return nil, fmt.Errorf("failed to read private key: %w", err)
	}
	
	block, _ := pem.Decode(privateKeyData)
	if block == nil {
		return nil, fmt.Errorf("failed to decode PEM block")
	}
	
	privateKey, err := x509.ParsePKCS1PrivateKey(block.Bytes)
	if err != nil {
		return nil, fmt.Errorf("failed to parse private key: %w", err)
	}
	
	return &LicenseServer{
		config:     config,
		privateKey: privateKey,
	}, nil
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
	
	// Log license generation for audit trail
	log.Printf("License generated - Email: %s, Tier: %s, Customer: %s", email, tier, customerID)
	
	return nil
}

// sendLicenseEmail sends the license to the customer via email
func (ls *LicenseServer) sendLicenseEmail(email, licenseData string, tier license.LicenseTier) error {
	// TODO: Implement email sending with proper optimizationP configuration
	// For now, just log the license (in production, use proper email service)
	
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
	
	log.Printf("Sending license email to %s:\nSubject: %s\nBody: %s", email, subject, body)
	
	// TODO: Replace with actual email sending logic
	// return optimizationp.SendEmail(ls.config.optimizationPHost, ls.config.optimizationPUser, ls.config.optimizationPPassword, email, subject, body)
	
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
        if rsaPrivateKey := os.Getenv("RSA_PRIVATE_KEY"); rsaPrivateKey != "" {
                // Decode base64 private key and write to temp file
                privateKeyData, err := base64.StdEncoding.DecodeString(rsaPrivateKey)
                if err != nil {
                        return nil, fmt.Errorf("failed to decode RSA_PRIVATE_KEY: %w", err)
                }
                
                tmpFile := "/tmp/private_key.pem"
                if err := os.WriteFile(tmpFile, privateKeyData, 0600); err != nil {
                        return nil, fmt.Errorf("failed to write private key to temp file: %w", err)
                }
                config.PrivateKeyPath = tmpFile
        } else {
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
	
	// Validate required configuration
	if config.StripeSecretKey == "" {
		return nil, fmt.Errorf("STRIPE_SECRET_KEY is required")
	}
	if config.StripeWebhookSecret == "" {
		return nil, fmt.Errorf("STRIPE_WEBHOOK_SECRET is required")
	}
	
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
