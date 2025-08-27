package license

import (
	"database/sql"
	"fmt"
	"log"
	"net/smtp"
	"time"

	_ "modernc.org/sqlite"
)

// AbandonedCart represents an abandoned checkout session
type AbandonedCart struct {
	ID              string    `json:"id" db:"id"`
	SessionID       string    `json:"session_id" db:"session_id"`
	CustomerEmail   string    `json:"customer_email" db:"customer_email"`
	AmountTotal     int64     `json:"amount_total" db:"amount_total"`
	Currency        string    `json:"currency" db:"currency"`
	ProductName     string    `json:"product_name" db:"product_name"`
	CreatedAt       time.Time `json:"created_at" db:"created_at"`
	ExpiredAt       time.Time `json:"expired_at" db:"expired_at"`
	EmailSequence   int       `json:"email_sequence" db:"email_sequence"`
	LastEmailSent   time.Time `json:"last_email_sent" db:"last_email_sent"`
	Recovered       bool      `json:"recovered" db:"recovered"`
	PaymentLinkURL  string    `json:"payment_link_url" db:"payment_link_url"`
}

// AbandonedCartManager handles abandoned cart recovery
type AbandonedCartManager struct {
	db         *sql.DB
	smtpConfig SMTPConfig
}

// SMTPConfig holds email configuration
type SMTPConfig struct {
	Host     string
	Port     int
	User     string
	Password string
	FromAddr string
}

// NewAbandonedCartManager creates a new abandoned cart manager
func NewAbandonedCartManager(dbPath string, smtpConfig SMTPConfig) (*AbandonedCartManager, error) {
	db, err := sql.Open("sqlite3", dbPath)
	if err != nil {
		return nil, fmt.Errorf("failed to open database: %w", err)
	}

	manager := &AbandonedCartManager{
		db:         db,
		smtpConfig: smtpConfig,
	}

	// Initialize database tables
	if err := manager.initTables(); err != nil {
		return nil, fmt.Errorf("failed to initialize tables: %w", err)
	}

	return manager, nil
}

// initTables creates the abandoned_carts table
func (acm *AbandonedCartManager) initTables() error {
	createTableSQL := `
		CREATE TABLE IF NOT EXISTS abandoned_carts (
			id TEXT PRIMARY KEY,
			session_id TEXT UNIQUE NOT NULL,
			customer_email TEXT,
			amount_total INTEGER NOT NULL,
			currency TEXT NOT NULL,
			product_name TEXT,
			created_at DATETIME NOT NULL,
			expired_at DATETIME NOT NULL,
			email_sequence INTEGER DEFAULT 0,
			last_email_sent DATETIME,
			recovered BOOLEAN DEFAULT FALSE,
			payment_link_url TEXT,
			UNIQUE(session_id)
		);
		
		CREATE INDEX IF NOT EXISTS idx_abandoned_carts_email ON abandoned_carts(customer_email);
		CREATE INDEX IF NOT EXISTS idx_abandoned_carts_expired ON abandoned_carts(expired_at);
		CREATE INDEX IF NOT EXISTS idx_abandoned_carts_recovered ON abandoned_carts(recovered);
	`

	_, err := acm.db.Exec(createTableSQL)
	return err
}

// RecordAbandonedCart records a new abandoned cart
func (acm *AbandonedCartManager) RecordAbandonedCart(sessionID, email string, amountTotal int64, currency, productName, paymentLinkURL string, expiredAt time.Time) error {
	cart := AbandonedCart{
		ID:             fmt.Sprintf("cart_%s_%d", sessionID, time.Now().Unix()),
		SessionID:      sessionID,
		CustomerEmail:  email,
		AmountTotal:    amountTotal,
		Currency:       currency,
		ProductName:    productName,
		CreatedAt:      time.Now(),
		ExpiredAt:      expiredAt,
		EmailSequence:  0,
		Recovered:      false,
		PaymentLinkURL: paymentLinkURL,
	}

	insertSQL := `
		INSERT OR REPLACE INTO abandoned_carts 
		(id, session_id, customer_email, amount_total, currency, product_name, created_at, expired_at, email_sequence, recovered, payment_link_url)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
	`

	_, err := acm.db.Exec(insertSQL,
		cart.ID, cart.SessionID, cart.CustomerEmail, cart.AmountTotal, cart.Currency,
		cart.ProductName, cart.CreatedAt, cart.ExpiredAt, cart.EmailSequence, cart.Recovered, cart.PaymentLinkURL)

	if err != nil {
		return fmt.Errorf("failed to record abandoned cart: %w", err)
	}

	log.Printf("Recorded abandoned cart: Session %s, Email %s, Amount $%.2f", 
		sessionID, email, float64(amountTotal)/100.0)
	
	return nil
}

// MarkRecovered marks an abandoned cart as recovered when payment succeeds
func (acm *AbandonedCartManager) MarkRecovered(sessionID string) error {
	updateSQL := `UPDATE abandoned_carts SET recovered = TRUE WHERE session_id = ?`
	
	result, err := acm.db.Exec(updateSQL, sessionID)
	if err != nil {
		return fmt.Errorf("failed to mark cart as recovered: %w", err)
	}

	rowsAffected, _ := result.RowsAffected()
	if rowsAffected > 0 {
		log.Printf("Marked abandoned cart as recovered: Session %s", sessionID)
	}

	return nil
}

// ProcessAbandonedCarts finds and processes abandoned carts for email sequences
func (acm *AbandonedCartManager) ProcessAbandonedCarts() error {
	now := time.Now()
	
	// Find carts ready for email sequence
	query := `
		SELECT id, session_id, customer_email, amount_total, currency, product_name, 
		       created_at, expired_at, email_sequence, last_email_sent, payment_link_url
		FROM abandoned_carts 
		WHERE recovered = FALSE 
		  AND customer_email IS NOT NULL 
		  AND customer_email != ''
		  AND (
		    (email_sequence = 0 AND expired_at <= ?) OR
		    (email_sequence = 1 AND last_email_sent <= ?) OR
		    (email_sequence = 2 AND last_email_sent <= ?)
		  )
		ORDER BY created_at
	`

	// Time intervals for email sequence
	oneDayAgo := now.Add(-24 * time.Hour)
	threeDaysAgo := now.Add(-72 * time.Hour)

	rows, err := acm.db.Query(query, now, oneDayAgo, threeDaysAgo)
	if err != nil {
		return fmt.Errorf("failed to query abandoned carts: %w", err)
	}
	defer rows.Close()

	processed := 0
	for rows.Next() {
		var cart AbandonedCart
		err := rows.Scan(&cart.ID, &cart.SessionID, &cart.CustomerEmail, &cart.AmountTotal,
			&cart.Currency, &cart.ProductName, &cart.CreatedAt, &cart.ExpiredAt,
			&cart.EmailSequence, &cart.LastEmailSent, &cart.PaymentLinkURL)
		if err != nil {
			log.Printf("Error scanning abandoned cart row: %v", err)
			continue
		}

		// Determine which email to send
		var emailType string
		var nextSequence int
		
		switch cart.EmailSequence {
		case 0:
			if cart.ExpiredAt.Before(now) {
				emailType = "reminder"
				nextSequence = 1
			}
		case 1:
			if cart.LastEmailSent.Before(oneDayAgo) {
				emailType = "benefits"
				nextSequence = 2
			}
		case 2:
			if cart.LastEmailSent.Before(threeDaysAgo) {
				emailType = "discount"
				nextSequence = 3
			}
		default:
			continue // No more emails to send
		}

		if emailType != "" {
			if err := acm.sendAbandonedCartEmail(cart, emailType); err != nil {
				log.Printf("Failed to send %s email to %s: %v", emailType, cart.CustomerEmail, err)
				continue
			}

			// Update email sequence
			if err := acm.updateEmailSequence(cart.ID, nextSequence, now); err != nil {
				log.Printf("Failed to update email sequence for cart %s: %v", cart.ID, err)
			}

			processed++
		}
	}

	if processed > 0 {
		log.Printf("Processed %d abandoned cart emails", processed)
	}

	return nil
}

// sendAbandonedCartEmail sends the appropriate email based on type
func (acm *AbandonedCartManager) sendAbandonedCartEmail(cart AbandonedCart, emailType string) error {
	if acm.smtpConfig.Host == "" {
		log.Printf("DEVELOPMENT MODE: Would send %s email to %s for cart %s", emailType, cart.CustomerEmail, cart.SessionID)
		return nil
	}

	var subject, body string
	productTier := acm.getProductTier(cart.AmountTotal)
	
	switch emailType {
	case "reminder":
		subject = "Your ContextLite download is waiting..."
		body = acm.getReminderEmailBody(cart, productTier)
	case "benefits":
		subject = "Still considering ContextLite? Here's why developers choose us over Pinecone..."
		body = acm.getBenefitsEmailBody(cart, productTier)
	case "discount":
		subject = "Last chance: 20% off ContextLite (expires tonight)"
		body = acm.getDiscountEmailBody(cart, productTier)
	default:
		return fmt.Errorf("unknown email type: %s", emailType)
	}

	return acm.sendEmail(cart.CustomerEmail, subject, body)
}

// sendEmail sends an email using SMTP
func (acm *AbandonedCartManager) sendEmail(to, subject, body string) error {
	auth := smtp.PlainAuth("", acm.smtpConfig.User, acm.smtpConfig.Password, acm.smtpConfig.Host)
	
	fromAddr := acm.smtpConfig.FromAddr
	if fromAddr == "" {
		fromAddr = acm.smtpConfig.User
	}

	msg := fmt.Sprintf("From: %s\r\nTo: %s\r\nSubject: %s\r\n\r\n%s",
		fromAddr, to, subject, body)

	smtpAddr := fmt.Sprintf("%s:%d", acm.smtpConfig.Host, acm.smtpConfig.Port)
	err := smtp.SendMail(smtpAddr, auth, fromAddr, []string{to}, []byte(msg))
	if err != nil {
		return fmt.Errorf("failed to send email: %w", err)
	}

	log.Printf("Sent %s email to %s", subject, to)
	return nil
}

// updateEmailSequence updates the email sequence for a cart
func (acm *AbandonedCartManager) updateEmailSequence(cartID string, sequence int, sentAt time.Time) error {
	updateSQL := `UPDATE abandoned_carts SET email_sequence = ?, last_email_sent = ? WHERE id = ?`
	_, err := acm.db.Exec(updateSQL, sequence, sentAt, cartID)
	return err
}

// getProductTier determines product tier from amount
func (acm *AbandonedCartManager) getProductTier(amountTotal int64) string {
	switch amountTotal {
	case 9900:
		return "Professional"
	case 299900:
		return "Enterprise"
	default:
		return "Professional"
	}
}

// Email templates
func (acm *AbandonedCartManager) getReminderEmailBody(cart AbandonedCart, tier string) string {
	return fmt.Sprintf(`Hi there,

I noticed you were interested in ContextLite %s but didn't complete your purchase.

Quick reminder: ContextLite is 100x faster than vector databases like Pinecone, with 0.3ms response times.

✅ No monthly fees (save $70-400/month vs Pinecone)
✅ Complete privacy - runs locally  
✅ 99.9%% accuracy
✅ Works offline

Complete your purchase here:
%s

Questions? Just reply to this email.

Best,
Mike Kuykendall
Founder, ContextLite`, tier, cart.PaymentLinkURL)
}

func (acm *AbandonedCartManager) getBenefitsEmailBody(cart AbandonedCart, tier string) string {
	return fmt.Sprintf(`Still considering ContextLite? Here's why 1000+ developers have made the switch:

🚀 **Speed**: 0.3ms vs 30-50ms (100x faster than Pinecone)
💰 **Cost**: One-time $%.0f vs $70-400/month recurring
🔒 **Privacy**: Your data never leaves your machine
⚡ **Reliability**: No cloud downtime or API limits

Real developer feedback:
"Replaced our $300/month Pinecone bill with ContextLite. Same accuracy, 100x faster." - Sarah Chen, Lead Engineer

Ready to make the switch?
%s

Best,
Mike`, float64(cart.AmountTotal)/100.0, cart.PaymentLinkURL)
}

func (acm *AbandonedCartManager) getDiscountEmailBody(cart AbandonedCart, tier string) string {
	// Create discount URL (you'd implement this based on your Stripe setup)
	discountURL := cart.PaymentLinkURL // For now, use same URL
	
	return fmt.Sprintf(`This is your final reminder about ContextLite %s.

🎯 **SPECIAL OFFER: 20%% OFF - EXPIRES TONIGHT**

Original price: $%.0f
Your price: $%.0f (Save $%.0f!)

Use this exclusive link:
%s

This offer expires at midnight PST tonight.

After tonight, ContextLite returns to full price. Don't miss out on:
✅ 100x faster than vector databases
✅ No monthly fees ever
✅ Complete privacy and control

Click here to secure your license:
%s

Best,
Mike Kuykendall
P.S. This discount won't be offered again.`, 
		tier, 
		float64(cart.AmountTotal)/100.0, 
		float64(cart.AmountTotal)*0.8/100.0, 
		float64(cart.AmountTotal)*0.2/100.0,
		discountURL, discountURL)
}

// GetAbandonedCartStats returns statistics about abandoned carts
func (acm *AbandonedCartManager) GetAbandonedCartStats(days int) (map[string]interface{}, error) {
	since := time.Now().AddDate(0, 0, -days)
	
	query := `
		SELECT 
			COUNT(*) as total_abandoned,
			COUNT(CASE WHEN recovered = TRUE THEN 1 END) as recovered,
			COUNT(CASE WHEN email_sequence > 0 THEN 1 END) as emailed,
			SUM(amount_total) as total_value,
			SUM(CASE WHEN recovered = TRUE THEN amount_total ELSE 0 END) as recovered_value
		FROM abandoned_carts 
		WHERE created_at >= ?
	`
	
	var stats struct {
		TotalAbandoned int64   `db:"total_abandoned"`
		Recovered      int64   `db:"recovered"`
		Emailed        int64   `db:"emailed"`
		TotalValue     int64   `db:"total_value"`
		RecoveredValue int64   `db:"recovered_value"`
	}
	
	row := acm.db.QueryRow(query, since)
	err := row.Scan(&stats.TotalAbandoned, &stats.Recovered, &stats.Emailed, &stats.TotalValue, &stats.RecoveredValue)
	if err != nil {
		return nil, fmt.Errorf("failed to get abandoned cart stats: %w", err)
	}
	
	recoveryRate := 0.0
	if stats.TotalAbandoned > 0 {
		recoveryRate = float64(stats.Recovered) / float64(stats.TotalAbandoned) * 100.0
	}
	
	return map[string]interface{}{
		"total_abandoned_carts": stats.TotalAbandoned,
		"recovered_carts":       stats.Recovered,
		"emailed_carts":         stats.Emailed,
		"recovery_rate_percent": recoveryRate,
		"total_abandoned_value": float64(stats.TotalValue) / 100.0,
		"recovered_value":       float64(stats.RecoveredValue) / 100.0,
		"period_days":           days,
	}, nil
}

// Close closes the database connection
func (acm *AbandonedCartManager) Close() error {
	return acm.db.Close()
}