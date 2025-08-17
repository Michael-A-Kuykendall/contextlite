# CRITICAL SECURITY FIXES IMPLEMENTATION PLAN

## 🚨 IMMEDIATE PRIORITIES (PRODUCTION BLOCKERS)

### 1. MAIN APPLICATION LICENSE INTEGRATION
**Current State**: No license validation in main binary
**Risk**: Enterprise features accessible without license
**Fix Required**: Integrate license validation into startup sequence

```go
// cmd/contextlite/main.go - ADD THIS
import (
    "contextlite/internal/license"
    "contextlite/internal/features"
)

func main() {
    // Initialize license manager FIRST
    licenseManager, err := license.NewLicenseManager()
    if err != nil {
        log.Fatalf("License initialization failed: %v", err)
    }
    
    // Create feature gate
    featureGate := features.NewFeatureGate(licenseManager)
    
    // Pass to all components that need license validation
    api := api.NewServer(storage, pipeline, featureGate)
}
```

### 2. COMPLETE STUBBED IMPLEMENTATIONS

#### A. Tenant Database Initialization (HIGH PRIORITY)
```go
// internal/enterprise/tenant.go - IMPLEMENT THIS
func (tm *TenantManager) initTenantDatabase(tenant *TenantConfig) error {
    // Create isolated SQLite database
    dbPath := tenant.DatabaseURL
    db, err := sql.Open("sqlite", dbPath)
    if err != nil {
        return fmt.Errorf("failed to create tenant database: %w", err)
    }
    defer db.Close()
    
    // Initialize with ContextLite schema
    if err := initializeContextLiteSchema(db); err != nil {
        return fmt.Errorf("failed to initialize schema: %w", err)
    }
    
    // Apply tenant-specific settings
    return applyTenantSettings(db, tenant.Settings)
}
```

#### B. MCP Server Deployment (MEDIUM PRIORITY)
```go
// internal/enterprise/mcp.go - IMPLEMENT THIS
func (mm *MCPManager) DeployMCPServer(serverID string) error {
    server, err := mm.GetMCPServer(serverID)
    if err != nil {
        return err
    }
    
    // Validate configuration
    if err := validateMCPConfig(server.Config); err != nil {
        return fmt.Errorf("invalid MCP config: %w", err)
    }
    
    // Start server process (could be Docker, systemd, etc.)
    if err := startMCPProcess(server); err != nil {
        return fmt.Errorf("failed to start MCP server: %w", err)
    }
    
    // Health check
    if err := healthCheckMCP(server.Endpoint); err != nil {
        return fmt.Errorf("MCP server health check failed: %w", err)
    }
    
    return mm.SetMCPServerStatus(serverID, "active")
}
```

### 3. LICENSE GENERATION SYSTEM (CRITICAL)

#### A. License Server with Stripe Integration
```go
// cmd/license-server/main.go - NEW FILE NEEDED
package main

import (
    "net/http"
    "github.com/stripe/stripe-go/v74"
    "github.com/stripe/stripe-go/v74/webhook"
)

func handleStripeWebhook(w http.ResponseWriter, r *http.Request) {
    payload, err := ioutil.ReadAll(r.Body)
    event, err := webhook.ConstructEvent(payload, r.Header.Get("Stripe-Signature"), webhookSecret)
    
    if event.Type == "checkout.session.completed" {
        session := event.Data.Object["checkout.session"]
        email := session["customer_email"]
        amount := session["amount_total"]
        
        // Determine license tier based on amount
        var tier license.LicenseTier
        switch amount {
        case 9900: // $99
            tier = license.TierPro
        case 299900: // $2,999
            tier = license.TierEnterprise
        }
        
        // Generate and send license
        licenseData, err := license.GenerateLicense(email, tier, "", privateKey)
        // Send license via email
        sendLicenseEmail(email, licenseData)
    }
}
```

#### B. RSA Key Generation (ONE-TIME SETUP)
```bash
# Generate RSA key pair for license signing
openssl genrsa -out private_key.pem 2048
openssl rsa -in private_key.pem -pubout -out public_key.pem

# Embed public key in application
# Keep private key secure on license server only
```

### 4. API ENDPOINT PROTECTION
```go
// internal/api/server.go - ADD LICENSE VALIDATION
func (s *Server) requireProfessional(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        if err := s.featureGate.RequireProfessional("API access"); err != nil {
            http.Error(w, err.Error(), http.StatusForbidden)
            return
        }
        next.ServeHTTP(w, r)
    })
}

// Apply to API routes
mux.Handle("/api/documents", s.requireProfessional(s.handleDocuments))
mux.Handle("/api/context", s.requireProfessional(s.handleContext))
```

---

## 🔧 IMPLEMENTATION SEQUENCE

### Phase 1: License Integration (2 days)
1. ✅ Add license validation to main.go startup
2. ✅ Integrate feature gates into API server
3. ✅ Add license validation to CLI commands
4. ✅ Test license enforcement end-to-end

### Phase 2: Complete Stubs (3 days)
1. ✅ Implement tenant database initialization
2. ✅ Complete MCP server deployment
3. ✅ Add proper error handling and validation
4. ✅ Integration testing

### Phase 3: License Generation (3 days)
1. ✅ Build license server with Stripe webhooks
2. ✅ Generate real RSA keys
3. ✅ Email delivery system for licenses
4. ✅ License revocation system

### Phase 4: Security Hardening (2 days)
1. ✅ Strengthen hardware fingerprinting
2. ✅ Add tamper detection
3. ✅ Penetration testing
4. ✅ Security audit

---

## 🎯 SUCCESS CRITERIA

### License System Must Pass:
- [ ] **Bypass Test**: Attempt to use enterprise features without license (must fail)
- [ ] **Sharing Test**: Use same license on different machine (must fail after grace period)
- [ ] **Tampering Test**: Modify license file (must detect and reject)
- [ ] **Generation Test**: Purchase → license generation → activation (must work seamlessly)

### Enterprise Features Must:
- [ ] **Multi-tenant**: Create isolated workspaces with proper DB separation
- [ ] **MCP Servers**: Deploy and manage custom integrations successfully
- [ ] **SSO Integration**: Connect with enterprise identity providers
- [ ] **Source Access**: Provide repository access to enterprise customers

---

## 💰 REVENUE PROTECTION VALIDATION

### Test Scenarios:
1. **Developer tries to access enterprise features** → Blocked with upgrade prompt
2. **Professional user hits document limit** → Graceful handling with upgrade option
3. **Enterprise customer loses license** → Grace period, then feature reduction
4. **License sharing attempt** → Hardware fingerprint mismatch detection

### Acceptance Criteria:
- **0% bypass rate** in penetration testing
- **<1 second** license validation time
- **100% feature segregation** working correctly
- **Seamless upgrade flow** from payment to activation

This implementation plan ensures bulletproof license protection while maintaining excellent user experience.
