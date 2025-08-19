# ContextLite Cloud - Technical Implementation Guide

## Executive Summary
Transform ContextLite from a single binary into a multi-tenant SaaS offering in 2-3 weeks, enabling recurring revenue of $49-99/month per customer with minimal infrastructure changes.

---

## 1. Architecture Overview

### Current State
```
Single Binary → Local SQLite → REST API → AI Tools
```

### Target State
```
Multi-Tenant Cloud Service
├── Load Balancer (Cloudflare)
├── API Gateway (Nginx/Caddy)
├── ContextLite Service (Modified Binary)
│   ├── Tenant Router
│   ├── Usage Tracker
│   └── License Validator
├── Storage Layer
│   ├── Tenant Isolation (SQLite per tenant)
│   └── Shared Config (PostgreSQL for user/billing)
└── Supporting Services
    ├── Auth (Clerk/Auth0)
    ├── Billing (Stripe)
    └── Monitoring (Prometheus/Grafana)
```

---

## 2. Technical Implementation

### 2.1 Multi-Tenant Architecture

#### Database Isolation Strategy
```go
// internal/storage/tenant_manager.go
package storage

import (
    "fmt"
    "path/filepath"
    "sync"
    "time"
)

type TenantManager struct {
    basePath string
    cache    map[string]*Storage
    mu       sync.RWMutex
    maxConns int
}

func NewTenantManager(basePath string) *TenantManager {
    return &TenantManager{
        basePath: basePath,
        cache:    make(map[string]*Storage),
        maxConns: 100, // Max concurrent tenant connections
    }
}

func (tm *TenantManager) GetTenantStorage(tenantID string) (*Storage, error) {
    tm.mu.RLock()
    if storage, exists := tm.cache[tenantID]; exists {
        tm.mu.RUnlock()
        return storage, nil
    }
    tm.mu.RUnlock()
    
    // Create new storage for tenant
    tm.mu.Lock()
    defer tm.mu.Unlock()
    
    dbPath := filepath.Join(tm.basePath, tenantID, "context.db")
    storage, err := New(dbPath)
    if err != nil {
        return nil, fmt.Errorf("failed to create tenant storage: %w", err)
    }
    
    tm.cache[tenantID] = storage
    return storage, nil
}

// Cleanup inactive tenant connections
func (tm *TenantManager) CleanupInactive() {
    ticker := time.NewTicker(5 * time.Minute)
    for range ticker.C {
        tm.mu.Lock()
        // Remove connections idle > 30 minutes
        for tenantID, storage := range tm.cache {
            if storage.LastAccessed().Before(time.Now().Add(-30 * time.Minute)) {
                storage.Close()
                delete(tm.cache, tenantID)
            }
        }
        tm.mu.Unlock()
    }
}
```

#### Tenant Context Middleware
```go
// internal/api/middleware/tenant.go
package middleware

import (
    "context"
    "net/http"
    "strings"
)

type TenantKey string
const TenantIDKey TenantKey = "tenant_id"

func TenantExtractor(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        var tenantID string
        
        // Method 1: Subdomain (customer.contextlite.cloud)
        host := r.Host
        if parts := strings.Split(host, "."); len(parts) > 2 {
            tenantID = parts[0]
        }
        
        // Method 2: API Key header
        if tenantID == "" {
            apiKey := r.Header.Get("X-API-Key")
            if apiKey != "" {
                tenantID = extractTenantFromAPIKey(apiKey)
            }
        }
        
        // Method 3: JWT claim
        if tenantID == "" {
            tenantID = extractTenantFromJWT(r.Header.Get("Authorization"))
        }
        
        if tenantID == "" {
            http.Error(w, "Tenant identification required", 401)
            return
        }
        
        ctx := context.WithValue(r.Context(), TenantIDKey, tenantID)
        next.ServeHTTP(w, r.WithContext(ctx))
    })
}
```

### 2.2 Usage Tracking & Billing

#### Usage Metrics Collection
```go
// internal/billing/usage.go
package billing

import (
    "sync"
    "time"
)

type UsageTracker struct {
    metrics map[string]*TenantUsage
    mu      sync.RWMutex
    stripe  *StripeClient
}

type TenantUsage struct {
    TenantID      string
    Queries       int64
    TokensUsed    int64
    StorageBytes  int64
    LastReset     time.Time
}

func (ut *UsageTracker) TrackQuery(tenantID string, tokens int64) {
    ut.mu.Lock()
    defer ut.mu.Unlock()
    
    if _, exists := ut.metrics[tenantID]; !exists {
        ut.metrics[tenantID] = &TenantUsage{
            TenantID:  tenantID,
            LastReset: time.Now(),
        }
    }
    
    ut.metrics[tenantID].Queries++
    ut.metrics[tenantID].TokensUsed += tokens
    
    // Check if limit exceeded
    if ut.shouldUpgradeTier(tenantID) {
        ut.notifyTierUpgrade(tenantID)
    }
}

func (ut *UsageTracker) GetMonthlyUsage(tenantID string) *TenantUsage {
    ut.mu.RLock()
    defer ut.mu.RUnlock()
    return ut.metrics[tenantID]
}

// Report to Stripe for billing
func (ut *UsageTracker) ReportUsageToStripe() {
    for tenantID, usage := range ut.metrics {
        ut.stripe.ReportUsage(tenantID, usage)
    }
}
```

#### Stripe Integration
```go
// internal/billing/stripe.go
package billing

import (
    "github.com/stripe/stripe-go/v74"
    "github.com/stripe/stripe-go/v74/subscription"
    "github.com/stripe/stripe-go/v74/usagerecord"
)

type StripeClient struct {
    apiKey string
}

func NewStripeClient(apiKey string) *StripeClient {
    stripe.Key = apiKey
    return &StripeClient{apiKey: apiKey}
}

func (sc *StripeClient) CreateSubscription(tenantID, email, tier string) (*stripe.Subscription, error) {
    params := &stripe.SubscriptionParams{
        Customer: stripe.String(tenantID),
        Items: []*stripe.SubscriptionItemsParams{
            {
                Price: stripe.String(getTierPriceID(tier)),
            },
        },
        Metadata: map[string]string{
            "tenant_id": tenantID,
            "tier":      tier,
        },
    }
    
    return subscription.New(params)
}

func (sc *StripeClient) ReportUsage(tenantID string, usage *TenantUsage) error {
    params := &stripe.UsageRecordParams{
        Quantity:  stripe.Int64(usage.Queries),
        Timestamp: stripe.Int64(time.Now().Unix()),
        Action:    stripe.String("set"),
    }
    
    _, err := usagerecord.New(params)
    return err
}

func getTierPriceID(tier string) string {
    tiers := map[string]string{
        "free":       "price_free",
        "starter":    "price_1234_49",     // $49/month
        "pro":        "price_5678_99",     // $99/month
        "enterprise": "price_9012_499",    // $499/month
    }
    return tiers[tier]
}
```

### 2.3 Authentication & Authorization

#### Clerk Integration
```go
// internal/auth/clerk.go
package auth

import (
    "github.com/clerk/clerk-sdk-go/clerk"
    "net/http"
)

type ClerkAuth struct {
    client clerk.Client
}

func NewClerkAuth(apiKey string) *ClerkAuth {
    client, _ := clerk.NewClient(apiKey)
    return &ClerkAuth{client: client}
}

func (ca *ClerkAuth) VerifyRequest(r *http.Request) (*TenantInfo, error) {
    sessionToken := r.Header.Get("Authorization")
    
    claims, err := ca.client.VerifyToken(sessionToken)
    if err != nil {
        return nil, err
    }
    
    return &TenantInfo{
        TenantID: claims.Subject,
        Email:    claims.Email,
        Tier:     claims.Metadata["tier"].(string),
        Limits:   getTierLimits(claims.Metadata["tier"].(string)),
    }, nil
}

type TenantInfo struct {
    TenantID string
    Email    string
    Tier     string
    Limits   TierLimits
}

type TierLimits struct {
    QueriesPerMonth int64
    TokensPerQuery  int64
    MaxDocuments    int64
    MaxWorkspaces   int
}

func getTierLimits(tier string) TierLimits {
    limits := map[string]TierLimits{
        "free": {
            QueriesPerMonth: 1000,
            TokensPerQuery:  4000,
            MaxDocuments:    1000,
            MaxWorkspaces:   1,
        },
        "starter": {
            QueriesPerMonth: 100000,
            TokensPerQuery:  8000,
            MaxDocuments:    10000,
            MaxWorkspaces:   5,
        },
        "pro": {
            QueriesPerMonth: -1, // Unlimited
            TokensPerQuery:  16000,
            MaxDocuments:    -1,
            MaxWorkspaces:   -1,
        },
    }
    return limits[tier]
}
```

### 2.4 API Rate Limiting

```go
// internal/api/middleware/ratelimit.go
package middleware

import (
    "golang.org/x/time/rate"
    "sync"
)

type RateLimiter struct {
    limiters map[string]*rate.Limiter
    mu       sync.RWMutex
    
    // Tier-based limits
    tierLimits map[string]rate.Limit
}

func NewRateLimiter() *RateLimiter {
    return &RateLimiter{
        limiters: make(map[string]*rate.Limiter),
        tierLimits: map[string]rate.Limit{
            "free":    rate.Limit(10),   // 10 req/sec
            "starter": rate.Limit(50),   // 50 req/sec
            "pro":     rate.Limit(200),  // 200 req/sec
        },
    }
}

func (rl *RateLimiter) GetLimiter(tenantID, tier string) *rate.Limiter {
    rl.mu.Lock()
    defer rl.mu.Unlock()
    
    if limiter, exists := rl.limiters[tenantID]; exists {
        return limiter
    }
    
    limit := rl.tierLimits[tier]
    limiter := rate.NewLimiter(limit, int(limit)*10) // Burst = 10x rate
    rl.limiters[tenantID] = limiter
    
    return limiter
}
```

---

## 3. Infrastructure Setup

### 3.1 Docker Configuration

```dockerfile
# Dockerfile.saas
FROM golang:1.21-alpine AS builder
WORKDIR /app
COPY go.mod go.sum ./
RUN go mod download
COPY . .
RUN go build -o contextlite-saas ./cmd/contextlite

FROM alpine:latest
RUN apk --no-cache add ca-certificates
WORKDIR /root/
COPY --from=builder /app/contextlite-saas .
COPY --from=builder /app/configs ./configs

EXPOSE 8080
CMD ["./contextlite-saas", "-mode=saas"]
```

### 3.2 Docker Compose (Development)

```yaml
# docker-compose.yml
version: '3.8'

services:
  contextlite:
    build:
      context: .
      dockerfile: Dockerfile.saas
    ports:
      - "8080:8080"
    environment:
      - MODE=saas
      - STRIPE_KEY=${STRIPE_KEY}
      - CLERK_API_KEY=${CLERK_API_KEY}
      - TENANT_DATA_PATH=/data/tenants
    volumes:
      - tenant_data:/data/tenants
      - ./configs:/app/configs
    depends_on:
      - postgres
      - redis

  postgres:
    image: postgres:15-alpine
    environment:
      POSTGRES_DB: contextlite_saas
      POSTGRES_USER: contextlite
      POSTGRES_PASSWORD: ${DB_PASSWORD}
    volumes:
      - postgres_data:/var/lib/postgresql/data
    ports:
      - "5432:5432"

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis_data:/data

  caddy:
    image: caddy:2-alpine
    ports:
      - "80:80"
      - "443:443"
    volumes:
      - ./Caddyfile:/etc/caddy/Caddyfile
      - caddy_data:/data
      - caddy_config:/config

volumes:
  tenant_data:
  postgres_data:
  redis_data:
  caddy_data:
  caddy_config:
```

### 3.3 Caddy Configuration (Auto-SSL)

```caddyfile
# Caddyfile
*.contextlite.cloud {
    tls {
        dns cloudflare {env.CF_API_TOKEN}
    }
    
    reverse_proxy contextlite:8080 {
        header_up X-Tenant-Domain {labels.0}
        header_up X-Real-IP {remote_host}
    }
    
    encode gzip
    
    # Rate limiting
    rate_limit {remote_host} 100r/s
}

contextlite.cloud {
    reverse_proxy contextlite:8080
    encode gzip
}
```

---

## 4. Railway/Render Deployment

### 4.1 Railway Configuration

```toml
# railway.toml
[build]
builder = "DOCKERFILE"
dockerfilePath = "Dockerfile.saas"

[deploy]
startCommand = "./contextlite-saas -mode=saas"
healthcheckPath = "/health"
healthcheckTimeout = 30
restartPolicyType = "ON_FAILURE"
restartPolicyMaxRetries = 3

[[services]]
name = "contextlite-api"
port = 8080

[services.domains]
"contextlite.cloud" = {}
"*.contextlite.cloud" = {}
```

### 4.2 Environment Variables

```bash
# .env.production
MODE=saas
PORT=8080

# Storage
TENANT_DATA_PATH=/data/tenants
MAX_TENANTS=10000
MAX_STORAGE_PER_TENANT=1GB

# Auth
CLERK_API_KEY=sk_live_YOUR_CLERK_SECRET_KEY
CLERK_FRONTEND_API=pk_live_YOUR_CLERK_PUBLISHABLE_KEY

# Billing
STRIPE_SECRET_KEY=sk_live_YOUR_STRIPE_SECRET_KEY
STRIPE_WEBHOOK_SECRET=whsec_YOUR_WEBHOOK_SECRET
STRIPE_PRICE_STARTER=price_YOUR_STARTER_PRICE_ID
STRIPE_PRICE_PRO=price_YOUR_PRO_PRICE_ID

# Database (for user/billing data)
DATABASE_URL=postgresql://user:pass@host/contextlite_saas

# Redis (for caching/sessions)
REDIS_URL=redis://default:pass@host:6379

# Monitoring
SENTRY_DSN=https://xxx@sentry.io/xxx
PROMETHEUS_ENABLED=true
```

---

## 5. Database Schema (User/Billing)

```sql
-- migrations/001_saas_tables.sql

-- Tenants table
CREATE TABLE tenants (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    slug VARCHAR(255) UNIQUE NOT NULL, -- subdomain
    name VARCHAR(255) NOT NULL,
    email VARCHAR(255) NOT NULL,
    tier VARCHAR(50) DEFAULT 'free',
    stripe_customer_id VARCHAR(255),
    stripe_subscription_id VARCHAR(255),
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW()
);

-- API Keys
CREATE TABLE api_keys (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    tenant_id UUID REFERENCES tenants(id) ON DELETE CASCADE,
    key_hash VARCHAR(255) UNIQUE NOT NULL,
    name VARCHAR(255),
    last_used TIMESTAMP,
    created_at TIMESTAMP DEFAULT NOW(),
    expires_at TIMESTAMP
);

-- Usage tracking
CREATE TABLE usage_events (
    id BIGSERIAL PRIMARY KEY,
    tenant_id UUID REFERENCES tenants(id) ON DELETE CASCADE,
    event_type VARCHAR(50), -- 'query', 'document_add', etc
    tokens_used INTEGER,
    metadata JSONB,
    created_at TIMESTAMP DEFAULT NOW()
);

-- Billing events
CREATE TABLE billing_events (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    tenant_id UUID REFERENCES tenants(id) ON DELETE CASCADE,
    stripe_event_id VARCHAR(255) UNIQUE,
    event_type VARCHAR(50),
    amount INTEGER, -- in cents
    currency VARCHAR(3) DEFAULT 'USD',
    metadata JSONB,
    created_at TIMESTAMP DEFAULT NOW()
);

-- Indexes
CREATE INDEX idx_tenants_stripe_customer ON tenants(stripe_customer_id);
CREATE INDEX idx_tenants_tier ON tenants(tier);
CREATE INDEX idx_usage_events_tenant_date ON usage_events(tenant_id, created_at);
CREATE INDEX idx_api_keys_hash ON api_keys(key_hash);
```

---

## 6. Onboarding Flow

### 6.1 Signup Handler

```go
// internal/api/onboarding.go
package api

func (s *Server) HandleSignup(w http.ResponseWriter, r *http.Request) {
    var req SignupRequest
    json.NewDecoder(r.Body).Decode(&req)
    
    // 1. Create Clerk user
    clerkUser, err := s.clerk.CreateUser(req.Email, req.Password)
    if err != nil {
        http.Error(w, "Failed to create user", 500)
        return
    }
    
    // 2. Create tenant
    tenant := &Tenant{
        ID:    generateTenantID(),
        Slug:  generateSlug(req.CompanyName),
        Name:  req.CompanyName,
        Email: req.Email,
        Tier:  "free",
    }
    
    // 3. Create Stripe customer
    stripeCustomer, err := s.stripe.CreateCustomer(tenant)
    tenant.StripeCustomerID = stripeCustomer.ID
    
    // 4. Save to database
    err = s.db.CreateTenant(tenant)
    
    // 5. Initialize tenant storage
    tenantStorage, err := s.tenantManager.GetTenantStorage(tenant.ID)
    tenantStorage.Initialize()
    
    // 6. Send welcome email
    s.email.SendWelcome(tenant.Email, tenant.Slug)
    
    // 7. Return success with auto-login token
    token := s.clerk.GenerateLoginToken(clerkUser.ID)
    json.NewEncoder(w).Encode(SignupResponse{
        TenantID: tenant.ID,
        Slug:     tenant.Slug,
        Token:    token,
        URL:      fmt.Sprintf("https://%s.contextlite.cloud", tenant.Slug),
    })
}
```

### 6.2 Quick Start Guide (Auto-Generated)

```go
func (s *Server) GenerateQuickStart(tenantID string) string {
    apiKey := s.generateAPIKey(tenantID)
    
    return fmt.Sprintf(`
# Welcome to ContextLite Cloud!

## Your API Endpoint
https://%s.contextlite.cloud/api/v1

## Your API Key
%s

## Quick Start

### 1. Test your connection
curl -H "X-API-Key: %s" \
  https://%s.contextlite.cloud/api/v1/health

### 2. Add documents
curl -X POST \
  -H "X-API-Key: %s" \
  -H "Content-Type: application/json" \
  -d '{"content": "Your document content", "path": "doc1.md"}' \
  https://%s.contextlite.cloud/api/v1/documents

### 3. Query context
curl -X POST \
  -H "X-API-Key: %s" \
  -H "Content-Type: application/json" \
  -d '{"query": "How does authentication work?", "max_tokens": 4000}' \
  https://%s.contextlite.cloud/api/v1/context/assemble

## Python Example
\`\`\`python
import requests

api_key = "%s"
base_url = "https://%s.contextlite.cloud/api/v1"

response = requests.post(
    f"{base_url}/context/assemble",
    headers={"X-API-Key": api_key},
    json={"query": "your query", "max_tokens": 4000}
)
\`\`\`
`, tenantSlug, apiKey, apiKey, tenantSlug, apiKey, tenantSlug, apiKey, tenantSlug, apiKey, tenantSlug)
}
```

---

## 7. Monitoring & Operations

### 7.1 Health Checks

```go
// internal/api/health.go
func (s *Server) HandleHealth(w http.ResponseWriter, r *http.Request) {
    health := map[string]interface{}{
        "status": "healthy",
        "version": VERSION,
        "tenant_count": s.tenantManager.ActiveTenantCount(),
        "uptime": time.Since(s.startTime).Seconds(),
        "checks": map[string]bool{
            "database": s.checkDatabase(),
            "redis": s.checkRedis(),
            "stripe": s.checkStripe(),
            "storage": s.checkStorage(),
        },
    }
    
    json.NewEncoder(w).Encode(health)
}
```

### 7.2 Prometheus Metrics

```go
// internal/metrics/prometheus.go
var (
    tenantsTotal = prometheus.NewGauge(prometheus.GaugeOpts{
        Name: "contextlite_tenants_total",
        Help: "Total number of tenants",
    })
    
    queriesPerSecond = prometheus.NewHistogramVec(
        prometheus.HistogramOpts{
            Name: "contextlite_queries_per_second",
            Help: "Queries per second by tenant",
        },
        []string{"tenant_id", "tier"},
    )
    
    storageBytes = prometheus.NewGaugeVec(
        prometheus.GaugeOpts{
            Name: "contextlite_storage_bytes",
            Help: "Storage used per tenant",
        },
        []string{"tenant_id"},
    )
)
```

---

## 8. Pricing & Tiers

### Tier Structure

| Feature | Free | Starter ($49) | Pro ($99) | Enterprise ($499) |
|---------|------|---------------|-----------|-------------------|
| Queries/month | 1,000 | 100,000 | Unlimited | Unlimited |
| Documents | 1,000 | 10,000 | Unlimited | Unlimited |
| Workspaces | 1 | 5 | Unlimited | Unlimited |
| API Rate Limit | 10 req/s | 50 req/s | 200 req/s | 1000 req/s |
| Support | Community | Email | Priority Email | Phone + Slack |
| SLA | None | None | 99.9% | 99.99% |
| Data Retention | 30 days | 90 days | 1 year | Unlimited |
| Custom Domain | No | No | Yes | Yes |
| SSO | No | No | No | Yes |
| Audit Logs | No | No | Basic | Advanced |

---

## 9. Migration Path

### 9.1 Binary → Cloud Migration Tool

```go
// cmd/migrate-to-cloud/main.go
func migrateToCloud(localDB, tenantID, apiKey string) error {
    // 1. Open local SQLite
    local, err := sql.Open("sqlite", localDB)
    
    // 2. Export all documents
    docs := exportDocuments(local)
    
    // 3. Upload to cloud
    client := NewCloudClient(apiKey)
    for _, doc := range docs {
        client.AddDocument(doc)
    }
    
    // 4. Verify migration
    return client.VerifyMigration(len(docs))
}
```

---

## 10. Timeline & Milestones

### Week 1: Foundation
- [ ] Day 1-2: Set up Railway/Render project
- [ ] Day 3-4: Implement tenant isolation
- [ ] Day 5: Add Clerk authentication
- [ ] Day 6-7: Basic billing integration

### Week 2: Core Features
- [ ] Day 8-9: Usage tracking
- [ ] Day 10-11: Rate limiting
- [ ] Day 12: Onboarding flow
- [ ] Day 13-14: Testing & bug fixes

### Week 3: Polish & Launch
- [ ] Day 15-16: Monitoring setup
- [ ] Day 17: Documentation
- [ ] Day 18: Landing page update
- [ ] Day 19: Beta testing
- [ ] Day 20-21: Launch!

---

## 11. Quick Start Commands

```bash
# Development
docker-compose up -d
go run cmd/contextlite/main.go -mode=saas

# Deploy to Railway
railway login
railway up

# Deploy to Render
render create
render deploy

# Database migrations
migrate -path migrations -database $DATABASE_URL up

# Create first tenant (testing)
curl -X POST https://api.contextlite.cloud/signup \
  -d '{"email": "test@example.com", "company": "Test Inc"}'
```

---

## 12. Revenue Projections

### Conservative Model
- Month 1: 10 paid users = $490 MRR
- Month 3: 50 paid users = $2,450 MRR  
- Month 6: 200 paid users = $9,800 MRR
- Month 12: 500 paid users = $24,500 MRR

### Growth Levers
1. **Free tier virality**: 10:1 free to paid ratio
2. **Usage-based upgrades**: Auto-upgrade when limits hit
3. **Team plans**: $199/month for 5 users
4. **Annual discounts**: 20% off for yearly payment
5. **Referral program**: 30% commission for 3 months

---

## 13. Support & Operations

### Customer Support Tiers
- **Free**: Community Discord
- **Starter**: Email (48hr response)
- **Pro**: Email (24hr response)  
- **Enterprise**: Dedicated Slack + Phone

### Operational Runbook
```bash
# Daily checks
- Monitor error rates
- Check disk usage per tenant
- Review signup funnel metrics

# Weekly tasks  
- Backup all tenant databases
- Review support tickets
- Update usage dashboards

# Monthly tasks
- Bill all customers via Stripe
- Clean up inactive tenants
- Performance optimization review
```

---

## Conclusion

This cloud implementation maintains ContextLite's core simplicity while adding just enough complexity for multi-tenancy. The 2-3 week timeline is aggressive but achievable given your existing codebase.

**Key Success Factors:**
1. Keep using SQLite per tenant (don't over-engineer)
2. Use managed services (Clerk, Stripe, Railway)
3. Start with manual processes, automate later
4. Focus on the onboarding experience
5. Price aggressively to gain market share

**Next Steps:**
1. Set up Railway/Render account
2. Create Stripe products/prices
3. Implement tenant isolation
4. Launch beta with 10 friendly users
5. Iterate based on feedback

The path from $0 to $10K MRR is clear and achievable within 6 months.