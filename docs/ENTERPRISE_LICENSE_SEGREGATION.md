# Enterprise License Feature Segregation

## Overview

ContextLite implements strict license-based feature segregation ensuring that enterprise features are only available to valid enterprise license holders. The system includes:

- **License validation** with RSA signature verification
- **Hardware fingerprinting** to prevent license sharing
- **Grace period** for new users (14 days)
- **Feature gates** that block unauthorized access
- **Automatic upgrades prompts** with direct purchase links

## License Tiers & Features

### Developer (Free)
- ✅ Single workspace
- ✅ Up to 10,000 documents
- ✅ Basic SMT optimization
- ✅ Community support
- ❌ Commercial use
- ❌ Advanced features

### Professional ($99)
- ✅ Unlimited workspaces (personal)
- ✅ Unlimited documents
- ✅ Advanced SMT features
- ✅ 7D scoring system
- ✅ Commercial license
- ✅ Priority support
- ✅ REST API access
- ❌ Enterprise features

### Enterprise ($2,999)
- ✅ **All Professional features**
- ✅ **Multi-tenant architecture**
- ✅ **SSO/LDAP integration**
- ✅ **Custom MCP servers**
- ✅ **White-label licensing**
- ✅ **Source code access**
- ✅ **On-premise deployment**
- ✅ **24/7 SLA support**
- ✅ **Team deployment tools**
- ✅ **Advanced analytics**
- ✅ **Audit trails**
- ✅ **Compliance reporting**

## Technical Implementation

### 1. License Validation System

```go
// License manager validates cryptographic signatures
licenseManager, err := license.NewLicenseManager()

// Feature gate enforces access control
featureGate := features.NewFeatureGate(licenseManager)

// Check enterprise features
if err := featureGate.ValidateMultiTenant(); err != nil {
    return fmt.Errorf("enterprise license required: %w", err)
}
```

### 2. Feature Gate Integration

**Enterprise Multi-Tenant:**
```go
// In tenant.go CreateTenant()
if err := tm.featureGate.ValidateMultiTenant(); err != nil {
    return nil, err // Blocks tenant creation without enterprise license
}
```

**Custom MCP Servers:**
```go
// In mcp.go CreateMCPServer()
if err := mm.featureGate.ValidateCustomMCP(); err != nil {
    return nil, err // Blocks MCP creation without enterprise license
}
```

**Document Limits:**
```go
// Enforced based on license tier
if err := featureGate.ValidateUnlimitedDocs(docCount); err != nil {
    return err // Blocks document addition when limit exceeded
}
```

### 3. Hardware Fingerprinting

```go
// Prevents license sharing across machines
hardwareID, err := getHardwareFingerprint()
if license.HardwareID != hardwareID {
    return errors.New("license not valid for this machine")
}
```

### 4. Grace Period Management

```go
// 14-day grace period for new users
if !licenseManager.HasValidLicense() && !licenseManager.IsInGracePeriod() {
    return errors.New("license required - grace period expired")
}
```

## Enterprise Feature Blocking

### Multi-Tenant Architecture
- **Blocks:** Tenant creation, tenant management, domain routing
- **Error:** "enterprise license required for multi-tenant workspaces"
- **Upgrade:** Links to https://contextlite.com/enterprise

### SSO/LDAP Integration
- **Blocks:** SAML/OAuth setup, Active Directory sync, role management
- **Error:** "enterprise license required for SSO/LDAP integration"
- **Upgrade:** Links to enterprise purchase

### Custom MCP Servers
- **Blocks:** MCP server creation, Jira/Slack integrations, custom protocols
- **Error:** "enterprise license required for custom MCP servers"
- **Upgrade:** Prompts enterprise license purchase

### White-Label Licensing
- **Blocks:** Brand customization, OEM licensing, API-only deployments
- **Error:** "enterprise license required for white-label licensing"
- **Upgrade:** Enterprise upgrade required

### Source Code Access
- **Blocks:** Repository access, modification rights, security audits
- **Error:** "enterprise license required for source code access"
- **Upgrade:** Enterprise tier only

### Team Deployment Tools
- **Blocks:** Admin console, user management, group policies
- **Error:** "enterprise license required for team deployment tools"
- **Upgrade:** Enterprise license needed

## API Response Examples

### Unauthorized Enterprise Feature Access

```json
HTTP 403 Forbidden
{
  "error": "enterprise license required for multi-tenant workspaces",
  "upgrade_url": "https://contextlite.com/enterprise",
  "feature": "multi_tenant",
  "current_tier": "professional",
  "required_tier": "enterprise"
}
```

### Document Limit Exceeded

```json
HTTP 403 Forbidden
{
  "error": "developer tier limited to 10,000 documents (current: 15,000)",
  "upgrade_url": "https://contextlite.com/pricing",
  "current_limit": 10000,
  "attempted_count": 15000,
  "tier": "developer"
}
```

### Grace Period Warning

```json
HTTP 200 OK
{
  "data": { /* normal response */ },
  "warning": "unlicensed usage - 3 days remaining in grace period",
  "purchase_url": "https://contextlite.com/pricing",
  "grace_expires": "2025-08-31T00:00:00Z"
}
```

## CLI Integration

```bash
# Enterprise feature attempts
$ contextlite create-tenant acme-corp
Error: enterprise license required for multi-tenant workspaces
Upgrade at: https://contextlite.com/enterprise

$ contextlite create-mcp-server jira
Error: enterprise license required for custom MCP servers  
Upgrade at: https://contextlite.com/enterprise

# Document limit enforcement
$ contextlite add-documents large-dataset/
Error: developer tier limited to 10,000 documents (current: 12,500)
Upgrade at: https://contextlite.com/pricing
```

## VS Code Extension Integration

The VS Code extension respects license tiers:

```typescript
// Check feature availability before showing UI
const licenseStatus = await contextlite.getLicenseStatus();

if (!licenseStatus.enterprise) {
    // Hide enterprise features in command palette
    // Show upgrade prompts for enterprise actions
    vscode.window.showWarningMessage(
        'Enterprise license required for multi-tenant workspaces',
        'Upgrade'
    ).then(selection => {
        if (selection === 'Upgrade') {
            vscode.env.openExternal(vscode.Uri.parse('https://contextlite.com/enterprise'));
        }
    });
}
```

## Security Measures

### 1. Cryptographic License Validation
- RSA-2048 signature verification
- Tamper-proof license files
- Hardware binding prevents sharing

### 2. Grace Period Tracking
- First-run timestamp recorded
- 14-day limit strictly enforced
- Automatic feature reduction post-grace

### 3. Feature Flag Architecture
- Clean separation of free/pro/enterprise code paths
- Compile-time feature exclusion possible
- Runtime validation at every access point

## Testing License Segregation

```bash
# Test enterprise features without license
go run examples/enterprise/main.go
# Output: Shows blocked features and upgrade prompts

# Test with professional license
export CONTEXTLITE_LICENSE="pro-license-key"
go run examples/enterprise/main.go
# Output: Professional features available, enterprise blocked

# Test with enterprise license  
export CONTEXTLITE_LICENSE="enterprise-license-key"
go run examples/enterprise/main.go
# Output: All features available
```

## Compliance & Auditing

Enterprise licenses include audit trails:

```go
// Log all feature access attempts
auditLog.Record(AuditEvent{
    User:      "user@company.com",
    Feature:   "multi_tenant",
    Action:    "create_tenant", 
    Allowed:   false,
    Reason:    "insufficient_license",
    Timestamp: time.Now(),
})
```

This ensures complete traceability of feature usage and license compliance for enterprise customers.

## Purchase Integration

All upgrade prompts include direct links to Stripe checkout:

- **Professional:** https://buy.stripe.com/PROFESSIONAL_LINK
- **Enterprise:** https://buy.stripe.com/8x2eV5fRj58XdDJ6q27N601

The license system automatically validates new purchases and activates features within minutes of payment completion.
