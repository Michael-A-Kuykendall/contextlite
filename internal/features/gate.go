package features

import (
	"fmt"
	"contextlite/internal/license"
)

// FeatureGate controls access to premium features
type FeatureGate struct {
	licenseManager *license.LicenseManager
}

// NewFeatureGate creates a new feature gate with license enforcement
func NewFeatureGate(licenseManager *license.LicenseManager) *FeatureGate {
	return &FeatureGate{
		licenseManager: licenseManager,
	}
}

// Enterprise Feature Constants
const (
	FeatureMultiTenant      = "multi_tenant"
	FeatureSSOLDAP          = "sso_ldap" 
	FeatureCustomMCP        = "custom_mcp"
	FeatureWhiteLabel       = "white_label"
	FeatureSourceAccess     = "source_access"
	FeatureSLASupport       = "sla_support"
	FeatureCustomIntegrations = "custom_integrations"
	FeatureTeamDeployment   = "team_deployment"
	FeatureOnPremise        = "on_premise"
	FeatureAnalytics        = "analytics"
)

// Professional Feature Constants  
const (
	FeatureUnlimitedDocs    = "unlimited_docs"
	FeatureAdvancedSMT      = "advanced_smt"
	FeatureCommercialUse    = "commercial_use"
	FeaturePrioritySupport  = "priority_support"
	FeatureAPI              = "api"
	Feature7DScoring        = "7d_scoring"
)

// Enterprise Feature Validation

// RequireEnterprise validates enterprise license for multi-tenant operations
func (fg *FeatureGate) RequireEnterprise(operation string) error {
	if !fg.licenseManager.HasFeature(FeatureMultiTenant) {
		return fmt.Errorf("enterprise license required for %s - upgrade at https://contextlite.com/enterprise", operation)
	}
	return nil
}

// ValidateMultiTenant checks if multi-tenant features are available
func (fg *FeatureGate) ValidateMultiTenant() error {
	return fg.RequireEnterprise("multi-tenant workspaces")
}

// ValidateSSO checks if SSO/LDAP integration is available
func (fg *FeatureGate) ValidateSSO() error {
	if !fg.licenseManager.HasFeature(FeatureSSOLDAP) {
		return fmt.Errorf("enterprise license required for SSO/LDAP integration - upgrade at https://contextlite.com/enterprise")
	}
	return nil
}

// ValidateCustomMCP checks if custom MCP server creation is available
func (fg *FeatureGate) ValidateCustomMCP() error {
	if !fg.licenseManager.HasFeature(FeatureCustomMCP) {
		return fmt.Errorf("enterprise license required for custom MCP servers - upgrade at https://contextlite.com/enterprise")
	}
	return nil
}

// ValidateWhiteLabel checks if white-label licensing is available
func (fg *FeatureGate) ValidateWhiteLabel() error {
	if !fg.licenseManager.HasFeature(FeatureWhiteLabel) {
		return fmt.Errorf("enterprise license required for white-label licensing - upgrade at https://contextlite.com/enterprise")
	}
	return nil
}

// ValidateSourceAccess checks if source code access is available
func (fg *FeatureGate) ValidateSourceAccess() error {
	if !fg.licenseManager.HasFeature(FeatureSourceAccess) {
		return fmt.Errorf("enterprise license required for source code access - upgrade at https://contextlite.com/enterprise")
	}
	return nil
}

// ValidateTeamDeployment checks if team deployment tools are available
func (fg *FeatureGate) ValidateTeamDeployment() error {
	if !fg.licenseManager.HasFeature(FeatureTeamDeployment) {
		return fmt.Errorf("enterprise license required for team deployment tools - upgrade at https://contextlite.com/enterprise")
	}
	return nil
}

// ValidateOnPremise checks if on-premise deployment is available
func (fg *FeatureGate) ValidateOnPremise() error {
	if !fg.licenseManager.HasFeature(FeatureOnPremise) {
		return fmt.Errorf("enterprise license required for on-premise deployment - upgrade at https://contextlite.com/enterprise")
	}
	return nil
}

// ValidateAnalytics checks if advanced analytics are available
func (fg *FeatureGate) ValidateAnalytics() error {
	if !fg.licenseManager.HasFeature(FeatureAnalytics) {
		return fmt.Errorf("enterprise license required for advanced analytics - upgrade at https://contextlite.com/enterprise")
	}
	return nil
}

// Professional Feature Validation

// RequireProfessional validates professional or enterprise license
func (fg *FeatureGate) RequireProfessional(operation string) error {
	tier := fg.licenseManager.GetTier()
	if tier != license.TierPro && tier != license.TierEnterprise {
		return fmt.Errorf("professional license required for %s - upgrade at https://contextlite.com/pricing", operation)
	}
	return nil
}

// ValidateUnlimitedDocs checks if unlimited documents are available
func (fg *FeatureGate) ValidateUnlimitedDocs(docCount int) error {
	tier := fg.licenseManager.GetTier()
	
	switch tier {
	case license.TierDeveloper:
		if docCount > 10000 {
			return fmt.Errorf("developer tier limited to 10,000 documents (current: %d) - upgrade at https://contextlite.com/pricing", docCount)
		}
	case license.TierPro, license.TierEnterprise:
		// Unlimited for paid tiers
		return nil
	default:
		// Grace period - allow up to 1000 docs
		if docCount > 1000 {
			return fmt.Errorf("unlicensed usage limited to 1,000 documents during grace period - get license at https://contextlite.com/pricing")
		}
	}
	
	return nil
}

// ValidateCommercialUse checks if commercial usage is allowed
func (fg *FeatureGate) ValidateCommercialUse() error {
	return fg.RequireProfessional("commercial usage")
}

// ValidateAdvancedSMT checks if advanced SMT features are available
func (fg *FeatureGate) ValidateAdvancedSMT() error {
	return fg.RequireProfessional("advanced SMT optimization")
}

// ValidateAPI checks if REST API access is available
func (fg *FeatureGate) ValidateAPI() error {
	return fg.RequireProfessional("REST API access")
}

// Validate7DScoring checks if 7D feature scoring is available
func (fg *FeatureGate) Validate7DScoring() error {
	return fg.RequireProfessional("7D feature scoring")
}

// Document Limits by Tier
func (fg *FeatureGate) GetDocumentLimit() int {
	tier := fg.licenseManager.GetTier()
	
	switch tier {
	case license.TierDeveloper:
		return 10000
	case license.TierPro, license.TierEnterprise:
		return -1 // Unlimited
	default:
		if fg.licenseManager.IsInGracePeriod() {
			return 1000 // Grace period limit
		}
		return 100 // Unlicensed strict limit
	}
}

// User Limits by Tier
func (fg *FeatureGate) GetUserLimit() int {
	tier := fg.licenseManager.GetTier()
	
	switch tier {
	case license.TierDeveloper:
		return 1
	case license.TierPro:
		return 10
	case license.TierEnterprise:
		return -1 // Unlimited
	default:
		return 1 // Unlicensed single user
	}
}

// Feature Availability Check
func (fg *FeatureGate) IsFeatureAvailable(feature string) bool {
	return fg.licenseManager.HasFeature(feature)
}

// Get License Status for UI
func (fg *FeatureGate) GetLicenseStatus() map[string]interface{} {
	tier := fg.licenseManager.GetTier()
	
	return map[string]interface{}{
		"tier":            string(tier),
		"doc_limit":       fg.GetDocumentLimit(),
		"user_limit":      fg.GetUserLimit(),
		"grace_period":    fg.licenseManager.IsInGracePeriod(),
		"enterprise":      tier == license.TierEnterprise,
		"professional":    tier == license.TierPro || tier == license.TierEnterprise,
		"features": map[string]bool{
			"multi_tenant":        fg.IsFeatureAvailable(FeatureMultiTenant),
			"sso_ldap":           fg.IsFeatureAvailable(FeatureSSOLDAP),
			"custom_mcp":         fg.IsFeatureAvailable(FeatureCustomMCP),
			"white_label":        fg.IsFeatureAvailable(FeatureWhiteLabel),
			"source_access":      fg.IsFeatureAvailable(FeatureSourceAccess),
			"team_deployment":    fg.IsFeatureAvailable(FeatureTeamDeployment),
			"unlimited_docs":     fg.IsFeatureAvailable(FeatureUnlimitedDocs),
			"advanced_smt":       fg.IsFeatureAvailable(FeatureAdvancedSMT),
			"commercial_use":     fg.IsFeatureAvailable(FeatureCommercialUse),
			"priority_support":   fg.IsFeatureAvailable(FeaturePrioritySupport),
			"api":               fg.IsFeatureAvailable(FeatureAPI),
			"7d_scoring":        fg.IsFeatureAvailable(Feature7DScoring),
		},
	}
}
