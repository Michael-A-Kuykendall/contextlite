package main

import (
	"fmt"
	"log"
	"database/sql"
	"github.com/Michael-A-Kuykendall/contextlite/internal/license"
	"github.com/Michael-A-Kuykendall/contextlite/internal/features"
	"github.com/Michael-A-Kuykendall/contextlite/internal/enterprise"
	_ "modernc.org/sqlite"
)

// Example integration showing license-gated enterprise features
func main() {
	// Initialize database
	db, err := sql.Open("sqlite", "contextlite.db")
	if err != nil {
		log.Fatal(err)
	}
	defer db.Close()

	// Initialize license manager
	licenseManager, err := license.NewLicenseManager()
	if err != nil {
		log.Fatal("Failed to initialize license manager:", err)
	}

	// Initialize feature gate
	featureGate := features.NewFeatureGate(licenseManager)

	// Check license status
	status := featureGate.GetLicenseStatus()
	fmt.Printf("License Status: %+v\n", status)

	// Example 1: Multi-tenant operations (Enterprise only)
	if err := featureGate.ValidateMultiTenant(); err != nil {
		fmt.Printf("Multi-tenant blocked: %v\n", err)
	} else {
		fmt.Println("✅ Multi-tenant features available")
		
		// Initialize tenant manager with feature gate
		tenantManager := enterprise.NewTenantManager(db, featureGate)
		
		// Create enterprise tenant
		settings := enterprise.TenantSettings{
			MaxUsers:     100,
			MaxDocuments: 1000000,
			SSOEnabled:   true,
			CustomMCP:    true,
		}
		
		tenant, err := tenantManager.CreateTenant("Acme Corp", "acme-corp", "org-123", settings)
		if err != nil {
			fmt.Printf("Failed to create tenant: %v\n", err)
		} else {
			fmt.Printf("✅ Created tenant: %s\n", tenant.Name)
		}
	}

	// Example 2: Custom MCP server creation (Enterprise only)
	if err := featureGate.ValidateCustomMCP(); err != nil {
		fmt.Printf("Custom MCP blocked: %v\n", err)
	} else {
		fmt.Println("✅ Custom MCP features available")
		
		// Initialize MCP manager with feature gate
		mcpManager := enterprise.NewMCPManager(db, featureGate)
		
		// Create Jira integration
		jiraServer, err := mcpManager.CreateJiraIntegration("tenant-123", "https://acme.atlassian.net", "api-token")
		if err != nil {
			fmt.Printf("Failed to create Jira integration: %v\n", err)
		} else {
			fmt.Printf("✅ Created Jira MCP server: %s\n", jiraServer.Name)
		}
	}

	// Example 3: Document limit enforcement
	docCount := 15000 // Simulate large document count
	if err := featureGate.ValidateUnlimitedDocs(docCount); err != nil {
		fmt.Printf("Document limit exceeded: %v\n", err)
	} else {
		fmt.Printf("✅ Document count %d within limits\n", docCount)
	}

	// Example 4: Professional features
	if err := featureGate.ValidateCommercialUse(); err != nil {
		fmt.Printf("Commercial use blocked: %v\n", err)
	} else {
		fmt.Println("✅ Commercial usage allowed")
	}

	// Example 5: API access validation
	if err := featureGate.ValidateAPI(); err != nil {
		fmt.Printf("API access blocked: %v\n", err)
	} else {
		fmt.Println("✅ REST API access granted")
	}

	// Print feature availability summary
	fmt.Println("\n=== Feature Availability ===")
	features := status["features"].(map[string]bool)
	for feature, available := range features {
		status := "❌"
		if available {
			status = "✅"
		}
		fmt.Printf("%s %s\n", status, feature)
	}
}

// Example HTTP handler that validates features
func handleCreateTenant(featureGate *features.FeatureGate) {
	// Validate enterprise license before allowing tenant creation
	if err := featureGate.ValidateMultiTenant(); err != nil {
		// Return 403 Forbidden with upgrade message
		fmt.Printf("HTTP 403: %v\n", err)
		return
	}
	
	// Proceed with tenant creation...
	fmt.Println("✅ Tenant creation authorized")
}

// Example CLI command that respects license limits
func handleAddDocuments(featureGate *features.FeatureGate, currentCount, newDocs int) {
	totalDocs := currentCount + newDocs
	
	if err := featureGate.ValidateUnlimitedDocs(totalDocs); err != nil {
		fmt.Printf("Cannot add documents: %v\n", err)
		return
	}
	
	fmt.Printf("✅ Adding %d documents (total: %d)\n", newDocs, totalDocs)
}

// Example white-label validation
func handleWhiteLabelRequest(featureGate *features.FeatureGate) {
	if err := featureGate.ValidateWhiteLabel(); err != nil {
		fmt.Printf("White-label request denied: %v\n", err)
		return
	}
	
	fmt.Println("✅ White-label licensing available")
}
