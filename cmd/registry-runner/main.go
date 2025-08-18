package main

import (
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"strings"
	"time"
)

// Component represents a system component
type Component struct {
	Name            string    `json:"name"`
	Package         string    `json:"package"`
	Coverage        float64   `json:"coverage"`
	TestsPassing    int       `json:"tests_passing"`
	TestsTotal      int       `json:"tests_total"`
	ProductionReady bool      `json:"production_ready"`
	Priority        string    `json:"priority"`
	RevenueImpact   string    `json:"revenue_impact"`
	LastUpdated     time.Time `json:"last_updated"`
}

// Registry represents the system registry
type Registry struct {
	Components         map[string]*Component `json:"components"`
	LastUpdate         time.Time             `json:"last_update"`
	OverallCoverage    float64               `json:"overall_coverage"`
	SystemHealth       string                `json:"system_health"`
	ProductionReadiness float64              `json:"production_readiness"`
	CriticalAlerts     []string              `json:"critical_alerts"`
}

// ComponentTest represents a test configuration
type ComponentTest struct {
	ID           string
	Name         string
	Package      string
	Priority     string
	RevenueImpact string
}

func main() {
	fmt.Println("🚀 ContextLite System Registry Test Runner")
	fmt.Println("==========================================")

	// Define components to test
	components := []ComponentTest{
		{"license_management", "License Management", "./internal/license/...", "CRITICAL", "CRITICAL"},
		{"license_server", "License Server", "./cmd/license-server/...", "CRITICAL", "CRITICAL"},
		{"core_engine", "Core Engine", "./internal/engine/...", "HIGH", "MEDIUM"},
		{"client", "Client Library", "./pkg/contextlite/...", "HIGH", "MEDIUM"},
		{"rest_api", "REST API", "./cmd/contextlite/...", "HIGH", "MEDIUM"},
	}

	// Load or create registry
	registry := loadOrCreateRegistry()

	// Test each component
	for _, comp := range components {
		fmt.Printf("\n🔍 Testing %s...\n", comp.Name)
		testComponent(registry, comp)
	}

	// Calculate overall metrics
	calculateOverallMetrics(registry)

	// Save registry
	saveRegistry(registry)

	// Update markdown
	updateMarkdown(registry)

	// Print summary
	printSummary(registry)
}

func loadOrCreateRegistry() *Registry {
	registry := &Registry{
		Components: make(map[string]*Component),
		LastUpdate: time.Now(),
	}

	// Try to load existing registry
	if data, err := os.ReadFile("system_registry.json"); err == nil {
		json.Unmarshal(data, registry)
	}

	return registry
}

func testComponent(registry *Registry, comp ComponentTest) {
	// Special handling for different test configurations
	var testPath string
	
	switch comp.ID {
	case "license_management":
		// License tests are in test/license but cover internal/license
		testPath = "./test/license/..."
	default:
		testPath = comp.Package
	}
	
	// Run tests with coverage
	var cmd *exec.Cmd
	if comp.ID == "license_management" {
		// For license management, we need to test the license tests but measure coverage of internal/license
		cmd = exec.Command("go", "test", "-v", "-coverpkg=./internal/license/...", "-coverprofile=temp_coverage.out", testPath)
	} else {
		cmd = exec.Command("go", "test", "-v", "-coverprofile=temp_coverage.out", testPath)
	}
	
	output, err := cmd.CombinedOutput()

	// Parse test results
	passed := strings.Count(string(output), "--- PASS:")
	failed := strings.Count(string(output), "--- FAIL:")
	total := passed + failed

	// Parse coverage
	coverage := 0.0
	if err == nil {
		coverageCmd := exec.Command("go", "tool", "cover", "-func=temp_coverage.out")
		if coverageOutput, coverageErr := coverageCmd.Output(); coverageErr == nil {
			coverageLines := strings.Split(string(coverageOutput), "\n")
			for _, line := range coverageLines {
				if strings.Contains(line, "total:") {
					parts := strings.Fields(line)
					if len(parts) >= 3 {
						coverageStr := strings.TrimSuffix(parts[2], "%")
						if _, err := fmt.Sscanf(coverageStr, "%f", &coverage); err == nil {
							coverage = coverage / 100.0
						}
					}
				}
			}
		}
	}

	// Clean up temp file
	os.Remove("temp_coverage.out")

	// Update registry
	if registry.Components[comp.ID] == nil {
		registry.Components[comp.ID] = &Component{}
	}

	component := registry.Components[comp.ID]
	component.Name = comp.Name
	component.Package = comp.Package
	component.Coverage = coverage
	component.TestsPassing = passed
	component.TestsTotal = total
	component.Priority = comp.Priority
	component.RevenueImpact = comp.RevenueImpact
	component.LastUpdated = time.Now()

	// Determine production readiness
	component.ProductionReady = coverage >= 0.8 && passed == total && total > 0

	// Print results
	status := "✅ PASS"
	if err != nil {
		status = "❌ FAIL"
	}

	fmt.Printf("   Status: %s\n", status)
	fmt.Printf("   Coverage: %.1f%%\n", coverage*100)
	fmt.Printf("   Tests: %d/%d passed\n", passed, total)
	fmt.Printf("   Production Ready: %v\n", component.ProductionReady)
}

func calculateOverallMetrics(registry *Registry) {
	if len(registry.Components) == 0 {
		return
	}

	totalCoverage := 0.0
	productionReadyCount := 0
	totalComponents := len(registry.Components)

	registry.CriticalAlerts = []string{}

	for _, comp := range registry.Components {
		totalCoverage += comp.Coverage
		if comp.ProductionReady {
			productionReadyCount++
		}

		// Check for critical alerts
		if comp.RevenueImpact == "CRITICAL" && !comp.ProductionReady {
			registry.CriticalAlerts = append(registry.CriticalAlerts,
				fmt.Sprintf("CRITICAL: %s not production ready (%.1f%% coverage)",
					comp.Name, comp.Coverage*100))
		}
	}

	registry.OverallCoverage = totalCoverage / float64(totalComponents)
	registry.ProductionReadiness = float64(productionReadyCount) / float64(totalComponents) * 100
	registry.LastUpdate = time.Now()

	// Determine system health
	if registry.ProductionReadiness >= 90 {
		registry.SystemHealth = "PRODUCTION_READY"
	} else if registry.ProductionReadiness >= 75 {
		registry.SystemHealth = "TESTING_COMPLETE"
	} else if registry.ProductionReadiness >= 50 {
		registry.SystemHealth = "TESTING_IN_PROGRESS"
	} else {
		registry.SystemHealth = "TESTING_REQUIRED"
	}
}

func saveRegistry(registry *Registry) {
	data, err := json.MarshalIndent(registry, "", "  ")
	if err != nil {
		fmt.Printf("❌ Error saving registry: %v\n", err)
		return
	}

	if err := os.WriteFile("system_registry.json", data, 0644); err != nil {
		fmt.Printf("❌ Error writing registry file: %v\n", err)
		return
	}

	fmt.Println("\n✅ Registry updated: system_registry.json")
}

func updateMarkdown(registry *Registry) {
	// Generate complete markdown from registry data
	content := generateMarkdownFromRegistry(registry)
	
	if err := os.WriteFile("SYSTEM_REGISTRY.md", []byte(content), 0644); err != nil {
		fmt.Printf("⚠️  Could not save SYSTEM_REGISTRY.md: %v\n", err)
		return
	}

	fmt.Println("✅ SYSTEM_REGISTRY.md updated")
}

func generateMarkdownFromRegistry(registry *Registry) string {
	var md strings.Builder
	
	// Header
	md.WriteString("# ContextLite System Registry & Test Dashboard\n")
	md.WriteString("*Auto-updated comprehensive parts registry for production monitoring*\n\n")
	
	// Overview
	healthIcon := "🔴"
	if registry.SystemHealth == "PRODUCTION_READY" {
		healthIcon = "✅"
	} else if strings.Contains(registry.SystemHealth, "TESTING") {
		healthIcon = "🟡"
	}
	
	md.WriteString("## 🎯 REGISTRY STATUS OVERVIEW\n")
	md.WriteString(fmt.Sprintf("**Last Updated**: %s\n", registry.LastUpdate.Format("2006-01-02 15:04:05")))
	md.WriteString(fmt.Sprintf("**System Health**: %s %s\n", healthIcon, registry.SystemHealth))
	md.WriteString(fmt.Sprintf("**Production Readiness**: %.1f%%\n", registry.ProductionReadiness))
	md.WriteString(fmt.Sprintf("**Overall Coverage**: %.1f%%\n\n", registry.OverallCoverage*100))
	
	// Critical Alerts
	if len(registry.CriticalAlerts) > 0 {
		md.WriteString("## 🚨 CRITICAL ALERTS\n")
		for _, alert := range registry.CriticalAlerts {
			md.WriteString(fmt.Sprintf("- %s\n", alert))
		}
		md.WriteString("\n")
	}
	
	// Component Status
	md.WriteString("## 📊 COMPONENT STATUS\n\n")
	
	// Business-Critical Systems
	md.WriteString("### Business-Critical Systems (Revenue Impact)\n")
	md.WriteString("| Component | Coverage | Test Status | Production Ready | Revenue Impact |\n")
	md.WriteString("|-----------|----------|-------------|------------------|----------------|\n")
	
	for _, comp := range registry.Components {
		if comp.RevenueImpact == "CRITICAL" {
			coverageIcon := "🔴"
			if comp.Coverage >= 0.9 {
				coverageIcon = "✅"
			} else if comp.Coverage >= 0.7 {
				coverageIcon = "🟡"
			}
			
			readyStatus := "🔴 NO"
			if comp.ProductionReady {
				readyStatus = "✅ YES"
			}
			
			testStatus := fmt.Sprintf("%d/%d PASS", comp.TestsPassing, comp.TestsTotal)
			
			md.WriteString(fmt.Sprintf("| %s | %s %.1f%% | %s | %s | 🔴 CRITICAL |\n",
				comp.Name, coverageIcon, comp.Coverage*100, testStatus, readyStatus))
		}
	}
	md.WriteString("\n")
	
	// High Priority Systems
	md.WriteString("### Core Engine Systems\n")
	md.WriteString("| Component | Coverage | Test Status | Production Ready | Priority |\n")
	md.WriteString("|-----------|----------|-------------|------------------|----------|\n")
	
	for _, comp := range registry.Components {
		if comp.Priority == "HIGH" {
			coverageIcon := "🔴"
			if comp.Coverage >= 0.9 {
				coverageIcon = "✅"
			} else if comp.Coverage >= 0.7 {
				coverageIcon = "🟡"
			}
			
			readyStatus := "🔴 NO"
			if comp.ProductionReady {
				readyStatus = "✅ YES"
			} else if comp.Coverage >= 0.6 {
				readyStatus = "🟡 PARTIAL"
			}
			
			testStatus := fmt.Sprintf("%d/%d PASS", comp.TestsPassing, comp.TestsTotal)
			
			md.WriteString(fmt.Sprintf("| %s | %s %.1f%% | %s | %s | 🟠 HIGH |\n",
				comp.Name, coverageIcon, comp.Coverage*100, testStatus, readyStatus))
		}
	}
	md.WriteString("\n")
	
	// Production Readiness Check
	md.WriteString("## 🎯 PRODUCTION READINESS CHECK\n\n")
	
	criticalReady := 0
	criticalTotal := 0
	blockers := []string{}
	
	for _, comp := range registry.Components {
		if comp.Priority == "CRITICAL" {
			criticalTotal++
			if comp.ProductionReady {
				criticalReady++
			} else {
				reason := "Unknown"
				if comp.Coverage < 0.8 {
					reason = fmt.Sprintf("Coverage %.1f%% < 80%%", comp.Coverage*100)
				} else if comp.TestsPassing != comp.TestsTotal {
					reason = fmt.Sprintf("Tests failing: %d/%d", comp.TestsPassing, comp.TestsTotal)
				}
				blockers = append(blockers, fmt.Sprintf("**%s** (%s)", comp.Name, reason))
			}
		}
	}
	
	if criticalTotal > 0 {
		md.WriteString(fmt.Sprintf("**Critical Components Ready**: %d/%d (%.1f%%)\n\n",
			criticalReady, criticalTotal, float64(criticalReady)/float64(criticalTotal)*100))
	}
	
	if len(blockers) > 0 {
		md.WriteString("### 🔴 Production Blockers\n")
		for _, blocker := range blockers {
			md.WriteString(fmt.Sprintf("- %s\n", blocker))
		}
		md.WriteString("\n")
	} else {
		md.WriteString("### ✅ No Critical Blockers\n")
		md.WriteString("All critical components are production ready!\n\n")
	}
	
	// Footer
	md.WriteString("---\n\n")
	md.WriteString("*This registry is automatically maintained by the test suite and updated on every test run.*\n")
	md.WriteString("\n**Commands:**\n")
	md.WriteString("- `make test-registry` - Update registry with latest test results\n")
	md.WriteString("- `make dashboard` - Show interactive dashboard\n")
	md.WriteString("- `make production-check` - Check production readiness\n")
	
	return md.String()
}

func printSummary(registry *Registry) {
	fmt.Println("\n🎉 Registry Update Complete!")
	fmt.Println("============================")
	fmt.Printf("System Health: %s\n", registry.SystemHealth)
	fmt.Printf("Production Readiness: %.1f%%\n", registry.ProductionReadiness)
	fmt.Printf("Overall Coverage: %.1f%%\n", registry.OverallCoverage*100)
	fmt.Printf("Components Tested: %d\n", len(registry.Components))

	if len(registry.CriticalAlerts) > 0 {
		fmt.Println("\n🚨 Critical Alerts:")
		for _, alert := range registry.CriticalAlerts {
			fmt.Printf("   - %s\n", alert)
		}
	}

	fmt.Println("\n📁 Files Generated:")
	fmt.Println("   - system_registry.json (JSON registry)")
	fmt.Println("   - SYSTEM_REGISTRY.md (updated)")
}
