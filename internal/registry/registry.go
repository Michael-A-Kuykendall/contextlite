package registry

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// SystemComponent represents a component in our system registry
type SystemComponent struct {
	Name             string             `json:"name"`
	Package          string             `json:"package"`
	Coverage         float64            `json:"coverage"`
	TestsPassing     int                `json:"tests_passing"`
	TestsTotal       int                `json:"tests_total"`
	ProductionReady  bool               `json:"production_ready"`
	Priority         string             `json:"priority"` // CRITICAL, HIGH, MEDIUM, LOW
	RevenueImpact    string             `json:"revenue_impact"` // CRITICAL, HIGH, MEDIUM, LOW
	LastUpdated      time.Time          `json:"last_updated"`
	Functions        []FunctionInfo     `json:"functions"`
	Dependencies     []string           `json:"dependencies"`
	PerformanceMetrics map[string]string `json:"performance_metrics"`
}

// FunctionInfo represents a function in the system
type FunctionInfo struct {
	Name         string    `json:"name"`
	Purpose      string    `json:"purpose"`
	Tested       bool      `json:"tested"`
	Performance  string    `json:"performance"`
	Security     string    `json:"security"`
	LastTested   time.Time `json:"last_tested"`
}

// TestResult represents the result of a test run
type TestResult struct {
	Name       string        `json:"name"`
	Package    string        `json:"package"`
	Passed     bool          `json:"passed"`
	Duration   time.Duration `json:"duration"`
	Coverage   float64       `json:"coverage"`
	BenchmarkOps int64       `json:"benchmark_ops"`
	BenchmarkNsOp int64      `json:"benchmark_ns_op"`
	Error      string        `json:"error,omitempty"`
}

// SystemRegistry maintains the complete system state
type SystemRegistry struct {
	Components      map[string]*SystemComponent `json:"components"`
	LastUpdate      time.Time                   `json:"last_update"`
	OverallCoverage float64                     `json:"overall_coverage"`
	SystemHealth    string                      `json:"system_health"`
	ProductionReadiness float64                `json:"production_readiness"`
	CriticalAlerts  []string                   `json:"critical_alerts"`
}

// NewSystemRegistry creates a new registry with initial components
func NewSystemRegistry() *SystemRegistry {
	registry := &SystemRegistry{
		Components:     make(map[string]*SystemComponent),
		LastUpdate:     time.Now(),
		SystemHealth:   "TESTING_IN_PROGRESS",
		CriticalAlerts: []string{},
	}

	// Initialize known components
	registry.initializeComponents()
	return registry
}

// initializeComponents sets up the initial system components
func (sr *SystemRegistry) initializeComponents() {
	// License Management System
	sr.Components["license_management"] = &SystemComponent{
		Name:            "License Management",
		Package:         "internal/license",
		Priority:        "CRITICAL",
		RevenueImpact:   "CRITICAL",
		Functions: []FunctionInfo{
			{Name: "GenerateLicense", Purpose: "Create signed license", Performance: "860μs/op"},
			{Name: "ValidateLicense", Purpose: "Verify license signature", Performance: "4.6μs/op"},
			{Name: "parseLicenseData", Purpose: "JSON parsing & validation", Performance: "<1μs"},
			{Name: "generateLicenseKey", Purpose: "Random key generation", Performance: "<1μs"},
			{Name: "getTierFeatures", Purpose: "Feature mapping by tier", Performance: "<1μs"},
		},
		Dependencies: []string{"crypto/rsa", "crypto/rand", "encoding/json"},
		PerformanceMetrics: map[string]string{
			"generation_time": "860μs",
			"validation_time": "4.6μs",
			"key_strength":    "RSA-2048",
		},
	}

	// License Server
	sr.Components["license_server"] = &SystemComponent{
		Name:            "License Server",
		Package:         "cmd/license-server",
		Priority:        "CRITICAL",
		RevenueImpact:   "CRITICAL",
		Functions: []FunctionInfo{
			{Name: "NewLicenseServer", Purpose: "Server initialization", Performance: "140ms"},
			{Name: "handleGenerateLicense", Purpose: "License API endpoint", Performance: "150ms"},
			{Name: "handleValidateLicense", Purpose: "Validation endpoint", Performance: "190ms"},
			{Name: "handleStripeWebhook", Purpose: "Payment processing", Performance: "100ms"},
			{Name: "generateAndSendLicense", Purpose: "Complete workflow", Performance: "180ms"},
			{Name: "determineLicenseTier", Purpose: "Payment → tier mapping", Performance: "<1ms"},
			{Name: "sendLicenseEmail", Purpose: "Email delivery", Performance: "230ms"},
		},
		Dependencies: []string{"github.com/stripe/stripe-go/v74", "internal/license", "net/optimizationp"},
		PerformanceMetrics: map[string]string{
			"api_response_time": "150ms",
			"webhook_processing": "100ms",
			"email_delivery": "230ms",
		},
	}

	// Core Engine
	sr.Components["core_engine"] = &SystemComponent{
		Name:            "Core Engine",
		Package:         "internal/engine",
		Priority:        "HIGH",
		RevenueImpact:   "MEDIUM",
		Functions: []FunctionInfo{
			{Name: "NewEngine", Purpose: "Engine initialization", Performance: "50ms"},
			{Name: "Query", Purpose: "Context retrieval", Performance: "100ms"},
			{Name: "AddDocument", Purpose: "Document indexing", Performance: "10ms"},
			{Name: "scoreDocuments", Purpose: "Relevance scoring", Performance: "50ms"},
			{Name: "probabilisticSelection", Purpose: "Result selection", Performance: "?ms"},
		},
		Dependencies: []string{"modernc.org/sqlite", "pkg/storage", "pkg/types"},
		PerformanceMetrics: map[string]string{
			"query_time": "100ms",
			"indexing_time": "10ms",
			"scoring_time": "50ms",
		},
	}

	// Storage Layer
	sr.Components["storage"] = &SystemComponent{
		Name:            "Storage Layer",
		Package:         "pkg/storage",
		Priority:        "HIGH",
		RevenueImpact:   "LOW",
		Functions: []FunctionInfo{
			{Name: "NewStorage", Purpose: "Storage initialization"},
			{Name: "AddDocument", Purpose: "Document persistence"},
			{Name: "SearchDocuments", Purpose: "FTS5 search"},
			{Name: "GetStats", Purpose: "Usage statistics"},
		},
		Dependencies: []string{"modernc.org/sqlite"},
		PerformanceMetrics: map[string]string{
			"insert_time": "5ms",
			"search_time": "20ms",
			"fts5_performance": "excellent",
		},
	}

	// REST API
	sr.Components["rest_api"] = &SystemComponent{
		Name:            "REST API",
		Package:         "cmd/contextlite",
		Priority:        "HIGH",
		RevenueImpact:   "LOW",
		Functions: []FunctionInfo{
			{Name: "handleQuery", Purpose: "Query endpoint"},
			{Name: "handleAddDocument", Purpose: "Document addition"},
			{Name: "handleHealth", Purpose: "Health check"},
			{Name: "handleStats", Purpose: "Statistics endpoint"},
		},
		Dependencies: []string{"net/http", "pkg/contextlite"},
		PerformanceMetrics: map[string]string{
			"response_time": "200ms",
			"throughput": "1000 req/s",
		},
	}

	// VS Code Extension
	sr.Components["vscode_extension"] = &SystemComponent{
		Name:            "VS Code Extension",
		Package:         "vscode-extension",
		Priority:        "MEDIUM",
		RevenueImpact:   "LOW",
		Functions: []FunctionInfo{
			{Name: "activate", Purpose: "Extension activation"},
			{Name: "indexWorkspace", Purpose: "Workspace indexing"},
			{Name: "provideContext", Purpose: "Context provision"},
		},
		Dependencies: []string{"vscode", "@types/node"},
		PerformanceMetrics: map[string]string{
			"activation_time": "500ms",
			"indexing_speed": "1000 files/s",
		},
	}
}

// UpdateFromTestRun updates the registry based on test results
func (sr *SystemRegistry) UpdateFromTestRun(results []TestResult) {
	sr.LastUpdate = time.Now()
	
	for _, result := range results {
		component := sr.getComponentByPackage(result.Package)
		if component == nil {
			continue
		}

		// Update test counts
		if result.Passed {
			component.TestsPassing++
		}
		component.TestsTotal++
		
		// Update coverage
		if result.Coverage > 0 {
			component.Coverage = result.Coverage
		}

		// Update performance metrics
		if result.BenchmarkNsOp > 0 {
			component.PerformanceMetrics[result.Name] = fmt.Sprintf("%dns/op", result.BenchmarkNsOp)
		}

		// Update production readiness
		component.ProductionReady = component.Coverage >= 0.8 && 
			float64(component.TestsPassing)/float64(component.TestsTotal) >= 0.9

		component.LastUpdated = time.Now()
	}

	sr.calculateOverallMetrics()
	sr.updateCriticalAlerts()
}

// getComponentByPackage finds a component by package name
func (sr *SystemRegistry) getComponentByPackage(packageName string) *SystemComponent {
	for _, component := range sr.Components {
		if strings.Contains(packageName, component.Package) ||
		   strings.Contains(component.Package, packageName) {
			return component
		}
	}
	return nil
}

// calculateOverallMetrics computes system-wide metrics
func (sr *SystemRegistry) calculateOverallMetrics() {
	totalCoverage := 0.0
	productionReadyCount := 0
	totalComponents := len(sr.Components)

	for _, component := range sr.Components {
		totalCoverage += component.Coverage
		if component.ProductionReady {
			productionReadyCount++
		}
	}

	sr.OverallCoverage = totalCoverage / float64(totalComponents)
	sr.ProductionReadiness = float64(productionReadyCount) / float64(totalComponents) * 100

	// Determine system health
	if sr.ProductionReadiness >= 90 {
		sr.SystemHealth = "PRODUCTION_READY"
	} else if sr.ProductionReadiness >= 75 {
		sr.SystemHealth = "TESTING_COMPLETE"
	} else if sr.ProductionReadiness >= 50 {
		sr.SystemHealth = "TESTING_IN_PROGRESS"
	} else {
		sr.SystemHealth = "TESTING_REQUIRED"
	}
}

// updateCriticalAlerts identifies critical issues
func (sr *SystemRegistry) updateCriticalAlerts() {
	sr.CriticalAlerts = []string{}

	for _, component := range sr.Components {
		if component.RevenueImpact == "CRITICAL" && !component.ProductionReady {
			sr.CriticalAlerts = append(sr.CriticalAlerts, 
				fmt.Sprintf("CRITICAL: %s not production ready (%.1f%% coverage)", 
					component.Name, component.Coverage*100))
		}
		
		if component.Priority == "CRITICAL" && component.Coverage < 0.8 {
			sr.CriticalAlerts = append(sr.CriticalAlerts, 
				fmt.Sprintf("LOW_COVERAGE: %s below 80%% coverage (%.1f%%)", 
					component.Name, component.Coverage*100))
		}

		if component.TestsTotal > 0 {
			passRate := float64(component.TestsPassing) / float64(component.TestsTotal)
			if passRate < 0.9 {
				sr.CriticalAlerts = append(sr.CriticalAlerts, 
					fmt.Sprintf("FAILING_TESTS: %s has %.1f%% test pass rate", 
						component.Name, passRate*100))
			}
		}
	}
}

// SaveToFile saves the registry to a JSON file
func (sr *SystemRegistry) SaveToFile(filepath string) error {
	data, err := json.MarshalIndent(sr, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal registry: %w", err)
	}

	return os.WriteFile(filepath, data, 0644)
}

// LoadFromFile loads the registry from a JSON file
func LoadFromFile(filepath string) (*SystemRegistry, error) {
	data, err := os.ReadFile(filepath)
	if err != nil {
		return nil, fmt.Errorf("failed to read registry file: %w", err)
	}

	var registry SystemRegistry
	if err := json.Unmarshal(data, &registry); err != nil {
		return nil, fmt.Errorf("failed to unmarshal registry: %w", err)
	}

	return &registry, nil
}

// GenerateMarkdownReport generates a markdown report of the current state
func (sr *SystemRegistry) GenerateMarkdownReport() string {
	var report strings.Builder

	// Header
	report.WriteString("# ContextLite System Registry & Test Dashboard\n")
	report.WriteString(fmt.Sprintf("*Auto-updated: %s*\n\n", sr.LastUpdate.Format("2006-01-02 15:04:05")))

	// Overview
	report.WriteString("## 🎯 SYSTEM OVERVIEW\n")
	report.WriteString(fmt.Sprintf("**System Health**: %s\n", sr.SystemHealth))
	report.WriteString(fmt.Sprintf("**Overall Coverage**: %.1f%%\n", sr.OverallCoverage*100))
	report.WriteString(fmt.Sprintf("**Production Readiness**: %.1f%%\n\n", sr.ProductionReadiness))

	// Critical Alerts
	if len(sr.CriticalAlerts) > 0 {
		report.WriteString("## 🚨 CRITICAL ALERTS\n")
		for _, alert := range sr.CriticalAlerts {
			report.WriteString(fmt.Sprintf("- %s\n", alert))
		}
		report.WriteString("\n")
	}

	// Components
	report.WriteString("## 📊 COMPONENT STATUS\n\n")
	report.WriteString("| Component | Coverage | Tests | Production Ready | Priority |\n")
	report.WriteString("|-----------|----------|-------|------------------|----------|\n")

	for _, component := range sr.Components {
		status := "🔴 NO"
		if component.ProductionReady {
			status = "✅ YES"
		} else if component.Coverage > 0.6 {
			status = "🟡 PARTIAL"
		}

		testStatus := fmt.Sprintf("%d/%d", component.TestsPassing, component.TestsTotal)
		if component.TestsTotal == 0 {
			testStatus = "NO TESTS"
		}

		priorityIcon := "🟢"
		if component.Priority == "CRITICAL" {
			priorityIcon = "🔴"
		} else if component.Priority == "HIGH" {
			priorityIcon = "🟠"
		}

		report.WriteString(fmt.Sprintf("| %s | %.1f%% | %s | %s | %s %s |\n",
			component.Name,
			component.Coverage*100,
			testStatus,
			status,
			priorityIcon,
			component.Priority))
	}

	return report.String()
}

// UpdateRegistryFromTestOutput updates the registry from go test output
func UpdateRegistryFromTestOutput(testOutput string, registryPath string) error {
	// Load existing registry or create new one
	registry, err := LoadFromFile(registryPath)
	if err != nil {
		registry = NewSystemRegistry()
	}

	// Parse test output for results
	results := parseTestOutput(testOutput)
	
	// Update registry
	registry.UpdateFromTestRun(results)
	
	// Save updated registry
	if err := registry.SaveToFile(registryPath); err != nil {
		return fmt.Errorf("failed to save registry: %w", err)
	}

	// Generate and save markdown report
	markdownPath := strings.Replace(registryPath, ".json", ".md", 1)
	report := registry.GenerateMarkdownReport()
	if err := os.WriteFile(markdownPath, []byte(report), 0644); err != nil {
		return fmt.Errorf("failed to save markdown report: %w", err)
	}

	return nil
}

// parseTestOutput parses go test output into structured results
func parseTestOutput(output string) []TestResult {
	var results []TestResult
	lines := strings.Split(output, "\n")
	
	for _, line := range lines {
		line = strings.TrimSpace(line)
		
		// Parse test results
		if strings.HasPrefix(line, "--- PASS:") || strings.HasPrefix(line, "--- FAIL:") {
			parts := strings.Fields(line)
			if len(parts) >= 3 {
				result := TestResult{
					Name:   strings.TrimSuffix(parts[2], ":"),
					Passed: strings.Contains(line, "PASS"),
				}
				
				// Extract duration if present
				if len(parts) >= 4 && strings.HasPrefix(parts[3], "(") {
					durationStr := strings.Trim(parts[3], "()")
					if duration, err := time.ParseDuration(durationStr); err == nil {
						result.Duration = duration
					}
				}
				
				results = append(results, result)
			}
		}
		
		// Parse coverage information
		if strings.Contains(line, "coverage:") {
			// Parse coverage percentage
			// Example: "coverage: 85.2% of statements"
		}
		
		// Parse benchmark results
		if strings.HasPrefix(line, "Benchmark") && strings.Contains(line, "ns/op") {
			// Parse benchmark data
			// Example: "BenchmarkLicenseGeneration-24 1418 860242 ns/op"
		}
	}
	
	return results
}

// GetRegistryPath returns the default registry file path
func GetRegistryPath() string {
	return filepath.Join(".", "system_registry.json")
}
