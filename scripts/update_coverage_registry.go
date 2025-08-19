package main

import (
	"encoding/json"
	"fmt"
	"log"
	"os"
	"os/exec"
	"regexp"
	"strconv"
	"strings"
	"time"
)

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

type SystemRegistry struct {
	Components     map[string]*Component `json:"components"`
	CriticalAlerts []string             `json:"critical_alerts"`
	LastUpdated    time.Time            `json:"last_updated"`
}

func main() {
	fmt.Println("🔍 Updating registry with accurate test coverage data...")
	
	registry := &SystemRegistry{
		Components:     make(map[string]*Component),
		CriticalAlerts: []string{},
		LastUpdated:    time.Now(),
	}
	
	// Define components to track
	components := map[string]struct {
		name          string
		package_path  string
		priority      string
		revenueImpact string
	}{
		"license-server": {
			name:          "License Server",
			package_path:  "./cmd/license-server",
			priority:      "CRITICAL",
			revenueImpact: "CRITICAL",
		},
		"engine": {
			name:          "Context Engine",
			package_path:  "./internal/engine",
			priority:      "CRITICAL", 
			revenueImpact: "HIGH",
		},
		"api": {
			name:          "API Layer",
			package_path:  "./internal/api",
			priority:      "HIGH",
			revenueImpact: "HIGH",
		},
		"storage": {
			name:          "Storage Layer", 
			package_path:  "./internal/storage",
			priority:      "HIGH",
			revenueImpact: "MEDIUM",
		},
		"pipeline": {
			name:          "Processing Pipeline",
			package_path:  "./internal/pipeline", 
			priority:      "MEDIUM",
			revenueImpact: "MEDIUM",
		},
		"config": {
			name:          "Configuration",
			package_path:  "./pkg/config",
			priority:      "MEDIUM",
			revenueImpact: "LOW",
		},
		"tokens": {
			name:          "Token Processing",
			package_path:  "./pkg/tokens",
			priority:      "MEDIUM", 
			revenueImpact: "LOW",
		},
		"evaluation": {
			name:          "Evaluation System",
			package_path:  "./internal/evaluation",
			priority:      "LOW",
			revenueImpact: "LOW",
		},
		"timing": {
			name:          "Timing Utils",
			package_path:  "./internal/timing",
			priority:      "LOW",
			revenueImpact: "LOW",
		},
		"contextlite": {
			name:          "Main Server",
			package_path:  "./cmd/contextlite",
			priority:      "HIGH",
			revenueImpact: "HIGH",
		},
	}
	
	// Get coverage for each component
	for key, comp := range components {
		fmt.Printf("📊 Analyzing %s...\n", comp.name)
		
		// Add progress indication for slow components
		if key == "license-server" {
			fmt.Printf("  ⏳ Running comprehensive license server tests (may take ~30s)...\n")
		}
		
		coverage, passing, total := getCoverageData(comp.package_path)
		
		registry.Components[key] = &Component{
			Name:            comp.name,
			Package:         comp.package_path,
			Coverage:        coverage,
			TestsPassing:    passing,
			TestsTotal:      total,
			ProductionReady: coverage >= 0.75 && passing == total,
			Priority:        comp.priority,
			RevenueImpact:   comp.revenueImpact,
			LastUpdated:     time.Now(),
		}
		
		fmt.Printf("  ✅ %.1f%% coverage, %d/%d tests passing\n", coverage*100, passing, total)
	}
	
	// Update critical alerts
	updateCriticalAlerts(registry)
	
	// Save registry
	registryPath := "internal/registry/system_registry.json"
	data, err := json.MarshalIndent(registry, "", "  ")
	if err != nil {
		log.Fatalf("Failed to marshal registry: %v", err)
	}
	
	err = os.WriteFile(registryPath, data, 0644)
	if err != nil {
		log.Fatalf("Failed to write registry: %v", err)
	}
	
	fmt.Printf("\n🎯 Registry updated successfully!\n")
	fmt.Printf("📁 Saved to: %s\n", registryPath)
	
	// Print summary
	printSummary(registry)
}

func getCoverageData(packagePath string) (coverage float64, passing int, total int) {
	// Clean up any existing temp coverage file
	os.Remove("temp_coverage.out")
	
	// Run go test with coverage and timeout
	cmd := exec.Command("go", "test", "-timeout", "60s", "-coverprofile=temp_coverage.out", packagePath)
	output, err := cmd.CombinedOutput()
	
	// Always clean up the temp file after use
	defer os.Remove("temp_coverage.out")
	
	if err != nil {
		fmt.Printf("  ⚠️  Test execution failed for %s: %v\n", packagePath, err)
		fmt.Printf("  📝 Output: %s\n", string(output))
		return 0.0, 0, 0
	}
	
	outputStr := string(output)
	
	// Parse coverage percentage
	coverageRegex := regexp.MustCompile(`coverage: ([\d.]+)% of statements`)
	if matches := coverageRegex.FindStringSubmatch(outputStr); len(matches) > 1 {
		if covFloat, err := strconv.ParseFloat(matches[1], 64); err == nil {
			coverage = covFloat / 100.0
		}
	}
	
	// Parse test results
	lines := strings.Split(outputStr, "\n")
	for _, line := range lines {
		if strings.Contains(line, "PASS") && strings.Contains(line, packagePath) {
			passing++
			total++
		} else if strings.Contains(line, "FAIL") && strings.Contains(line, packagePath) {
			total++
		}
	}
	
	// If no specific test results found, count by test functions
	if total == 0 {
		// Count PASS/FAIL from individual test functions
		passRegex := regexp.MustCompile(`--- PASS: Test\w+`)
		failRegex := regexp.MustCompile(`--- FAIL: Test\w+`)
		
		passing = len(passRegex.FindAllString(outputStr, -1))
		failing := len(failRegex.FindAllString(outputStr, -1))
		total = passing + failing
	}
	
	// Clean up temporary file
	os.Remove("temp_coverage.out")
	
	return coverage, passing, total
}

func updateCriticalAlerts(registry *SystemRegistry) {
	registry.CriticalAlerts = []string{}
	
	for _, component := range registry.Components {
		if component.RevenueImpact == "CRITICAL" && !component.ProductionReady {
			registry.CriticalAlerts = append(registry.CriticalAlerts,
				fmt.Sprintf("CRITICAL: %s not production ready (%.1f%% coverage)",
					component.Name, component.Coverage*100))
		}
		
		if component.Priority == "CRITICAL" && component.Coverage < 0.8 {
			registry.CriticalAlerts = append(registry.CriticalAlerts,
				fmt.Sprintf("LOW_COVERAGE: %s below 80%% coverage (%.1f%%)",
					component.Name, component.Coverage*100))
		}
		
		if component.TestsTotal > 0 {
			passRate := float64(component.TestsPassing) / float64(component.TestsTotal)
			if passRate < 0.9 {
				registry.CriticalAlerts = append(registry.CriticalAlerts,
					fmt.Sprintf("TEST_FAILURES: %s has failing tests (%d/%d passing)",
						component.Name, component.TestsPassing, component.TestsTotal))
			}
		}
	}
}

func printSummary(registry *SystemRegistry) {
	fmt.Printf("\n📈 COVERAGE SUMMARY:\n")
	fmt.Printf("==================\n")
	
	// Group by priority
	critical := []*Component{}
	high := []*Component{}
	medium := []*Component{}
	low := []*Component{}
	
	for _, comp := range registry.Components {
		switch comp.Priority {
		case "CRITICAL":
			critical = append(critical, comp)
		case "HIGH":
			high = append(high, comp)
		case "MEDIUM":
			medium = append(medium, comp)
		case "LOW":
			low = append(low, comp)
		}
	}
	
	printGroup("CRITICAL", critical)
	printGroup("HIGH", high)
	printGroup("MEDIUM", medium)
	printGroup("LOW", low)
	
	if len(registry.CriticalAlerts) > 0 {
		fmt.Printf("\n🚨 CRITICAL ALERTS:\n")
		for _, alert := range registry.CriticalAlerts {
			fmt.Printf("  ❌ %s\n", alert)
		}
	} else {
		fmt.Printf("\n✅ No critical alerts!\n")
	}
}

func printGroup(priority string, components []*Component) {
	if len(components) == 0 {
		return
	}
	
	fmt.Printf("\n%s Priority:\n", priority)
	for _, comp := range components {
		status := "🔴"
		if comp.ProductionReady {
			status = "✅"
		} else if comp.Coverage >= 0.5 {
			status = "🟡"
		}
		
		fmt.Printf("  %s %-20s %.1f%% (%d/%d tests)\n",
			status, comp.Name, comp.Coverage*100, comp.TestsPassing, comp.TestsTotal)
	}
}
