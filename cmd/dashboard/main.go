package main

import (
	"encoding/json"
	"fmt"
	"os"
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

func main() {
	// Load registry
	data, err := os.ReadFile("system_registry.json")
	if err != nil {
		fmt.Println("❌ No registry found. Run 'make test-registry' first.")
		return
	}

	var registry Registry
	if err := json.Unmarshal(data, &registry); err != nil {
		fmt.Printf("❌ Error parsing registry: %v\n", err)
		return
	}

	printDashboard(&registry)
}

func printDashboard(registry *Registry) {
	fmt.Println("╔══════════════════════════════════════════════════════════════╗")
	fmt.Println("║                🎯 CONTEXTLITE SYSTEM DASHBOARD               ║")
	fmt.Println("╚══════════════════════════════════════════════════════════════╝")
	fmt.Println()

	// System Overview
	healthIcon := getHealthIcon(registry.SystemHealth)
	fmt.Printf("📊 SYSTEM OVERVIEW\n")
	fmt.Printf("   Health: %s %s\n", healthIcon, registry.SystemHealth)
	fmt.Printf("   Production Readiness: %.1f%%\n", registry.ProductionReadiness)
	fmt.Printf("   Overall Coverage: %.1f%%\n", registry.OverallCoverage*100)
	fmt.Printf("   Last Updated: %s\n", registry.LastUpdate.Format("2006-01-02 15:04:05"))
	fmt.Println()

	// Critical Alerts
	if len(registry.CriticalAlerts) > 0 {
		fmt.Printf("🚨 CRITICAL ALERTS (%d)\n", len(registry.CriticalAlerts))
		for _, alert := range registry.CriticalAlerts {
			fmt.Printf("   • %s\n", alert)
		}
		fmt.Println()
	}

	// Component Status
	fmt.Println("📋 COMPONENT STATUS")
	fmt.Println("┌─────────────────────┬──────────┬───────────┬─────────────┬──────────┐")
	fmt.Println("│ Component           │ Coverage │ Tests     │ Prod Ready  │ Priority │")
	fmt.Println("├─────────────────────┼──────────┼───────────┼─────────────┼──────────┤")

	// Sort components by priority
	criticalComponents := []*Component{}
	highComponents := []*Component{}
	mediumComponents := []*Component{}

	for _, comp := range registry.Components {
		switch comp.Priority {
		case "CRITICAL":
			criticalComponents = append(criticalComponents, comp)
		case "HIGH":
			highComponents = append(highComponents, comp)
		default:
			mediumComponents = append(mediumComponents, comp)
		}
	}

	// Print components in priority order
	allComponents := append(append(criticalComponents, highComponents...), mediumComponents...)
	for _, comp := range allComponents {
		name := truncateString(comp.Name, 19)
		coverage := fmt.Sprintf("%.1f%%", comp.Coverage*100)
		tests := fmt.Sprintf("%d/%d", comp.TestsPassing, comp.TestsTotal)
		prodReady := getReadinessIcon(comp.ProductionReady)
		priority := getPriorityIcon(comp.Priority)

		fmt.Printf("│ %-19s │ %8s │ %9s │ %11s │ %8s │\n",
			name, coverage, tests, prodReady, priority)
	}

	fmt.Println("└─────────────────────┴──────────┴───────────┴─────────────┴──────────┘")
	fmt.Println()

	// Production Readiness Check
	fmt.Println("🎯 PRODUCTION READINESS CHECK")
	criticalReady := 0
	criticalTotal := 0
	for _, comp := range registry.Components {
		if comp.Priority == "CRITICAL" {
			criticalTotal++
			if comp.ProductionReady {
				criticalReady++
			}
		}
	}

	if criticalTotal > 0 {
		fmt.Printf("   Critical Components: %d/%d ready (%.1f%%)\n",
			criticalReady, criticalTotal, float64(criticalReady)/float64(criticalTotal)*100)
	}

	// Production blockers
	blockers := []string{}
	for _, comp := range registry.Components {
		if comp.Priority == "CRITICAL" && !comp.ProductionReady {
			reason := "Unknown"
			if comp.Coverage < 0.8 {
				reason = fmt.Sprintf("Coverage %.1f%% < 80%%", comp.Coverage*100)
			} else if comp.TestsPassing != comp.TestsTotal {
				reason = fmt.Sprintf("Tests failing: %d/%d", comp.TestsPassing, comp.TestsTotal)
			}
			blockers = append(blockers, fmt.Sprintf("%s (%s)", comp.Name, reason))
		}
	}

	if len(blockers) > 0 {
		fmt.Printf("   🔴 Production Blockers:\n")
		for _, blocker := range blockers {
			fmt.Printf("      • %s\n", blocker)
		}
	} else {
		fmt.Printf("   ✅ No critical blockers!\n")
	}

	fmt.Println()

	// Next Steps
	fmt.Println("🚀 RECOMMENDED ACTIONS")
	if registry.ProductionReadiness < 100 {
		fmt.Println("   1. Fix critical component issues listed above")
		fmt.Println("   2. Run 'make test-registry' to update status")
		fmt.Println("   3. Verify with 'make production-check'")
	} else {
		fmt.Println("   ✅ All systems go for production!")
	}

	fmt.Println()
	fmt.Println("📁 Registry Files:")
	fmt.Println("   • system_registry.json (Machine-readable)")
	fmt.Println("   • SYSTEM_REGISTRY.md (Human-readable)")
	fmt.Println()
	fmt.Println("🔄 Update registry: make test-registry")
	fmt.Println("📊 View this dashboard: make dashboard")
}

func getHealthIcon(health string) string {
	switch health {
	case "PRODUCTION_READY":
		return "✅"
	case "TESTING_COMPLETE":
		return "🟡"
	case "TESTING_IN_PROGRESS":
		return "🟡"
	default:
		return "🔴"
	}
}

func getReadinessIcon(ready bool) string {
	if ready {
		return "✅ YES"
	}
	return "🔴 NO"
}

func getPriorityIcon(priority string) string {
	switch priority {
	case "CRITICAL":
		return "🔴 CRIT"
	case "HIGH":
		return "🟠 HIGH"
	case "MEDIUM":
		return "🟡 MED"
	default:
		return "🟢 LOW"
	}
}

func truncateString(s string, length int) string {
	if len(s) <= length {
		return s
	}
	return s[:length-3] + "..."
}
