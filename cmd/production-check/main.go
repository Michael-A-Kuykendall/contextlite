package main

import (
	"encoding/json"
	"fmt"
	"os"
)

type Component struct {
	ProductionReady bool   `json:"production_ready"`
	Priority        string `json:"priority"`
	Name            string `json:"name"`
	Coverage        float64 `json:"coverage"`
}

type Registry struct {
	Components         map[string]Component `json:"components"`
	SystemHealth       string               `json:"system_health"`
	ProductionReadiness float64             `json:"production_readiness"`
}

func main() {
	data, err := os.ReadFile("system_registry.json")
	if err != nil {
		fmt.Println("❌ No registry found - run 'make test-registry' first")
		os.Exit(1)
	}

	var r Registry
	if err := json.Unmarshal(data, &r); err != nil {
		fmt.Printf("❌ Error parsing registry: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("System Health: %s\n", r.SystemHealth)
	fmt.Printf("Production Readiness: %.1f%%\n", r.ProductionReadiness)

	blockers := 0
	for _, comp := range r.Components {
		if comp.Priority == "CRITICAL" && !comp.ProductionReady {
			fmt.Printf("❌ BLOCKER: %s not production ready (%.1f%% coverage)\n", comp.Name, comp.Coverage*100)
			blockers++
		}
	}

	if blockers == 0 {
		fmt.Println("✅ All critical components are production ready!")
	} else {
		fmt.Printf("🔴 %d critical components blocking production\n", blockers)
		os.Exit(1)
	}
}
