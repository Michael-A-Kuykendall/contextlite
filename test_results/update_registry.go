package main

import (
    "encoding/json"
    "fmt"
    "os"
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

type Registry struct {
    Components         map[string]*Component `json:"components"`
    LastUpdate         time.Time             `json:"last_update"`
    OverallCoverage    float64               `json:"overall_coverage"`
    SystemHealth       string                `json:"system_health"`
    ProductionReadiness float64              `json:"production_readiness"`
    CriticalAlerts     []string              `json:"critical_alerts"`
}

func main() {
    registryPath := "system_registry.json"
    
    // Load existing registry
    var registry Registry
    if data, err := os.ReadFile(registryPath); err == nil {
        json.Unmarshal(data, &registry)
    }
    
    if registry.Components == nil {
        registry.Components = make(map[string]*Component)
    }
    
    // Determine component priority and revenue impact
    priority := "MEDIUM"
    revenueImpact := "LOW"
    
    switch "storage" {
    case "license_management", "license_server":
        priority = "CRITICAL"
        revenueImpact = "CRITICAL"
    case "core_engine", "storage", "rest_api":
        priority = "HIGH"
        revenueImpact = "MEDIUM"
    }
    
    // Update component
    registry.Components["storage"] = &Component{
        Name:            "Storage Layer",
        Package:         "./pkg/storage/...",
        Coverage:        0.0,
        TestsPassing:    0,
        TestsTotal:      0,
        ProductionReady: false,
        Priority:        priority,
        RevenueImpact:   revenueImpact,
        LastUpdated:     time.Now(),
    }
    
    // Calculate overall metrics
    totalCoverage := 0.0
    productionReadyCount := 0
    totalComponents := len(registry.Components)
    
    for _, comp := range registry.Components {
        totalCoverage += comp.Coverage
        if comp.ProductionReady {
            productionReadyCount++
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
    
    // Update critical alerts
    registry.CriticalAlerts = []string{}
    for _, comp := range registry.Components {
        if comp.RevenueImpact == "CRITICAL" && !comp.ProductionReady {
            registry.CriticalAlerts = append(registry.CriticalAlerts,
                fmt.Sprintf("CRITICAL: %s not production ready (%.1f%% coverage)",
                    comp.Name, comp.Coverage*100))
        }
    }
    
    // Save registry
    data, _ := json.MarshalIndent(registry, "", "  ")
    os.WriteFile(registryPath, data, 0644)
    
    fmt.Printf("Registry updated: %s (%.1f%% coverage, %d/%d tests)\n",
        "Storage Layer", 0.0, 0, 0)
}
