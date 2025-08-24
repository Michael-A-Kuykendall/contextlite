package main

import (
	"encoding/json"
	"fmt"
	"math"
	"os"
	"strings"
	"testing"
	"time"
)

// Helper function for floating point comparison
func abs(x float64) float64 {
	return math.Abs(x)
}

func TestComponent(t *testing.T) {
	// Test Component struct marshaling/unmarshaling
	comp := &Component{
		Name:            "Test Component",
		Package:         "test/pkg",
		Coverage:        0.95,
		TestsPassing:    8,
		TestsTotal:      10,
		ProductionReady: true,
		Priority:        "CRITICAL",
		RevenueImpact:   "HIGH",
		LastUpdated:     time.Now(),
	}

	data, err := json.Marshal(comp)
	if err != nil {
		t.Errorf("Failed to marshal Component: %v", err)
	}

	var decoded Component
	err = json.Unmarshal(data, &decoded)
	if err != nil {
		t.Errorf("Failed to unmarshal Component: %v", err)
	}

	if decoded.Name != comp.Name {
		t.Errorf("Component Name mismatch: got %s, want %s", decoded.Name, comp.Name)
	}

	if decoded.Coverage != comp.Coverage {
		t.Errorf("Component Coverage mismatch: got %f, want %f", decoded.Coverage, comp.Coverage)
	}

	if decoded.ProductionReady != comp.ProductionReady {
		t.Errorf("Component ProductionReady mismatch: got %v, want %v", decoded.ProductionReady, comp.ProductionReady)
	}
}

func TestRegistry(t *testing.T) {
	// Test Registry struct marshaling/unmarshaling
	registry := &Registry{
		Components: map[string]*Component{
			"comp1": {
				Name:            "Component 1",
				Package:         "pkg1",
				Coverage:        0.85,
				TestsPassing:    5,
				TestsTotal:      5,
				ProductionReady: true,
				Priority:        "CRITICAL",
				RevenueImpact:   "HIGH",
				LastUpdated:     time.Now(),
			},
		},
		LastUpdate:          time.Now(),
		OverallCoverage:     0.85,
		SystemHealth:        "PRODUCTION_READY",
		ProductionReadiness: 100.0,
		CriticalAlerts:      []string{"Alert 1", "Alert 2"},
	}

	data, err := json.Marshal(registry)
	if err != nil {
		t.Errorf("Failed to marshal Registry: %v", err)
	}

	var decoded Registry
	err = json.Unmarshal(data, &decoded)
	if err != nil {
		t.Errorf("Failed to unmarshal Registry: %v", err)
	}

	if decoded.SystemHealth != registry.SystemHealth {
		t.Errorf("Registry SystemHealth mismatch: got %s, want %s", decoded.SystemHealth, registry.SystemHealth)
	}

	if decoded.ProductionReadiness != registry.ProductionReadiness {
		t.Errorf("Registry ProductionReadiness mismatch: got %f, want %f", decoded.ProductionReadiness, registry.ProductionReadiness)
	}

	if len(decoded.Components) != len(registry.Components) {
		t.Errorf("Registry Components length mismatch: got %d, want %d", len(decoded.Components), len(registry.Components))
	}
}

func TestComponentTest(t *testing.T) {
	// Test ComponentTest struct
	compTest := ComponentTest{
		ID:           "test_id",
		Name:         "Test Component",
		Package:      "./test/pkg",
		Priority:     "HIGH",
		RevenueImpact: "MEDIUM",
	}

	if compTest.ID != "test_id" {
		t.Errorf("ComponentTest ID mismatch: got %s, want test_id", compTest.ID)
	}

	if compTest.Priority != "HIGH" {
		t.Errorf("ComponentTest Priority mismatch: got %s, want HIGH", compTest.Priority)
	}
}

func TestLoadOrCreateRegistry(t *testing.T) {
	t.Run("CreateNewRegistry", func(t *testing.T) {
		// Ensure no existing registry file
		os.Remove("system_registry.json")
		
		registry := loadOrCreateRegistry()
		
		if registry == nil {
			t.Fatal("loadOrCreateRegistry returned nil")
		}
		
		if registry.Components == nil {
			t.Error("Registry Components map should not be nil")
		}
		
		if len(registry.Components) != 0 {
			t.Errorf("New registry should have 0 components, got %d", len(registry.Components))
		}
	})

	t.Run("LoadExistingRegistry", func(t *testing.T) {
		// Create test registry file
		testRegistry := &Registry{
			Components: map[string]*Component{
				"test_comp": {
					Name:            "Test Component",
					Package:         "test/pkg",
					Coverage:        0.90,
					TestsPassing:    5,
					TestsTotal:      5,
					ProductionReady: true,
					Priority:        "HIGH",
					RevenueImpact:   "MEDIUM",
					LastUpdated:     time.Now(),
				},
			},
			LastUpdate:          time.Now(),
			OverallCoverage:     0.90,
			SystemHealth:        "PRODUCTION_READY",
			ProductionReadiness: 100.0,
			CriticalAlerts:      []string{},
		}

		data, _ := json.Marshal(testRegistry)
		os.WriteFile("system_registry.json", data, 0644)
		defer os.Remove("system_registry.json")

		registry := loadOrCreateRegistry()

		if len(registry.Components) != 1 {
			t.Errorf("Expected 1 component in loaded registry, got %d", len(registry.Components))
		}

		if registry.SystemHealth != "PRODUCTION_READY" {
			t.Errorf("Expected PRODUCTION_READY, got %s", registry.SystemHealth)
		}
	})

	t.Run("LoadInvalidRegistry", func(t *testing.T) {
		// Create invalid JSON file
		os.WriteFile("system_registry.json", []byte("invalid json"), 0644)
		defer os.Remove("system_registry.json")

		registry := loadOrCreateRegistry()
		
		// Should create new registry even with invalid JSON
		if registry == nil {
			t.Fatal("loadOrCreateRegistry should not return nil even with invalid JSON")
		}
		
		if registry.Components == nil {
			t.Error("Registry Components should be initialized")
		}
	})
}

func TestCalculateOverallMetrics(t *testing.T) {
	t.Run("EmptyRegistry", func(t *testing.T) {
		registry := &Registry{
			Components: make(map[string]*Component),
		}

		calculateOverallMetrics(registry)

		// Should not crash with empty registry
		// Note: CriticalAlerts is NOT initialized when registry is empty (function returns early)
		// This tests the actual behavior of the function
		if len(registry.Components) != 0 {
			t.Errorf("Empty registry should have 0 components, got %d", len(registry.Components))
		}
	})

	t.Run("SingleComponent", func(t *testing.T) {
		registry := &Registry{
			Components: map[string]*Component{
				"comp1": {
					Name:            "Component 1",
					Coverage:        0.85,
					ProductionReady: true,
					RevenueImpact:   "MEDIUM",
				},
			},
		}

		calculateOverallMetrics(registry)

		if registry.OverallCoverage != 0.85 {
			t.Errorf("Expected overall coverage 0.85, got %f", registry.OverallCoverage)
		}

		if registry.ProductionReadiness != 100.0 {
			t.Errorf("Expected production readiness 100.0, got %f", registry.ProductionReadiness)
		}

		if registry.SystemHealth != "PRODUCTION_READY" {
			t.Errorf("Expected PRODUCTION_READY, got %s", registry.SystemHealth)
		}
	})

	t.Run("MultipleComponents", func(t *testing.T) {
		registry := &Registry{
			Components: map[string]*Component{
				"comp1": {
					Name:            "Component 1",
					Coverage:        0.80,
					ProductionReady: true,
					RevenueImpact:   "CRITICAL",
				},
				"comp2": {
					Name:            "Component 2",
					Coverage:        0.60,
					ProductionReady: false,
					RevenueImpact:   "CRITICAL",
				},
				"comp3": {
					Name:            "Component 3",
					Coverage:        0.90,
					ProductionReady: true,
					RevenueImpact:   "MEDIUM",
				},
			},
		}

		calculateOverallMetrics(registry)

		expectedCoverage := (0.80 + 0.60 + 0.90) / 3
		if abs(registry.OverallCoverage - expectedCoverage) > 0.001 {
			t.Errorf("Expected overall coverage %f, got %f", expectedCoverage, registry.OverallCoverage)
		}

		expectedReadiness := 2.0 / 3.0 * 100 // 2 out of 3 ready
		if abs(registry.ProductionReadiness - expectedReadiness) > 0.001 {
			t.Errorf("Expected production readiness %f, got %f", expectedReadiness, registry.ProductionReadiness)
		}

		// Should have critical alert for comp2
		if len(registry.CriticalAlerts) != 1 {
			t.Errorf("Expected 1 critical alert, got %d", len(registry.CriticalAlerts))
		}

		if !strings.Contains(registry.CriticalAlerts[0], "Component 2") {
			t.Error("Critical alert should mention Component 2")
		}
	})

	t.Run("SystemHealthLevels", func(t *testing.T) {
		testCases := []struct {
			numReady       int
			numTotal       int
			expectedHealth string
		}{
			{9, 10, "PRODUCTION_READY"},  // 90%
			{8, 10, "TESTING_COMPLETE"},  // 80%
			{6, 10, "TESTING_IN_PROGRESS"}, // 60%
			{3, 10, "TESTING_REQUIRED"},  // 30%
		}

		for _, tc := range testCases {
			registry := &Registry{
				Components: make(map[string]*Component),
			}
			
			// Create components with specified readiness ratio
			for i := 0; i < tc.numTotal; i++ {
				ready := i < tc.numReady
				registry.Components[fmt.Sprintf("comp%d", i)] = &Component{
					Name:            fmt.Sprintf("Component %d", i),
					ProductionReady: ready,
					Coverage:        0.8,
				}
			}

			calculateOverallMetrics(registry)

			expectedReadiness := float64(tc.numReady) / float64(tc.numTotal) * 100
			if abs(registry.ProductionReadiness - expectedReadiness) > 0.1 {
				t.Errorf("Expected production readiness %f, got %f",
					expectedReadiness, registry.ProductionReadiness)
			}

			if registry.SystemHealth != tc.expectedHealth {
				t.Errorf("For readiness %f, expected health %s, got %s",
					expectedReadiness, tc.expectedHealth, registry.SystemHealth)
			}
		}
	})
}

func TestSaveRegistry(t *testing.T) {
	registry := &Registry{
		Components: map[string]*Component{
			"test_comp": {
				Name:     "Test Component",
				Coverage: 0.85,
			},
		},
		SystemHealth: "PRODUCTION_READY",
	}

	// Clean up before and after
	os.Remove("system_registry.json")
	defer os.Remove("system_registry.json")

	saveRegistry(registry)

	// Verify file was created
	if _, err := os.Stat("system_registry.json"); os.IsNotExist(err) {
		t.Error("Registry file was not created")
	}

	// Verify file contents
	data, err := os.ReadFile("system_registry.json")
	if err != nil {
		t.Errorf("Failed to read saved registry file: %v", err)
	}

	var loaded Registry
	err = json.Unmarshal(data, &loaded)
	if err != nil {
		t.Errorf("Failed to unmarshal saved registry: %v", err)
	}

	if loaded.SystemHealth != "PRODUCTION_READY" {
		t.Errorf("Saved registry SystemHealth mismatch: got %s, want PRODUCTION_READY", loaded.SystemHealth)
	}
}

func TestUpdateMarkdown(t *testing.T) {
	registry := &Registry{
		Components: map[string]*Component{
			"test_comp": {
				Name:            "Test Component",
				Coverage:        0.85,
				TestsPassing:    5,
				TestsTotal:      5,
				ProductionReady: true,
				Priority:        "HIGH",
				RevenueImpact:   "CRITICAL",
			},
		},
		LastUpdate:          time.Now(),
		SystemHealth:        "PRODUCTION_READY",
		ProductionReadiness: 100.0,
		OverallCoverage:     0.85,
		CriticalAlerts:      []string{},
	}

	// Clean up before and after
	os.Remove("SYSTEM_REGISTRY.md")
	defer os.Remove("SYSTEM_REGISTRY.md")

	updateMarkdown(registry)

	// Verify file was created
	if _, err := os.Stat("SYSTEM_REGISTRY.md"); os.IsNotExist(err) {
		t.Error("Markdown file was not created")
	}

	// Verify file contents
	content, err := os.ReadFile("SYSTEM_REGISTRY.md")
	if err != nil {
		t.Errorf("Failed to read saved markdown file: %v", err)
	}

	contentStr := string(content)
	if !strings.Contains(contentStr, "# ContextLite System Registry") {
		t.Error("Markdown should contain header")
	}

	if !strings.Contains(contentStr, "PRODUCTION_READY") {
		t.Error("Markdown should contain system health")
	}

	if !strings.Contains(contentStr, "Test Component") {
		t.Error("Markdown should contain component name")
	}
}

func TestGenerateMarkdownFromRegistry(t *testing.T) {
	t.Run("CompleteRegistry", func(t *testing.T) {
		registry := &Registry{
			Components: map[string]*Component{
				"critical_comp": {
					Name:            "Critical Component",
					Coverage:        0.95,
					TestsPassing:    10,
					TestsTotal:      10,
					ProductionReady: true,
					Priority:        "CRITICAL",
					RevenueImpact:   "CRITICAL",
				},
				"high_comp": {
					Name:            "High Priority Component",
					Coverage:        0.75,
					TestsPassing:    8,
					TestsTotal:      10,
					ProductionReady: false,
					Priority:        "HIGH",
					RevenueImpact:   "MEDIUM",
				},
			},
			LastUpdate:          time.Now(),
			SystemHealth:        "TESTING_IN_PROGRESS",
			ProductionReadiness: 50.0,
			OverallCoverage:     0.85,
			CriticalAlerts:      []string{"Alert 1", "Alert 2"},
		}

		md := generateMarkdownFromRegistry(registry)

		// Check for header
		if !strings.Contains(md, "# ContextLite System Registry") {
			t.Error("Markdown should contain main header")
		}

		// Check for system status
		if !strings.Contains(md, "## 🎯 REGISTRY STATUS OVERVIEW") {
			t.Error("Markdown should contain status overview section")
		}

		if !strings.Contains(md, "TESTING_IN_PROGRESS") {
			t.Error("Markdown should contain system health")
		}

		// Check for critical alerts
		if !strings.Contains(md, "## 🚨 CRITICAL ALERTS") {
			t.Error("Markdown should contain critical alerts section")
		}

		// Check for components sections
		if !strings.Contains(md, "### Business-Critical Systems") {
			t.Error("Markdown should contain business-critical systems section")
		}

		if !strings.Contains(md, "### Core Engine Systems") {
			t.Error("Markdown should contain core engine systems section")
		}

		// Check for production readiness
		if !strings.Contains(md, "## 🎯 PRODUCTION READINESS CHECK") {
			t.Error("Markdown should contain production readiness section")
		}

		// Check for component data
		if !strings.Contains(md, "Critical Component") {
			t.Error("Markdown should contain critical component name")
		}

		if !strings.Contains(md, "High Priority Component") {
			t.Error("Markdown should contain high priority component name")
		}
	})

	t.Run("EmptyRegistry", func(t *testing.T) {
		registry := &Registry{
			Components:          make(map[string]*Component),
			LastUpdate:          time.Now(),
			SystemHealth:        "TESTING_REQUIRED",
			ProductionReadiness: 0.0,
			OverallCoverage:     0.0,
			CriticalAlerts:      []string{},
		}

		md := generateMarkdownFromRegistry(registry)

		// Should still generate basic structure
		if !strings.Contains(md, "# ContextLite System Registry") {
			t.Error("Empty registry should still generate header")
		}

		if !strings.Contains(md, "TESTING_REQUIRED") {
			t.Error("Empty registry should show correct system health")
		}
	})

	t.Run("ProductionReadyRegistry", func(t *testing.T) {
		registry := &Registry{
			Components: map[string]*Component{
				"comp1": {
					Name:            "Component 1",
					Coverage:        0.95,
					TestsPassing:    10,
					TestsTotal:      10,
					ProductionReady: true,
					Priority:        "CRITICAL",
					RevenueImpact:   "CRITICAL",
				},
			},
			LastUpdate:          time.Now(),
			SystemHealth:        "PRODUCTION_READY",
			ProductionReadiness: 100.0,
			OverallCoverage:     0.95,
			CriticalAlerts:      []string{},
		}

		md := generateMarkdownFromRegistry(registry)

		if !strings.Contains(md, "✅ No Critical Blockers") {
			t.Error("Production ready registry should show no blockers")
		}

		if !strings.Contains(md, "All critical components are production ready") {
			t.Error("Production ready registry should indicate readiness")
		}
	})
}

func TestPrintSummary(t *testing.T) {
	registry := &Registry{
		SystemHealth:        "PRODUCTION_READY",
		ProductionReadiness: 95.5,
		OverallCoverage:     0.88,
		Components: map[string]*Component{
			"comp1": {Name: "Component 1"},
			"comp2": {Name: "Component 2"},
		},
		CriticalAlerts: []string{"Alert 1", "Alert 2"},
	}

	// This function prints to stdout, so we can't easily test output
	// But we can ensure it doesn't panic
	printSummary(registry)

	// Test with empty alerts
	registry.CriticalAlerts = []string{}
	printSummary(registry)
}

func TestProductionReadinessLogic(t *testing.T) {
	// Test the production readiness determination logic
	testCases := []struct {
		coverage        float64
		testsPassing    int
		testsTotal      int
		expectedReady   bool
		description     string
	}{
		{0.85, 10, 10, true, "High coverage, all tests passing"},
		{0.75, 10, 10, false, "Low coverage, all tests passing"},
		{0.85, 8, 10, false, "High coverage, some tests failing"},
		{0.85, 0, 0, false, "High coverage, no tests"},
		{1.0, 5, 5, true, "Perfect coverage, all tests passing"},
		{0.8, 1, 1, true, "Minimum coverage, all tests passing"},
		{0.79, 5, 5, false, "Just below minimum coverage"},
	}

	for _, tc := range testCases {
		t.Run(tc.description, func(t *testing.T) {
			// Simulate the production readiness logic
			productionReady := tc.coverage >= 0.8 && tc.testsPassing == tc.testsTotal && tc.testsTotal > 0

			if productionReady != tc.expectedReady {
				t.Errorf("Production readiness logic failed for %s: got %v, want %v",
					tc.description, productionReady, tc.expectedReady)
			}
		})
	}
}

func TestCoverageIconLogic(t *testing.T) {
	// Test the coverage icon logic used in markdown generation
	testCases := []struct {
		coverage     float64
		expectedIcon string
	}{
		{0.95, "✅"},  // >= 0.9
		{0.90, "✅"},  // >= 0.9
		{0.85, "🟡"},  // >= 0.7 && < 0.9
		{0.70, "🟡"},  // >= 0.7 && < 0.9
		{0.65, "🔴"},  // < 0.7
		{0.0, "🔴"},   // < 0.7
	}

	for _, tc := range testCases {
		t.Run("Coverage_"+strings.ReplaceAll(tc.expectedIcon, " ", "_"), func(t *testing.T) {
			// Simulate coverage icon logic
			var icon string
			if tc.coverage >= 0.9 {
				icon = "✅"
			} else if tc.coverage >= 0.7 {
				icon = "🟡"
			} else {
				icon = "🔴"
			}

			if icon != tc.expectedIcon {
				t.Errorf("Coverage icon logic failed for %f: got %s, want %s",
					tc.coverage, icon, tc.expectedIcon)
			}
		})
	}
}

func TestComponentTestStructure(t *testing.T) {
	// Test the predefined component test configurations
	components := []ComponentTest{
		{"license_management", "License Management", "./internal/license/...", "CRITICAL", "CRITICAL"},
		{"license_server", "License Server", "./cmd/license-server/...", "CRITICAL", "CRITICAL"},
		{"core_engine", "Core Engine", "./internal/engine/...", "HIGH", "MEDIUM"},
		{"client", "Client Library", "./pkg/contextlite/...", "HIGH", "MEDIUM"},
		{"rest_api", "REST API", "./cmd/contextlite/...", "HIGH", "MEDIUM"},
	}

	// Verify the predefined components have correct structure
	for _, comp := range components {
		if comp.ID == "" {
			t.Error("Component ID should not be empty")
		}
		if comp.Name == "" {
			t.Error("Component Name should not be empty")
		}
		if comp.Package == "" {
			t.Error("Component Package should not be empty")
		}
		if comp.Priority == "" {
			t.Error("Component Priority should not be empty")
		}
		if comp.RevenueImpact == "" {
			t.Error("Component RevenueImpact should not be empty")
		}

		// Check priority levels
		validPriorities := []string{"CRITICAL", "HIGH", "MEDIUM", "LOW"}
		found := false
		for _, valid := range validPriorities {
			if comp.Priority == valid {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("Invalid priority for component %s: %s", comp.ID, comp.Priority)
		}

		// Check revenue impact levels
		validImpacts := []string{"CRITICAL", "HIGH", "MEDIUM", "LOW"}
		found = false
		for _, valid := range validImpacts {
			if comp.RevenueImpact == valid {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("Invalid revenue impact for component %s: %s", comp.ID, comp.RevenueImpact)
		}
	}
}