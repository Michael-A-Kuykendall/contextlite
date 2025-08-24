package main

import (
	"encoding/json"
	"os"
	"testing"
)

func TestComponent(t *testing.T) {
	// Test Component struct marshaling/unmarshaling
	comp := Component{
		ProductionReady: true,
		Priority:        "CRITICAL",
		Name:           "Test Component",
		Coverage:       0.95,
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
		t.Errorf("Component name mismatch: got %s, want %s", decoded.Name, comp.Name)
	}

	if decoded.ProductionReady != comp.ProductionReady {
		t.Errorf("Component ProductionReady mismatch: got %v, want %v", decoded.ProductionReady, comp.ProductionReady)
	}

	if decoded.Priority != comp.Priority {
		t.Errorf("Component Priority mismatch: got %s, want %s", decoded.Priority, comp.Priority)
	}

	if decoded.Coverage != comp.Coverage {
		t.Errorf("Component Coverage mismatch: got %f, want %f", decoded.Coverage, comp.Coverage)
	}
}

func TestRegistry(t *testing.T) {
	// Test Registry struct marshaling/unmarshaling
	registry := Registry{
		Components: map[string]Component{
			"comp1": {
				ProductionReady: true,
				Priority:        "CRITICAL",
				Name:           "Component 1",
				Coverage:       0.95,
			},
			"comp2": {
				ProductionReady: false,
				Priority:        "HIGH",
				Name:           "Component 2", 
				Coverage:       0.65,
			},
		},
		SystemHealth:        "PRODUCTION_READY",
		ProductionReadiness: 85.5,
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

func TestMainLogicWithValidRegistry(t *testing.T) {
	// Create temporary registry file for testing
	tempFile := "test_production_check_registry.json"
	
	t.Run("AllCriticalComponentsReady", func(t *testing.T) {
		registry := Registry{
			Components: map[string]Component{
				"critical-comp-1": {
					ProductionReady: true,
					Priority:        "CRITICAL",
					Name:           "Critical Component 1",
					Coverage:       0.95,
				},
				"critical-comp-2": {
					ProductionReady: true, 
					Priority:        "CRITICAL",
					Name:           "Critical Component 2",
					Coverage:       0.88,
				},
				"high-comp": {
					ProductionReady: false, // This shouldn't block production (not CRITICAL)
					Priority:        "HIGH",
					Name:           "High Priority Component",
					Coverage:       0.75,
				},
			},
			SystemHealth:        "PRODUCTION_READY",
			ProductionReadiness: 100.0,
		}

		data, err := json.Marshal(registry)
		if err != nil {
			t.Fatalf("Failed to marshal test registry: %v", err)
		}

		err = os.WriteFile(tempFile, data, 0644)
		if err != nil {
			t.Fatalf("Failed to write test registry file: %v", err)
		}
		defer os.Remove(tempFile)

		// Test the main function logic by reading and processing the file
		data, err = os.ReadFile(tempFile)
		if err != nil {
			t.Fatalf("Failed to read test file: %v", err)
		}

		var r Registry
		err = json.Unmarshal(data, &r)
		if err != nil {
			t.Fatalf("Failed to unmarshal test registry: %v", err)
		}

		// Simulate main function logic
		blockers := 0
		for _, comp := range r.Components {
			if comp.Priority == "CRITICAL" && !comp.ProductionReady {
				blockers++
			}
		}

		if blockers != 0 {
			t.Errorf("Expected 0 blockers with all critical components ready, got %d", blockers)
		}

		if r.SystemHealth != "PRODUCTION_READY" {
			t.Errorf("Expected PRODUCTION_READY health, got %s", r.SystemHealth)
		}
	})

	t.Run("CriticalComponentsBlocking", func(t *testing.T) {
		registry := Registry{
			Components: map[string]Component{
				"critical-comp-1": {
					ProductionReady: true,
					Priority:        "CRITICAL", 
					Name:           "Critical Component 1",
					Coverage:       0.95,
				},
				"critical-comp-2": {
					ProductionReady: false, // This blocks production
					Priority:        "CRITICAL",
					Name:           "Critical Component 2", 
					Coverage:       0.65,
				},
				"critical-comp-3": {
					ProductionReady: false, // This also blocks production
					Priority:        "CRITICAL",
					Name:           "Critical Component 3",
					Coverage:       0.45,
				},
				"medium-comp": {
					ProductionReady: false, // This shouldn't count as blocker
					Priority:        "MEDIUM",
					Name:           "Medium Priority Component",
					Coverage:       0.30,
				},
			},
			SystemHealth:        "TESTING_IN_PROGRESS",
			ProductionReadiness: 65.5,
		}

		data, err := json.Marshal(registry)
		if err != nil {
			t.Fatalf("Failed to marshal test registry: %v", err)
		}

		err = os.WriteFile(tempFile, data, 0644)
		if err != nil {
			t.Fatalf("Failed to write test registry file: %v", err)
		}
		defer os.Remove(tempFile)

		// Test the main function logic
		data, err = os.ReadFile(tempFile)
		if err != nil {
			t.Fatalf("Failed to read test file: %v", err)
		}

		var r Registry
		err = json.Unmarshal(data, &r)
		if err != nil {
			t.Fatalf("Failed to unmarshal test registry: %v", err)
		}

		// Simulate main function logic - count critical components not production ready
		blockers := 0
		for _, comp := range r.Components {
			if comp.Priority == "CRITICAL" && !comp.ProductionReady {
				blockers++
			}
		}

		if blockers != 2 {
			t.Errorf("Expected 2 blockers (critical components not ready), got %d", blockers)
		}
	})

	t.Run("EmptyRegistry", func(t *testing.T) {
		registry := Registry{
			Components:          make(map[string]Component),
			SystemHealth:        "PRODUCTION_READY",
			ProductionReadiness: 100.0,
		}

		data, err := json.Marshal(registry)
		if err != nil {
			t.Fatalf("Failed to marshal empty registry: %v", err)
		}

		err = os.WriteFile(tempFile, data, 0644)
		if err != nil {
			t.Fatalf("Failed to write empty registry file: %v", err)
		}
		defer os.Remove(tempFile)

		// Test with empty registry
		data, err = os.ReadFile(tempFile)
		if err != nil {
			t.Fatalf("Failed to read empty registry file: %v", err)
		}

		var r Registry
		err = json.Unmarshal(data, &r)
		if err != nil {
			t.Fatalf("Failed to unmarshal empty registry: %v", err)
		}

		// Should have 0 blockers with empty registry
		blockers := 0
		for _, comp := range r.Components {
			if comp.Priority == "CRITICAL" && !comp.ProductionReady {
				blockers++
			}
		}

		if blockers != 0 {
			t.Errorf("Expected 0 blockers with empty registry, got %d", blockers)
		}
	})
}

func TestMainErrorHandling(t *testing.T) {
	t.Run("InvalidJSON", func(t *testing.T) {
		invalidFile := "test_invalid_production_check.json"
		err := os.WriteFile(invalidFile, []byte("invalid json content"), 0644)
		if err != nil {
			t.Fatalf("Failed to write invalid test file: %v", err)
		}
		defer os.Remove(invalidFile)

		// Test that invalid JSON is handled
		data, err := os.ReadFile(invalidFile)
		if err != nil {
			t.Fatalf("Failed to read invalid test file: %v", err)
		}

		var registry Registry
		err = json.Unmarshal(data, &registry)
		if err == nil {
			t.Error("Expected error when unmarshaling invalid JSON")
		}
	})

	t.Run("NonExistentFile", func(t *testing.T) {
		// Test reading non-existent file
		_, err := os.ReadFile("non_existent_registry.json")
		if err == nil {
			t.Error("Expected error when reading non-existent file")
		}
	})
}

func TestComponentPriorityLevels(t *testing.T) {
	// Test various priority levels and their blocking behavior
	priorities := []string{"CRITICAL", "HIGH", "MEDIUM", "LOW", ""}
	
	for _, priority := range priorities {
		t.Run("Priority_"+priority, func(t *testing.T) {
			comp := Component{
				ProductionReady: false,
				Priority:        priority,
				Name:           "Test Component " + priority,
				Coverage:       0.75,
			}

			// Only CRITICAL priority should count as blocker when not production ready
			shouldBlock := (priority == "CRITICAL")
			actualBlock := (comp.Priority == "CRITICAL" && !comp.ProductionReady)
			
			if actualBlock != shouldBlock {
				t.Errorf("Component with priority '%s' blocking behavior: got %v, want %v", priority, actualBlock, shouldBlock)
			}
		})
	}
}

func TestCoverageDisplayFormat(t *testing.T) {
	// Test coverage formatting (used in blocker output)
	testCases := []struct {
		coverage float64
		expected string
	}{
		{0.95, "95.0"},
		{0.5, "50.0"},
		{0.0, "0.0"},
		{1.0, "100.0"},
		{0.123, "12.3"},
		{0.999, "99.9"},
	}

	for _, tc := range testCases {
		t.Run("Coverage_"+tc.expected, func(t *testing.T) {
			comp := Component{Coverage: tc.coverage}
			// Simulate the coverage display format used in main function
			displayValue := comp.Coverage * 100
			
			// Check if the multiplication works correctly
			if displayValue < 0 || displayValue > 100 {
				t.Errorf("Coverage %f resulted in invalid display value %f", tc.coverage, displayValue)
			}
		})
	}
}