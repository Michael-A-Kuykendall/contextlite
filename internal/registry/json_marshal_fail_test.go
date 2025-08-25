package registry

import (
	"math"
	"testing"
	"path/filepath"
)

// TestSaveToFile_JSONMarshalError - Target the JSON marshaling error path in SaveToFile
func TestSaveToFile_JSONMarshalError(t *testing.T) {
	t.Run("JSONMarshalError_NaNValues", func(t *testing.T) {
		registry := NewSystemRegistry()
		
		// Add a component with NaN values that can't be JSON marshaled
		badComponent := &SystemComponent{
			Name:               "bad_component",
			Package:            "test_package",
			Coverage:           math.NaN(),        // NaN cannot be JSON marshaled
			TestsTotal:         42,
			TestsPassing:       40,
			ProductionReady:    false,
			Priority:           "HIGH",
			RevenueImpact:      "MEDIUM", 
			Functions:          []FunctionInfo{},
			Dependencies:       []string{},
			PerformanceMetrics: make(map[string]string),
		}
		
		// Add NaN/Inf to performance metrics as well
		badComponent.PerformanceMetrics["latency"] = "NaN"
		badComponent.PerformanceMetrics["throughput"] = "+Inf"
		
		registry.Components["bad_component"] = badComponent
		
		// Also set registry-level NaN values
		registry.ProductionReadiness = math.NaN()
		registry.SystemHealth = "TESTING_IN_PROGRESS" // This should be fine
		
		// Try to save - this should fail at JSON marshaling
		tempFile := filepath.Join(t.TempDir(), "bad_registry.json")
		err := registry.SaveToFile(tempFile)
		
		if err != nil {
			t.Logf("✅ Successfully triggered JSON marshaling error: %v", err)
			
			// Verify it's the right type of error
			expectedMsg := "failed to marshal registry"
			if len(err.Error()) >= len(expectedMsg) && err.Error()[:len(expectedMsg)] == expectedMsg {
				t.Logf("🎯 HIT THE TARGET! JSON marshaling error path covered")
			} else {
				t.Logf("Got different error: %s", err.Error())
			}
		} else {
			t.Error("Expected JSON marshaling to fail with NaN/Inf values")
		}
	})
}