package registry

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// Test GetComponentStatus and IsProductionReady by creating real registry files
func TestRegistryFunctions_DirectCalls(t *testing.T) {
	// Save current directory and change to temp directory for testing
	originalDir, err := os.Getwd()
	if err != nil {
		t.Fatalf("Failed to get current directory: %v", err)
	}
	defer os.Chdir(originalDir)

	// Create temp directory and change to it
	tempDir := t.TempDir()
	err = os.Chdir(tempDir)
	if err != nil {
		t.Fatalf("Failed to change to temp directory: %v", err)
	}

	t.Run("GetComponentStatus_Success", func(t *testing.T) {
		// Create a registry with test component
		registry := NewSystemRegistry()
		registry.Components["TestComponent"] = &SystemComponent{
			Name:            "Test Component",
			Coverage:        0.85,
			TestsPassing:    8,
			TestsTotal:      10,
			ProductionReady: true,
			Priority:        "HIGH",
			Package:         "test/package",
			LastUpdated:     time.Now(),
		}

		// Save to default path that GetRegistryPath returns
		err := registry.SaveToFile(GetRegistryPath())
		if err != nil {
			t.Fatalf("Failed to save registry: %v", err)
		}

		// Now test GetComponentStatus
		comp, err := GetComponentStatus("TestComponent")
		if err != nil {
			t.Errorf("Expected no error, got: %v", err)
		}
		if comp == nil {
			t.Error("Expected component, got nil")
		}
		if comp.Name != "Test Component" {
			t.Errorf("Expected name 'Test Component', got: %s", comp.Name)
		}
	})

	t.Run("GetComponentStatus_ComponentNotFound", func(t *testing.T) {
		// Component should not exist
		comp, err := GetComponentStatus("NonExistentComponent")
		if err == nil {
			t.Error("Expected error for non-existent component")
		}
		if comp != nil {
			t.Error("Expected nil component")
		}
		if !strings.Contains(err.Error(), "not found") {
			t.Errorf("Expected 'not found' error, got: %v", err)
		}
	})

	t.Run("GetComponentStatus_NoRegistryFile", func(t *testing.T) {
		// Remove registry file
		os.Remove(GetRegistryPath())
		
		comp, err := GetComponentStatus("TestComponent")
		if err == nil {
			t.Error("Expected error when registry file doesn't exist")
		}
		if comp != nil {
			t.Error("Expected nil component when registry load fails")
		}
	})

	t.Run("IsProductionReady_AllReady", func(t *testing.T) {
		// Create registry with all critical components ready
		registry := NewSystemRegistry()
		registry.Components["CriticalComp1"] = &SystemComponent{
			Name:            "Critical Component 1",
			Coverage:        0.95,
			ProductionReady: true,
			Priority:        "CRITICAL",
		}
		registry.Components["CriticalComp2"] = &SystemComponent{
			Name:            "Critical Component 2",
			Coverage:        0.90,
			ProductionReady: true,
			Priority:        "CRITICAL",
		}
		registry.Components["NonCritical"] = &SystemComponent{
			Name:            "Non Critical",
			Coverage:        0.50,
			ProductionReady: false,
			Priority:        "LOW", // Not critical, so doesn't affect production readiness
		}

		err := registry.SaveToFile(GetRegistryPath())
		if err != nil {
			t.Fatalf("Failed to save registry: %v", err)
		}

		ready, blockers := IsProductionReady()
		if !ready {
			t.Error("Expected production ready when all critical components are ready")
		}
		if len(blockers) != 0 {
			t.Errorf("Expected no blockers, got: %v", blockers)
		}
	})

	t.Run("IsProductionReady_CriticalNotReady", func(t *testing.T) {
		// Create registry with critical component not ready
		registry := NewSystemRegistry()
		registry.Components["CriticalNotReady"] = &SystemComponent{
			Name:            "Critical Not Ready",
			Coverage:        0.70,
			ProductionReady: false,
			Priority:        "CRITICAL",
		}

		err := registry.SaveToFile(GetRegistryPath())
		if err != nil {
			t.Fatalf("Failed to save registry: %v", err)
		}

		ready, blockers := IsProductionReady()
		if ready {
			t.Error("Expected not production ready when critical component not ready")
		}
		if len(blockers) == 0 {
			t.Error("Expected blockers when critical component not ready")
		}
		if !strings.Contains(blockers[0], "Critical Not Ready") {
			t.Errorf("Expected blocker to contain component name, got: %s", blockers[0])
		}
		if !strings.Contains(blockers[0], "70.0%") {
			t.Errorf("Expected blocker to contain coverage, got: %s", blockers[0])
		}
	})

	t.Run("IsProductionReady_NoRegistryFile", func(t *testing.T) {
		// Remove registry file
		os.Remove(GetRegistryPath())

		ready, blockers := IsProductionReady()
		if ready {
			t.Error("Expected not ready when registry load fails")
		}
		if len(blockers) != 1 {
			t.Errorf("Expected 1 blocker for load failure, got %d", len(blockers))
		}
		if !strings.Contains(blockers[0], "Failed to load registry") {
			t.Errorf("Expected blocker about registry load failure, got: %s", blockers[0])
		}
	})
}

// Test updateMarkdownRegistry function 
func TestUpdateMarkdownRegistry_Coverage(t *testing.T) {
	// Save current directory and change to temp directory
	originalDir, err := os.Getwd()
	if err != nil {
		t.Fatalf("Failed to get current directory: %v", err)
	}
	defer os.Chdir(originalDir)

	tempDir := t.TempDir()
	err = os.Chdir(tempDir)
	if err != nil {
		t.Fatalf("Failed to change to temp directory: %v", err)
	}

	t.Run("updateMarkdownRegistry_Success", func(t *testing.T) {
		// Create initial markdown content
		initialContent := `# System Registry

**Last Updated**: 2024-01-01 00:00:00
**System Health**: GOOD  
**Production Readiness**: 85.0%

## Component Status

| Component | Coverage | Tests | Ready | Priority |
|-----------|----------|--------|--------|----------|
| Test Component | 🟢 90% | 9/10 PASS | ✅ YES | 🟠 HIGH |
`

		err := os.WriteFile("SYSTEM_REGISTRY.md", []byte(initialContent), 0644)
		if err != nil {
			t.Fatalf("Failed to write initial markdown: %v", err)
		}

		// Create test registry
		registry := NewSystemRegistry()
		registry.SystemHealth = "EXCELLENT"
		registry.ProductionReadiness = 92.5
		registry.Components["UpdatedComponent"] = &SystemComponent{
			Name:            "Updated Component",
			Coverage:        0.88,
			TestsPassing:    8,
			TestsTotal:      9,
			ProductionReady: true,
			Priority:        "CRITICAL",
		}

		// This should exercise the updateMarkdownRegistry function
		err = updateMarkdownRegistry(registry)
		if err != nil {
			t.Errorf("Expected no error, got: %v", err)
		}

		// Verify updates were made
		updatedContent, err := os.ReadFile("SYSTEM_REGISTRY.md")
		if err != nil {
			t.Fatalf("Failed to read updated markdown: %v", err)
		}

		content := string(updatedContent)
		if !strings.Contains(content, "EXCELLENT") {
			t.Error("Expected updated system health")
		}
		if !strings.Contains(content, "92.5%") {
			t.Error("Expected updated production readiness")
		}
	})

	t.Run("updateMarkdownRegistry_FileNotFound", func(t *testing.T) {
		// Ensure no markdown file exists
		os.Remove("SYSTEM_REGISTRY.md")

		registry := NewSystemRegistry()
		err := updateMarkdownRegistry(registry)
		if err == nil {
			t.Error("Expected error when markdown file doesn't exist")
		}
	})
}

// Test BenchmarkHook function with better approach
func TestBenchmarkHook_Coverage(t *testing.T) {
	originalDir, err := os.Getwd()
	if err != nil {
		t.Fatalf("Failed to get current directory: %v", err)
	}
	defer os.Chdir(originalDir)

	tempDir := t.TempDir()
	err = os.Chdir(tempDir)
	if err != nil {
		t.Fatalf("Failed to change to temp directory: %v", err)
	}

	t.Run("BenchmarkHook_ComponentNotFound", func(t *testing.T) {
		// Create registry without the target component
		registry := NewSystemRegistry()
		err := registry.SaveToFile(GetRegistryPath())
		if err != nil {
			t.Fatalf("Failed to save registry: %v", err)
		}

		// BenchmarkHook is a void function and doesn't return an error
		// This will exercise the function but not hit the component update path
		BenchmarkHook(&testing.B{}, "nonexistent/package", "BenchmarkTest", 100)
	})

	t.Run("BenchmarkHook_NoRegistryFile", func(t *testing.T) {
		// Ensure no registry file exists
		os.Remove(GetRegistryPath())

		// This will exercise the function with no registry file
		BenchmarkHook(&testing.B{}, "test/package", "BenchmarkTest", 100)
	})
}

// Test additional edge cases to boost coverage
func TestRegistryEdgeCases_Coverage(t *testing.T) {
	t.Run("SaveToFile_InvalidPath", func(t *testing.T) {
		registry := NewSystemRegistry()
		
		// Try to save to invalid path (should fail)
		err := registry.SaveToFile("/nonexistent/directory/registry.json")
		if err == nil {
			t.Error("Expected error saving to invalid path")
		}
	})
	
	t.Run("LoadFromFile_InvalidJSON", func(t *testing.T) {
		tempDir := t.TempDir()
		invalidPath := filepath.Join(tempDir, "invalid.json")
		
		// Write invalid JSON
		err := os.WriteFile(invalidPath, []byte("invalid json content"), 0644)
		if err != nil {
			t.Fatalf("Failed to write invalid JSON: %v", err)
		}
		
		_, err = LoadFromFile(invalidPath)
		if err == nil {
			t.Error("Expected error loading invalid JSON")
		}
	})
	
	t.Run("UpdateFromTestRun_NewComponent", func(t *testing.T) {
		registry := NewSystemRegistry()
		
		// Create TestResult to update with
		testResults := []TestResult{
			{
				Name:        "TestNewPackage",
				Package:     "new/package",
				Passed:      true,
				Coverage:    0.85,
				Duration:    time.Millisecond * 1000,
			},
		}
		
		registry.UpdateFromTestRun(testResults)
		
		comp := registry.Components["new/package"]
		if comp == nil {
			t.Error("Expected new component to be created")
		}
	})
	
	t.Run("CalculateOverallMetrics_NoComponents", func(t *testing.T) {
		registry := NewSystemRegistry()
		
		// Test with no components
		registry.calculateOverallMetrics()
		
		if registry.SystemHealth != "UNKNOWN" {
			t.Errorf("Expected UNKNOWN health with no components, got: %s", registry.SystemHealth)
		}
	})
	
	t.Run("CalculateOverallMetrics_MixedComponents", func(t *testing.T) {
		registry := NewSystemRegistry()
		
		// Add components with different qualities
		registry.Components["good"] = &SystemComponent{
			Coverage: 0.95,
			Priority: "HIGH",
			ProductionReady: true,
		}
		registry.Components["bad_critical"] = &SystemComponent{
			Coverage: 0.30,
			Priority: "CRITICAL",
			ProductionReady: false,
		}
		
		registry.calculateOverallMetrics()
		
		// Should have degraded health due to bad critical component
		if registry.SystemHealth == "EXCELLENT" {
			t.Error("Expected degraded health with bad critical component")
		}
	})
}