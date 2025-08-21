package registry

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func TestSystemComponent_Fields(t *testing.T) {
	now := time.Now()
	functions := []FunctionInfo{
		{Name: "testFunc", Purpose: "Testing", Tested: true, Performance: "fast", Security: "high", LastTested: now},
	}
	deps := []string{"dep1", "dep2"}
	metrics := map[string]string{"latency": "10ms", "throughput": "1000rps"}

	component := SystemComponent{
		Name:               "TestComponent",
		Package:            "test/package",
		Coverage:           85.5,
		TestsPassing:       10,
		TestsTotal:         12,
		ProductionReady:    true,
		Priority:           "HIGH",
		RevenueImpact:      "CRITICAL",
		LastUpdated:        now,
		Functions:          functions,
		Dependencies:       deps,
		PerformanceMetrics: metrics,
	}

	if component.Name != "TestComponent" {
		t.Errorf("Expected Name to be 'TestComponent', got %s", component.Name)
	}
	if component.Package != "test/package" {
		t.Errorf("Expected Package to be 'test/package', got %s", component.Package)
	}
	if component.Coverage != 85.5 {
		t.Errorf("Expected Coverage to be 85.5, got %f", component.Coverage)
	}
	if component.TestsPassing != 10 {
		t.Errorf("Expected TestsPassing to be 10, got %d", component.TestsPassing)
	}
	if component.TestsTotal != 12 {
		t.Errorf("Expected TestsTotal to be 12, got %d", component.TestsTotal)
	}
	if !component.ProductionReady {
		t.Error("Expected ProductionReady to be true")
	}
	if component.Priority != "HIGH" {
		t.Errorf("Expected Priority to be 'HIGH', got %s", component.Priority)
	}
	if component.RevenueImpact != "CRITICAL" {
		t.Errorf("Expected RevenueImpact to be 'CRITICAL', got %s", component.RevenueImpact)
	}
	if len(component.Functions) != 1 {
		t.Errorf("Expected 1 function, got %d", len(component.Functions))
	}
	if component.Functions[0].Name != "testFunc" {
		t.Errorf("Expected function name to be 'testFunc', got %s", component.Functions[0].Name)
	}
	if len(component.Dependencies) != 2 {
		t.Errorf("Expected 2 dependencies, got %d", len(component.Dependencies))
	}
	if component.Dependencies[0] != "dep1" {
		t.Errorf("Expected first dependency to be 'dep1', got %s", component.Dependencies[0])
	}
	if component.PerformanceMetrics["latency"] != "10ms" {
		t.Errorf("Expected latency metric to be '10ms', got %s", component.PerformanceMetrics["latency"])
	}
}

func TestFunctionInfo_Fields(t *testing.T) {
	now := time.Now()
	function := FunctionInfo{
		Name:        "processData",
		Purpose:     "Process incoming data stream",
		Tested:      true,
		Performance: "fast",
		Security:    "high",
		LastTested:  now,
	}

	if function.Name != "processData" {
		t.Errorf("Expected Name to be 'processData', got %s", function.Name)
	}
	if function.Purpose != "Process incoming data stream" {
		t.Errorf("Expected Purpose to be 'Process incoming data stream', got %s", function.Purpose)
	}
	if !function.Tested {
		t.Error("Expected Tested to be true")
	}
	if function.Performance != "fast" {
		t.Errorf("Expected Performance to be 'fast', got %s", function.Performance)
	}
	if function.Security != "high" {
		t.Errorf("Expected Security to be 'high', got %s", function.Security)
	}
	if function.LastTested != now {
		t.Errorf("Expected LastTested to be %v, got %v", now, function.LastTested)
	}
}

func TestTestResult_Fields(t *testing.T) {
	duration := time.Duration(500 * time.Millisecond)
	result := TestResult{
		Name:         "TestFunction",
		Package:      "main/test",
		Passed:       true,
		Duration:     duration,
		Coverage:     92.3,
		BenchmarkOps: 1000000,
		BenchmarkNsOp: 150,
		Error:        "",
	}

	if result.Name != "TestFunction" {
		t.Errorf("Expected Name to be 'TestFunction', got %s", result.Name)
	}
	if result.Package != "main/test" {
		t.Errorf("Expected Package to be 'main/test', got %s", result.Package)
	}
	if !result.Passed {
		t.Error("Expected Passed to be true")
	}
	if result.Duration != duration {
		t.Errorf("Expected Duration to be %v, got %v", duration, result.Duration)
	}
	if result.Coverage != 92.3 {
		t.Errorf("Expected Coverage to be 92.3, got %f", result.Coverage)
	}
	if result.BenchmarkOps != 1000000 {
		t.Errorf("Expected BenchmarkOps to be 1000000, got %d", result.BenchmarkOps)
	}
	if result.BenchmarkNsOp != 150 {
		t.Errorf("Expected BenchmarkNsOp to be 150, got %d", result.BenchmarkNsOp)
	}
	if result.Error != "" {
		t.Errorf("Expected Error to be empty, got %s", result.Error)
	}
}

func TestNewSystemRegistry(t *testing.T) {
	registry := NewSystemRegistry()

	if registry == nil {
		t.Fatal("Expected registry to be created")
	}
	if registry.Components == nil {
		t.Error("Expected Components map to be initialized")
	}
	if registry.LastUpdate.IsZero() {
		t.Error("Expected LastUpdate to be set")
	}
	if registry.SystemHealth == "" {
		t.Error("Expected SystemHealth to be set")
	}
}

func TestSystemRegistry_SaveAndLoad(t *testing.T) {
	// Create a temporary file for testing
	tempDir := t.TempDir()
	registryPath := filepath.Join(tempDir, "test_registry.json")

	// Create a test registry
	registry := NewSystemRegistry()
	registry.SystemHealth = "test-version"
	
	component := &SystemComponent{
		Name:            "TestComponent",
		Package:         "test/pkg",
		Coverage:        75.0,
		TestsPassing:    8,
		TestsTotal:      10,
		ProductionReady: false,
		Priority:        "MEDIUM",
		RevenueImpact:   "LOW",
		LastUpdated:     time.Now(),
		Functions:       []FunctionInfo{},
		Dependencies:    []string{"dep1"},
		PerformanceMetrics: map[string]string{"latency": "5ms"},
	}
	registry.Components["TestComponent"] = component

	// Test SaveToFile
	err := registry.SaveToFile(registryPath)
	if err != nil {
		t.Fatalf("SaveToFile failed: %v", err)
	}

	// Verify file exists
	if _, err := os.Stat(registryPath); os.IsNotExist(err) {
		t.Fatal("Registry file was not created")
	}

	// Test LoadFromFile
	loadedRegistry, err := LoadFromFile(registryPath)
	if err != nil {
		t.Fatalf("LoadFromFile failed: %v", err)
	}

	if loadedRegistry.SystemHealth != "test-version" {
		t.Errorf("Expected SystemHealth to be 'test-version', got %s", loadedRegistry.SystemHealth)
	}
	
	// Registry initializes with default components, so check that our component was added
	if len(loadedRegistry.Components) == 0 {
		t.Error("Expected at least 1 component")
	}
	
	loadedComponent := loadedRegistry.Components["TestComponent"]
	if loadedComponent == nil {
		t.Fatal("Expected TestComponent to exist")
	}
	
	if loadedComponent.Name != "TestComponent" {
		t.Errorf("Expected component Name to be 'TestComponent', got %s", loadedComponent.Name)
	}
	if loadedComponent.Coverage != 75.0 {
		t.Errorf("Expected component Coverage to be 75.0, got %f", loadedComponent.Coverage)
	}
	if len(loadedComponent.Dependencies) != 1 {
		t.Errorf("Expected 1 dependency, got %d", len(loadedComponent.Dependencies))
	}
	if loadedComponent.PerformanceMetrics["latency"] != "5ms" {
		t.Errorf("Expected latency to be '5ms', got %s", loadedComponent.PerformanceMetrics["latency"])
	}
}

func TestLoadFromFile_NonExistent(t *testing.T) {
	// Test loading from non-existent file
	_, err := LoadFromFile("/non/existent/file.json")
	if err == nil {
		t.Error("Expected error when loading non-existent file")
	}
}

func TestGetRegistryPath(t *testing.T) {
	path := GetRegistryPath()
	if path == "" {
		t.Error("Expected registry path to be returned")
	}
	if !strings.HasSuffix(path, ".json") {
		t.Errorf("Expected path to end with .json, got %s", path)
	}
}

func TestSystemRegistry_JSON_Serialization(t *testing.T) {
	registry := NewSystemRegistry()
	registry.SystemHealth = "HEALTHY"
	
	component := &SystemComponent{
		Name:        "JSONTest",
		Package:     "json/test",
		Coverage:    88.8,
		Priority:    "HIGH",
		Functions:   []FunctionInfo{{Name: "jsonFunc", Tested: true}},
		Dependencies: []string{"json", "testing"},
		PerformanceMetrics: map[string]string{"speed": "fast"},
	}
	registry.Components["JSONTest"] = component

	// Test marshaling
	jsonData, err := json.Marshal(registry)
	if err != nil {
		t.Fatalf("JSON marshaling failed: %v", err)
	}

	// Test unmarshaling
	var unmarshaledRegistry SystemRegistry
	err = json.Unmarshal(jsonData, &unmarshaledRegistry)
	if err != nil {
		t.Fatalf("JSON unmarshaling failed: %v", err)
	}

	if unmarshaledRegistry.SystemHealth != "HEALTHY" {
		t.Errorf("Expected SystemHealth to be 'HEALTHY', got %s", unmarshaledRegistry.SystemHealth)
	}
	
	unmarshaledComponent := unmarshaledRegistry.Components["JSONTest"]
	if unmarshaledComponent == nil {
		t.Fatal("Expected JSONTest component to exist after unmarshaling")
	}
	
	if unmarshaledComponent.Coverage != 88.8 {
		t.Errorf("Expected Coverage to be 88.8, got %f", unmarshaledComponent.Coverage)
	}
	
	if len(unmarshaledComponent.Functions) != 1 {
		t.Errorf("Expected 1 function, got %d", len(unmarshaledComponent.Functions))
	}
	
	if unmarshaledComponent.Functions[0].Name != "jsonFunc" {
		t.Errorf("Expected function name to be 'jsonFunc', got %s", unmarshaledComponent.Functions[0].Name)
	}
}

func TestSystemRegistry_UpdateFromTestRun(t *testing.T) {
	registry := NewSystemRegistry()
	
	// Create test results
	results := []TestResult{
		{
			Name:         "TestLicenseGeneration",
			Package:      "internal/license",
			Passed:       true,
			Coverage:     85.5,
			BenchmarkNsOp: 860000,
		},
		{
			Name:         "TestLicenseValidation", 
			Package:      "internal/license",
			Passed:       true,
			Coverage:     85.5,
		},
		{
			Name:         "TestFailedTest",
			Package:      "internal/engine",
			Passed:       false,
			Error:        "assertion failed",
		},
	}
	
	// Update registry from test results
	initialUpdate := registry.LastUpdate
	time.Sleep(time.Millisecond) // Small delay to ensure time difference
	registry.UpdateFromTestRun(results)
	
	// Check that LastUpdate was updated
	if !registry.LastUpdate.After(initialUpdate) {
		t.Error("Expected LastUpdate to be updated after test run")
	}
	
	// Check license management component was updated
	licenseComp := registry.Components["license_management"]
	if licenseComp == nil {
		t.Fatal("Expected license_management component to exist")
	}
	
	// Should have 2 passing tests added
	if licenseComp.TestsPassing < 2 {
		t.Errorf("Expected at least 2 passing tests, got %d", licenseComp.TestsPassing)
	}
	
	// Coverage should be updated
	if licenseComp.Coverage != 85.5 {
		t.Errorf("Expected coverage to be 85.5, got %f", licenseComp.Coverage)
	}
	
	// Performance metrics should be updated
	if licenseComp.PerformanceMetrics["TestLicenseGeneration"] != "860000ns/op" {
		t.Errorf("Expected benchmark metric to be set, got %s", licenseComp.PerformanceMetrics["TestLicenseGeneration"])
	}
}

func TestSystemRegistry_GetComponentByPackage(t *testing.T) {
	registry := NewSystemRegistry()
	
	// Test finding component by exact package name
	comp := registry.getComponentByPackage("internal/license")
	if comp == nil {
		t.Fatal("Expected to find license component by package name")
	}
	if comp.Name != "License Management" {
		t.Errorf("Expected License Management component, got %s", comp.Name)
	}
	
	// Test finding component by partial package name
	comp = registry.getComponentByPackage("license")
	if comp == nil {
		t.Fatal("Expected to find license component by partial package name")
	}
	
	// Test finding component when package contains component package
	comp = registry.getComponentByPackage("cmd/contextlite")
	if comp == nil {
		t.Fatal("Expected to find REST API component")
	}
	if comp.Name != "REST API" {
		t.Errorf("Expected REST API component, got %s", comp.Name)
	}
	
	// Test non-existent package
	comp = registry.getComponentByPackage("non/existent/package")
	if comp != nil {
		t.Error("Expected nil for non-existent package")
	}
}

func TestSystemRegistry_CalculateOverallMetrics(t *testing.T) {
	registry := NewSystemRegistry()
	
	// Manually set some component metrics for testing
	for _, comp := range registry.Components {
		comp.Coverage = 0.8 // 80% coverage
		comp.ProductionReady = true
	}
	
	// Set one component to not production ready
	registry.Components["license_management"].ProductionReady = false
	registry.Components["license_management"].Coverage = 0.5
	
	registry.calculateOverallMetrics()
	
	// Check overall coverage calculation
	if registry.OverallCoverage < 0.6 || registry.OverallCoverage > 0.9 {
		t.Errorf("Expected reasonable overall coverage, got %f", registry.OverallCoverage)
	}
	
	// Check production readiness calculation
	totalComponents := len(registry.Components)
	expectedReadiness := float64(totalComponents-1) / float64(totalComponents) * 100
	if registry.ProductionReadiness != expectedReadiness {
		t.Errorf("Expected production readiness %f, got %f", expectedReadiness, registry.ProductionReadiness)
	}
	
	// Check system health determination
	if registry.SystemHealth == "" {
		t.Error("Expected system health to be set")
	}
}

func TestSystemRegistry_UpdateCriticalAlerts(t *testing.T) {
	registry := NewSystemRegistry()
	
	// Set up conditions that should trigger alerts
	licenseComp := registry.Components["license_management"]
	licenseComp.Coverage = 0.5 // Below 80% for critical component
	licenseComp.ProductionReady = false
	licenseComp.TestsPassing = 1
	licenseComp.TestsTotal = 10 // Low pass rate
	
	registry.updateCriticalAlerts()
	
	if len(registry.CriticalAlerts) == 0 {
		t.Error("Expected critical alerts to be generated")
	}
	
	// Check for specific alert types
	alertsStr := strings.Join(registry.CriticalAlerts, " ")
	if !strings.Contains(alertsStr, "CRITICAL") {
		t.Error("Expected CRITICAL alert for license management")
	}
	if !strings.Contains(alertsStr, "LOW_COVERAGE") {
		t.Error("Expected LOW_COVERAGE alert")
	}
	if !strings.Contains(alertsStr, "FAILING_TESTS") {
		t.Error("Expected FAILING_TESTS alert")
	}
}

func TestSystemRegistry_GenerateMarkdownReport(t *testing.T) {
	registry := NewSystemRegistry()
	registry.SystemHealth = "TESTING_IN_PROGRESS"
	registry.OverallCoverage = 0.75
	registry.ProductionReadiness = 66.7
	
	report := registry.GenerateMarkdownReport()
	
	if report == "" {
		t.Fatal("Expected non-empty markdown report")
	}
	
	// Check that report contains expected sections
	if !strings.Contains(report, "# ContextLite System Registry & Test Dashboard") {
		t.Error("Expected report to contain title")
	}
	if !strings.Contains(report, "SYSTEM OVERVIEW") {
		t.Error("Expected report to contain system overview")
	}
	if !strings.Contains(report, "COMPONENT STATUS") {
		t.Error("Expected report to contain component status")
	}
	if !strings.Contains(report, "TESTING_IN_PROGRESS") {
		t.Error("Expected report to contain system health")
	}
	if !strings.Contains(report, "75.0%") {
		t.Error("Expected report to contain overall coverage")
	}
	if !strings.Contains(report, "66.7%") {
		t.Error("Expected report to contain production readiness")
	}
	
	// Check for component table headers
	if !strings.Contains(report, "| Component | Coverage | Tests | Production Ready | Priority |") {
		t.Error("Expected report to contain component table")
	}
}

func TestUpdateRegistryFromTestOutput(t *testing.T) {
	// Create temporary directory for test
	tempDir := t.TempDir()
	registryPath := filepath.Join(tempDir, "test_registry.json")
	
	testOutput := `=== RUN   TestLicense
--- PASS: TestLicense (0.01s)
=== RUN   TestValidation  
--- FAIL: TestValidation (0.02s)
PASS
coverage: 85.2% of statements`
	
	err := UpdateRegistryFromTestOutput(testOutput, registryPath)
	if err != nil {
		t.Fatalf("UpdateRegistryFromTestOutput failed: %v", err)
	}
	
	// Verify registry was created
	if _, err := os.Stat(registryPath); os.IsNotExist(err) {
		t.Fatal("Registry file was not created")
	}
	
	// Verify markdown report was created
	markdownPath := strings.Replace(registryPath, ".json", ".md", 1)
	if _, err := os.Stat(markdownPath); os.IsNotExist(err) {
		t.Fatal("Markdown report was not created")
	}
}

func TestParseTestOutput(t *testing.T) {
	testOutput := `=== RUN   TestLicenseGeneration
--- PASS: TestLicenseGeneration (0.86s)
=== RUN   TestValidation
--- FAIL: TestValidation (0.02s)
=== RUN   TestBenchmark
--- PASS: TestBenchmark (1.23s)
BenchmarkLicenseGeneration-24    1418    860242 ns/op
coverage: 85.2% of statements`
	
	results := parseTestOutput(testOutput)
	
	if len(results) != 3 {
		t.Errorf("Expected 3 test results, got %d", len(results))
	}
	
	// Check first result (PASS)
	if results[0].Name != "TestLicenseGeneration" {
		t.Errorf("Expected TestLicenseGeneration, got %s", results[0].Name)
	}
	if !results[0].Passed {
		t.Error("Expected TestLicenseGeneration to be marked as passed")
	}
	if results[0].Duration != 860*time.Millisecond {
		t.Errorf("Expected duration 0.86s, got %v", results[0].Duration)
	}
	
	// Check second result (FAIL)
	if results[1].Name != "TestValidation" {
		t.Errorf("Expected TestValidation, got %s", results[1].Name)
	}
	if results[1].Passed {
		t.Error("Expected TestValidation to be marked as failed")
	}
	
	// Check third result
	if results[2].Name != "TestBenchmark" {
		t.Errorf("Expected TestBenchmark, got %s", results[2].Name)
	}
}