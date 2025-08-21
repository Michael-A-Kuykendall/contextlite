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