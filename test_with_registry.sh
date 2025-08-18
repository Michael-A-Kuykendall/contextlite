#!/bin/bash

# ContextLite Test Runner with Auto-Registry Updates
# Runs comprehensive tests and automatically updates system registry

set -e

echo "🚀 ContextLite Comprehensive Test Suite with Registry Updates"
echo "============================================================"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Directories
REPO_ROOT=$(pwd)
REGISTRY_FILE="${REPO_ROOT}/system_registry.json"
COVERAGE_FILE="${REPO_ROOT}/coverage_complete.out"
RESULTS_DIR="${REPO_ROOT}/test_results"

# Create results directory
mkdir -p "${RESULTS_DIR}"

# Initialize registry if it doesn't exist
if [ ! -f "${REGISTRY_FILE}" ]; then
    echo "📝 Initializing system registry..."
    cat > "${REGISTRY_FILE}" << 'EOF'
{
  "components": {},
  "last_update": "2025-08-18T14:15:00Z",
  "overall_coverage": 0.0,
  "system_health": "TESTING_REQUIRED",
  "production_readiness": 0.0,
  "critical_alerts": []
}
EOF
fi

echo -e "${BLUE}📊 Starting comprehensive test suite...${NC}"

# Function to run tests for a specific component and update registry
run_component_tests() {
    local component_name="$1"
    local package_path="$2"
    local component_id="$3"
    
    echo -e "${YELLOW}Testing ${component_name}...${NC}"
    
    # Run tests with coverage
    TEST_OUTPUT="${RESULTS_DIR}/${component_id}_test.out"
    COVERAGE_OUTPUT="${RESULTS_DIR}/${component_id}_coverage.out"
    
    if go test -v -coverprofile="${COVERAGE_OUTPUT}" "${package_path}" > "${TEST_OUTPUT}" 2>&1; then
        echo -e "${GREEN}✅ ${component_name} tests PASSED${NC}"
        TEST_STATUS="PASS"
    else
        echo -e "${RED}❌ ${component_name} tests FAILED${NC}"
        TEST_STATUS="FAIL"
        cat "${TEST_OUTPUT}"
    fi
    
    # Extract coverage percentage
    COVERAGE_PERCENT=0
    if [ -f "${COVERAGE_OUTPUT}" ]; then
        COVERAGE_PERCENT=$(go tool cover -func="${COVERAGE_OUTPUT}" | grep "total:" | awk '{print $3}' | sed 's/%//')
        if [ -z "${COVERAGE_PERCENT}" ]; then
            COVERAGE_PERCENT=0
        fi
    fi
    
    # Count tests
    TOTAL_TESTS=$(grep -c "=== RUN" "${TEST_OUTPUT}" 2>/dev/null || echo "0")
    PASSED_TESTS=$(grep -c "--- PASS:" "${TEST_OUTPUT}" 2>/dev/null || echo "0")
    FAILED_TESTS=$(grep -c "--- FAIL:" "${TEST_OUTPUT}" 2>/dev/null || echo "0")
    
    echo "   Coverage: ${COVERAGE_PERCENT}%"
    echo "   Tests: ${PASSED_TESTS}/${TOTAL_TESTS} passed"
    
    # Update registry using Go helper
    update_registry_component "${component_id}" "${component_name}" "${package_path}" \
        "${COVERAGE_PERCENT}" "${PASSED_TESTS}" "${TOTAL_TESTS}" "${TEST_STATUS}"
    
    echo ""
}

# Function to update registry component
update_registry_component() {
    local component_id="$1"
    local component_name="$2"
    local package_path="$3"
    local coverage="$4"
    local passed="$5"
    local total="$6"
    local status="$7"
    
    # Calculate production readiness
    PRODUCTION_READY="false"
    if (( $(echo "${coverage} >= 80" | bc -l) )) && (( passed == total )) && (( total > 0 )); then
        PRODUCTION_READY="true"
    fi
    
    # Create temporary Go program to update registry
    cat > "${RESULTS_DIR}/update_registry.go" << EOF
package main

import (
    "encoding/json"
    "fmt"
    "os"
    "time"
)

type Component struct {
    Name            string    \`json:"name"\`
    Package         string    \`json:"package"\`
    Coverage        float64   \`json:"coverage"\`
    TestsPassing    int       \`json:"tests_passing"\`
    TestsTotal      int       \`json:"tests_total"\`
    ProductionReady bool      \`json:"production_ready"\`
    Priority        string    \`json:"priority"\`
    RevenueImpact   string    \`json:"revenue_impact"\`
    LastUpdated     time.Time \`json:"last_updated"\`
}

type Registry struct {
    Components         map[string]*Component \`json:"components"\`
    LastUpdate         time.Time             \`json:"last_update"\`
    OverallCoverage    float64               \`json:"overall_coverage"\`
    SystemHealth       string                \`json:"system_health"\`
    ProductionReadiness float64              \`json:"production_readiness"\`
    CriticalAlerts     []string              \`json:"critical_alerts"\`
}

func main() {
    registryPath := "${REGISTRY_FILE}"
    
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
    
    switch "${component_id}" {
    case "license_management", "license_server":
        priority = "CRITICAL"
        revenueImpact = "CRITICAL"
    case "core_engine", "storage", "rest_api":
        priority = "HIGH"
        revenueImpact = "MEDIUM"
    }
    
    // Update component
    registry.Components["${component_id}"] = &Component{
        Name:            "${component_name}",
        Package:         "${package_path}",
        Coverage:        ${coverage} / 100.0,
        TestsPassing:    ${passed},
        TestsTotal:      ${total},
        ProductionReady: ${PRODUCTION_READY},
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
        "${component_name}", ${coverage}, ${passed}, ${total})
}
EOF
    
    # Run the registry update
    cd "${RESULTS_DIR}"
    go run update_registry.go
    cd "${REPO_ROOT}"
    rm -f "${RESULTS_DIR}/update_registry.go"
}

# Main test execution
echo -e "${BLUE}🔍 Running component tests...${NC}"

# Test License Management (Critical)
run_component_tests "License Management" "./test/license/..." "license_management"

# Test License Server (Critical)  
run_component_tests "License Server" "./cmd/license-server/..." "license_server"

# Test Core Engine (High Priority)
run_component_tests "Core Engine" "./internal/engine/..." "core_engine"

# Test Storage Layer (High Priority)
run_component_tests "Storage Layer" "./pkg/storage/..." "storage"

# Test Client Library (High Priority)
run_component_tests "Client Library" "./pkg/contextlite/..." "client"

# Test REST API (High Priority)
run_component_tests "REST API" "./cmd/contextlite/..." "rest_api"

# Test Integration Tests (if they exist)
if [ -d "./test/integration" ]; then
    run_component_tests "Integration Tests" "./test/integration/..." "integration"
fi

# Generate overall coverage report
echo -e "${BLUE}📈 Generating overall coverage report...${NC}"
go test -coverprofile="${COVERAGE_FILE}" ./... > "${RESULTS_DIR}/overall_test.out" 2>&1 || true

if [ -f "${COVERAGE_FILE}" ]; then
    OVERALL_COVERAGE=$(go tool cover -func="${COVERAGE_FILE}" | grep "total:" | awk '{print $3}' | sed 's/%//')
    echo -e "${GREEN}Overall Coverage: ${OVERALL_COVERAGE}%${NC}"
    
    # Generate HTML coverage report
    go tool cover -html="${COVERAGE_FILE}" -o "${RESULTS_DIR}/coverage.html"
    echo -e "${BLUE}Coverage report generated: ${RESULTS_DIR}/coverage.html${NC}"
fi

# Update main SYSTEM_REGISTRY.md
echo -e "${BLUE}📝 Updating SYSTEM_REGISTRY.md...${NC}"
if [ -f "${REGISTRY_FILE}" ]; then
    # Create a Go program to update the markdown
    cat > "${RESULTS_DIR}/update_markdown.go" << 'EOF'
package main

import (
    "encoding/json"
    "fmt"
    "os"
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
    registryData, err := os.ReadFile("system_registry.json")
    if err != nil {
        return
    }
    
    var registry Registry
    if err := json.Unmarshal(registryData, &registry); err != nil {
        return
    }
    
    // Read existing markdown
    markdownPath := "SYSTEM_REGISTRY.md"
    content, err := os.ReadFile(markdownPath)
    if err != nil {
        return
    }
    
    lines := strings.Split(string(content), "\n")
    
    // Update key metrics
    for i, line := range lines {
        if strings.HasPrefix(strings.TrimSpace(line), "**Last Updated**:") {
            lines[i] = fmt.Sprintf("**Last Updated**: %s", registry.LastUpdate.Format("2006-01-02 15:04:05"))
        } else if strings.HasPrefix(strings.TrimSpace(line), "**System Health**:") {
            healthIcon := "🔴"
            if registry.SystemHealth == "PRODUCTION_READY" {
                healthIcon = "✅"
            } else if strings.Contains(registry.SystemHealth, "TESTING") {
                healthIcon = "🟡"
            }
            lines[i] = fmt.Sprintf("**System Health**: %s %s", healthIcon, registry.SystemHealth)
        } else if strings.HasPrefix(strings.TrimSpace(line), "**Production Readiness**:") {
            lines[i] = fmt.Sprintf("**Production Readiness**: %.1f%%", registry.ProductionReadiness)
        }
    }
    
    // Write updated content
    os.WriteFile(markdownPath, []byte(strings.Join(lines, "\n")), 0644)
    
    fmt.Printf("SYSTEM_REGISTRY.md updated - Health: %s, Readiness: %.1f%%\n",
        registry.SystemHealth, registry.ProductionReadiness)
}
EOF

    cd "${RESULTS_DIR}"
    go run update_markdown.go
    cd "${REPO_ROOT}"
    rm -f "${RESULTS_DIR}/update_markdown.go"
fi

# Final summary
echo ""
echo -e "${GREEN}🎉 Test Suite Complete!${NC}"
echo "=============================================="

# Show registry summary
if [ -f "${REGISTRY_FILE}" ]; then
    echo -e "${BLUE}📊 System Status Summary:${NC}"
    
    # Use jq if available, otherwise use basic parsing
    if command -v jq >/dev/null 2>&1; then
        SYSTEM_HEALTH=$(jq -r '.system_health' "${REGISTRY_FILE}")
        PRODUCTION_READINESS=$(jq -r '.production_readiness' "${REGISTRY_FILE}")
        OVERALL_COVERAGE=$(jq -r '.overall_coverage' "${REGISTRY_FILE}")
        CRITICAL_ALERTS_COUNT=$(jq -r '.critical_alerts | length' "${REGISTRY_FILE}")
        
        echo "   System Health: ${SYSTEM_HEALTH}"
        echo "   Production Readiness: ${PRODUCTION_READINESS}%"
        echo "   Overall Coverage: $(echo "${OVERALL_COVERAGE} * 100" | bc -l | cut -d. -f1)%"
        echo "   Critical Alerts: ${CRITICAL_ALERTS_COUNT}"
        
        if [ "${CRITICAL_ALERTS_COUNT}" -gt 0 ]; then
            echo -e "${RED}⚠️  Critical alerts detected - check SYSTEM_REGISTRY.md${NC}"
        fi
    else
        echo "   Registry updated: ${REGISTRY_FILE}"
        echo "   Check SYSTEM_REGISTRY.md for detailed status"
    fi
fi

echo ""
echo -e "${BLUE}📁 Test artifacts:${NC}"
echo "   Registry: ${REGISTRY_FILE}"
echo "   Results: ${RESULTS_DIR}/"
echo "   Coverage: ${RESULTS_DIR}/coverage.html"
echo "   System Registry: SYSTEM_REGISTRY.md"

echo ""
echo -e "${GREEN}✅ Registry-integrated testing complete!${NC}"
