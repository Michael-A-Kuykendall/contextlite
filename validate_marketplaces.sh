#!/bin/bash

# Phase 1 Integration Testing - Marketplace Validation Script
# Systematically validates all high-risk marketplaces

echo "🧪 ContextLite Phase 1 Integration Testing"
echo "=========================================="
echo "Validating high-risk marketplaces for v0.9.0-alpha5"
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Test results
declare -A results

test_marketplace() {
    local name=$1
    local command=$2
    local expected_pattern=$3
    
    echo -e "${BLUE}Testing ${name}...${NC}"
    
    if eval "$command" 2>&1 | grep -q "$expected_pattern"; then
        echo -e "${GREEN}✅ ${name}: Available${NC}"
        results["$name"]="PASS"
    else
        echo -e "${RED}❌ ${name}: Not available yet${NC}"
        results["$name"]="FAIL"
    fi
    echo ""
}

test_direct_availability() {
    local name=$1
    local url=$2
    
    echo -e "${BLUE}Testing ${name} via HTTP...${NC}"
    
    if curl -s -o /dev/null -w "%{http_code}" "$url" | grep -q "200\|302"; then
        echo -e "${GREEN}✅ ${name}: HTTP accessible${NC}"
        results["$name"]="PASS"
    else
        echo -e "${RED}❌ ${name}: Not accessible yet${NC}"
        results["$name"]="FAIL"
    fi
    echo ""
}

echo "🔍 Phase 1: High-Risk Marketplaces"
echo "=================================="

# GitHub Releases (baseline)
echo -e "${BLUE}Testing GitHub Releases...${NC}"
if curl -s https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases | grep -q "v0.9.0-alpha"; then
    echo -e "${GREEN}✅ GitHub Releases: Available${NC}"
    results["GitHub Releases"]="PASS"
else
    echo -e "${RED}❌ GitHub Releases: Not available${NC}"
    results["GitHub Releases"]="FAIL"
fi
echo ""

# npm (JavaScript ecosystem)
test_marketplace "npm" "npm view contextlite" "contextlite"

# PyPI (Python ecosystem)  
test_marketplace "PyPI" "pip show contextlite" "Name: contextlite"

# Docker Hub (Container ecosystem)
test_marketplace "Docker Hub" "docker search contextlite" "contextlite"

# Homebrew (macOS package manager)
test_marketplace "Homebrew" "brew search contextlite" "contextlite"

# Check web endpoints
test_direct_availability "npm Registry" "https://registry.npmjs.org/contextlite"
test_direct_availability "PyPI" "https://pypi.org/project/contextlite/"
test_direct_availability "Docker Hub" "https://hub.docker.com/r/contextlite/contextlite"

echo "📊 Phase 1 Results Summary"
echo "========================="

total=0
passed=0

for marketplace in "${!results[@]}"; do
    result=${results[$marketplace]}
    total=$((total + 1))
    
    if [ "$result" = "PASS" ]; then
        echo -e "${GREEN}✅ $marketplace${NC}"
        passed=$((passed + 1))
    else
        echo -e "${RED}❌ $marketplace${NC}"
    fi
done

echo ""
echo -e "Results: ${GREEN}$passed${NC}/${total} marketplaces validated"

if [ $passed -eq $total ]; then
    echo -e "${GREEN}🎉 Phase 1 SUCCESS: All high-risk marketplaces validated${NC}"
    echo "Ready to proceed to Phase 2 (medium-risk marketplaces)"
    exit 0
elif [ $passed -gt 0 ]; then
    echo -e "${YELLOW}⚠️  Phase 1 PARTIAL: Some marketplaces still processing${NC}"
    echo "Continue monitoring and re-run validation"
    exit 1
else
    echo -e "${RED}❌ Phase 1 FAILED: No marketplaces validated${NC}"
    echo "Check GitHub Actions workflow for issues"
    exit 2
fi
