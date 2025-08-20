#!/bin/bash
# ContextLite Functional Test Runner
# Tests all deployed packages to verify they actually work
set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Test results tracking
TESTS_PASSED=0
TESTS_FAILED=0
TESTS_TOTAL=0
RESULTS_FILE="FUNCTIONAL_TEST_RESULTS_$(date +%Y%m%d_%H%M%S).md"

# Function to log results
log_result() {
    local test_name="$1"
    local status="$2"
    local details="$3"
    
    echo "## $test_name" >> "$RESULTS_FILE"
    echo "**Status**: $status" >> "$RESULTS_FILE"
    echo "**Timestamp**: $(date)" >> "$RESULTS_FILE"
    echo "**Details**: $details" >> "$RESULTS_FILE"
    echo "" >> "$RESULTS_FILE"
    
    if [ "$status" = "✅ PASSED" ]; then
        TESTS_PASSED=$((TESTS_PASSED + 1))
        echo -e "${GREEN}✅ $test_name: PASSED${NC}"
    else
        TESTS_FAILED=$((TESTS_FAILED + 1))
        echo -e "${RED}❌ $test_name: FAILED${NC}"
        echo -e "${RED}   Details: $details${NC}"
    fi
    TESTS_TOTAL=$((TESTS_TOTAL + 1))
}

# Function to run a test script
run_test() {
    local test_script="$1"
    local test_name="$2"
    
    echo -e "${BLUE}🧪 Running $test_name...${NC}"
    
    if [ ! -f "$test_script" ]; then
        log_result "$test_name" "❌ FAILED" "Test script not found: $test_script"
        return 1
    fi
    
    # Run the test and capture output
    if output=$(bash "$test_script" 2>&1); then
        log_result "$test_name" "✅ PASSED" "Test completed successfully"
        echo -e "${GREEN}   Output: $output${NC}" | head -n 5
    else
        log_result "$test_name" "❌ FAILED" "Test script failed with exit code $?"
        echo -e "${RED}   Error output: $output${NC}" | head -n 10
    fi
}

# Initialize results file
cat > "$RESULTS_FILE" << 'EOF'
# ContextLite Functional Test Results

**Generated**: $(date)
**Purpose**: Verify that all deployed packages actually work
**Critical**: This is the first time we're testing our production packages!

## Executive Summary

EOF

echo -e "${BLUE}🚀 CONTEXTLITE FUNCTIONAL TEST SUITE${NC}"
echo -e "${BLUE}=====================================${NC}"
echo -e "${YELLOW}Testing all deployed packages for the first time!${NC}"
echo -e "${YELLOW}Results will be saved to: $RESULTS_FILE${NC}"
echo ""

# Pre-test validation
echo -e "${BLUE}🔍 Pre-test validation...${NC}"

# Check if we have required tools
MISSING_TOOLS=""
command -v curl >/dev/null 2>&1 || MISSING_TOOLS="$MISSING_TOOLS curl"
command -v unzip >/dev/null 2>&1 || MISSING_TOOLS="$MISSING_TOOLS unzip"

if [ -n "$MISSING_TOOLS" ]; then
    echo -e "${RED}❌ Missing required tools: $MISSING_TOOLS${NC}"
    log_result "Pre-test Validation" "❌ FAILED" "Missing tools: $MISSING_TOOLS"
    exit 1
else
    echo -e "${GREEN}✅ All required tools available${NC}"
    log_result "Pre-test Validation" "✅ PASSED" "All required tools available"
fi

# Test internet connectivity
echo -e "${BLUE}🌐 Testing internet connectivity...${NC}"
if curl -s --connect-timeout 5 https://api.github.com >/dev/null; then
    echo -e "${GREEN}✅ Internet connectivity OK${NC}"
    log_result "Internet Connectivity" "✅ PASSED" "Can reach GitHub API"
else
    echo -e "${RED}❌ No internet connectivity${NC}"
    log_result "Internet Connectivity" "❌ FAILED" "Cannot reach GitHub API"
fi

echo ""
echo -e "${BLUE}📋 Running Package Tests...${NC}"
echo -e "${BLUE}============================${NC}"

# Test 1: Direct Binary from GitHub Releases
run_test "test/integration/scripts/test_direct_binary.sh" "GitHub Binary Release"

# Test 2: npm Package
if command -v npm >/dev/null 2>&1; then
    run_test "test/integration/scripts/test_npm_package.sh" "npm Package"
else
    log_result "npm Package" "⏭️ SKIPPED" "npm not available on this system"
    echo -e "${YELLOW}⏭️ npm Package: SKIPPED (npm not available)${NC}"
fi

# Test 3: PyPI Package  
if command -v python >/dev/null 2>&1 || command -v python3 >/dev/null 2>&1; then
    run_test "test/integration/scripts/test_pypi_package.sh" "PyPI Package"
else
    log_result "PyPI Package" "⏭️ SKIPPED" "Python not available on this system"
    echo -e "${YELLOW}⏭️ PyPI Package: SKIPPED (Python not available)${NC}"
fi

# Test 4: Docker Container
if command -v docker >/dev/null 2>&1; then
    run_test "test/integration/scripts/test_docker_container.sh" "Docker Container"
else
    log_result "Docker Container" "⏭️ SKIPPED" "Docker not available on this system"
    echo -e "${YELLOW}⏭️ Docker Container: SKIPPED (Docker not available)${NC}"
fi

# Test 5: Hugging Face Download Page
run_test "test/integration/scripts/test_hugging_face.sh" "Hugging Face Download"

echo ""
echo -e "${BLUE}📊 FINAL RESULTS${NC}"
echo -e "${BLUE}================${NC}"

# Calculate success rate
SUCCESS_RATE=0
if [ $TESTS_TOTAL -gt 0 ]; then
    SUCCESS_RATE=$((TESTS_PASSED * 100 / TESTS_TOTAL))
fi

echo -e "Total Tests: $TESTS_TOTAL"
echo -e "${GREEN}Passed: $TESTS_PASSED${NC}"
echo -e "${RED}Failed: $TESTS_FAILED${NC}"
echo -e "Success Rate: ${SUCCESS_RATE}%"

# Update results file with summary
cat >> "$RESULTS_FILE" << EOF

**Total Tests**: $TESTS_TOTAL
**Passed**: $TESTS_PASSED  
**Failed**: $TESTS_FAILED
**Success Rate**: ${SUCCESS_RATE}%

## Analysis

EOF

if [ $TESTS_FAILED -eq 0 ]; then
    echo -e "${GREEN}🎉 ALL TESTS PASSED! Production packages are working!${NC}"
    cat >> "$RESULTS_FILE" << EOF
🎉 **ALL TESTS PASSED!** 

Our production packages are actually working! This is fantastic news for our deployment pipeline.

### Key Findings:
- All tested deployment channels are functional
- Users can successfully install and use ContextLite
- Trial system activates correctly
- API endpoints respond properly
- No critical deployment issues found

### Recommendations:
- ✅ Safe to continue with public launch
- ✅ Deployment pipeline is reliable
- ✅ User experience will be smooth
EOF
elif [ $SUCCESS_RATE -ge 80 ]; then
    echo -e "${YELLOW}⚠️ MOSTLY WORKING: $SUCCESS_RATE% success rate${NC}"
    echo -e "${YELLOW}Some packages have issues but core functionality works${NC}"
    cat >> "$RESULTS_FILE" << EOF
⚠️ **MOSTLY WORKING** ($SUCCESS_RATE% success rate)

Some deployment channels have issues but the core functionality is working.

### Key Findings:
- Core packages (GitHub binary) likely working
- Some package managers may have deployment issues
- Critical functionality is available to users
- Minor issues need addressing

### Recommendations:
- ✅ Safe to launch with working channels
- 🔧 Fix failing channels in parallel
- 📝 Document known issues for users
- 🚀 Don't let perfect be enemy of good
EOF
else
    echo -e "${RED}🚨 CRITICAL ISSUES: Only $SUCCESS_RATE% success rate${NC}"
    echo -e "${RED}Multiple packages are broken - deployment needs attention${NC}"
    cat >> "$RESULTS_FILE" << EOF
🚨 **CRITICAL ISSUES** ($SUCCESS_RATE% success rate)

Multiple deployment channels are broken. This needs immediate attention.

### Key Findings:
- Majority of packages are not working
- Users will have difficulty installing ContextLite
- Deployment pipeline has fundamental issues
- Launch should be delayed

### Recommendations:
- 🛑 STOP launch until issues resolved
- 🔧 Focus on fixing core deployment channels
- 🧪 Re-run tests after each fix
- 🎯 Prioritize GitHub binary and one package manager
EOF
fi

echo ""
echo -e "${BLUE}📄 Full results saved to: $RESULTS_FILE${NC}"
echo -e "${BLUE}💡 Next steps:${NC}"

if [ $TESTS_FAILED -gt 0 ]; then
    echo -e "${YELLOW}1. Review failed tests in the results file${NC}"
    echo -e "${YELLOW}2. Fix the underlying deployment issues${NC}"  
    echo -e "${YELLOW}3. Re-run tests to verify fixes${NC}"
    echo -e "${YELLOW}4. Update deployment documentation${NC}"
else
    echo -e "${GREEN}1. Celebrate! 🎉 Our packages actually work!${NC}"
    echo -e "${GREEN}2. Proceed with launch confidence${NC}"
    echo -e "${GREEN}3. Set up regular automated testing${NC}"
    echo -e "${GREEN}4. Monitor package download success rates${NC}"
fi

# Exit with error code if any tests failed
if [ $TESTS_FAILED -gt 0 ]; then
    exit 1
else
    exit 0
fi
