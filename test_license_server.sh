#!/bin/bash

# ContextLite License Server Test Suite
# Comprehensive validation for production readiness

set -e  # Exit on any error

# Configuration
if [ -z "$1" ]; then
    echo "Usage: $0 <server-url>"
    echo "Example: $0 https://contextlite-testing-production.up.railway.app"
    exit 1
fi

SERVER_URL="$1"
TEST_EMAIL="test-$(date +%s)@example.com"
TEST_SESSION="test-session-$(date +%s)"

echo "🧪 CONTEXTLITE LICENSE SERVER TEST SUITE"
echo "=========================================="
echo "Testing server: $SERVER_URL"
echo "Started at: $(date)"
echo ""

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Test counter
TESTS_RUN=0
TESTS_PASSED=0

run_test() {
    local test_name="$1"
    local test_command="$2"
    local expected_result="$3"
    
    TESTS_RUN=$((TESTS_RUN + 1))
    echo -n "[$TESTS_RUN] Testing $test_name... "
    
    if eval "$test_command" > /dev/null 2>&1; then
        if [ -n "$expected_result" ]; then
            # Check if output contains expected result
            result=$(eval "$test_command" 2>/dev/null)
            if echo "$result" | grep -q "$expected_result"; then
                echo -e "${GREEN}PASS${NC}"
                TESTS_PASSED=$((TESTS_PASSED + 1))
                return 0
            else
                echo -e "${RED}FAIL${NC} (Expected: $expected_result)"
                return 1
            fi
        else
            echo -e "${GREEN}PASS${NC}"
            TESTS_PASSED=$((TESTS_PASSED + 1))
            return 0
        fi
    else
        echo -e "${RED}FAIL${NC}"
        return 1
    fi
}

echo "🏥 HEALTH CHECK TESTS"
echo "===================="

# Test 1: Basic Health Check
run_test "Health endpoint" \
    "curl -s -f $SERVER_URL/health" \
    "healthy"

# Test 2: Health response format
run_test "Health JSON format" \
    "curl -s $SERVER_URL/health | jq -e '.status' 2>/dev/null" \
    "healthy"

echo ""
echo "🔐 LICENSE FUNCTIONALITY TESTS"
echo "=============================="

# Test 3: License generation endpoint
run_test "License generation (Professional)" \
    "curl -s -X POST $SERVER_URL/generate -H 'Content-Type: application/json' -d '{\"email\":\"$TEST_EMAIL\",\"tier\":\"professional\"}' | jq -e '.license' 2>/dev/null"

# Test 4: License validation
GENERATED_LICENSE=$(curl -s -X POST $SERVER_URL/generate -H 'Content-Type: application/json' -d "{\"email\":\"$TEST_EMAIL\",\"tier\":\"professional\"}" | jq -r '.license' 2>/dev/null)

if [ "$GENERATED_LICENSE" != "null" ] && [ -n "$GENERATED_LICENSE" ]; then
    run_test "License validation" \
        "curl -s -X POST $SERVER_URL/validate -H 'Content-Type: application/json' -d '{\"license\":\"$GENERATED_LICENSE\"}' | jq -e '.valid' 2>/dev/null" \
        "true"
else
    echo "[$((TESTS_RUN + 1))] Testing License validation... ${YELLOW}SKIP${NC} (No license to validate)"
    TESTS_RUN=$((TESTS_RUN + 1))
fi

# Test 5: Email test endpoint
run_test "Email system test" \
    "curl -s -X POST $SERVER_URL/test-email -H 'Content-Type: application/json' -d '{\"email\":\"$TEST_EMAIL\"}' | jq -e '.success' 2>/dev/null" \
    "true"

echo ""
echo "🛒 ABANDONED CART TESTS"
echo "======================"

# Test 6: Cart creation
run_test "Abandoned cart creation" \
    "curl -s -X POST $SERVER_URL/cart/create -H 'Content-Type: application/json' -d '{\"session_id\":\"$TEST_SESSION\",\"email\":\"$TEST_EMAIL\",\"amount\":9900,\"product_name\":\"Test Product\",\"payment_url\":\"https://test.com\"}' | jq -e '.success' 2>/dev/null" \
    "true"

# Test 7: Cart analytics
run_test "Cart analytics endpoint" \
    "curl -s $SERVER_URL/cart/status | jq -e '.analytics.total_abandoned_carts' 2>/dev/null"

# Test 8: Cart completion
run_test "Cart completion" \
    "curl -s -X POST $SERVER_URL/cart/complete -H 'Content-Type: application/json' -d '{\"session_id\":\"$TEST_SESSION\"}' | jq -e '.success' 2>/dev/null" \
    "true"

# Test 9: Mass email processing
run_test "Mass email processing" \
    "curl -s -X POST $SERVER_URL/cart/abandon | jq -e '.success' 2>/dev/null" \
    "true"

echo ""
echo "📊 ANALYTICS & TRACKING TESTS"
echo "============================="

# Test 10: License activation
run_test "License activation endpoint" \
    "curl -s -X POST $SERVER_URL/activate -H 'Content-Type: application/json' -d '{\"license_key\":\"test\",\"email\":\"$TEST_EMAIL\",\"hardware_id\":\"test123\",\"tier\":\"professional\"}' | jq -e '.success' 2>/dev/null" \
    "true"

# Test 11: Usage tracking
run_test "Usage tracking endpoint" \
    "curl -s -X POST $SERVER_URL/usage -H 'Content-Type: application/json' -d '{\"license_key\":\"test\",\"activation_id\":\"test\",\"event_type\":\"query\"}' | jq -e '.success' 2>/dev/null" \
    "true"

# Test 12: Analytics endpoint
run_test "Analytics endpoint" \
    "curl -s $SERVER_URL/analytics | jq -e '.success' 2>/dev/null" \
    "true"

echo ""
echo "🔍 SECURITY & ERROR HANDLING TESTS"
echo "=================================="

# Test 13: Invalid license validation
run_test "Invalid license handling" \
    "curl -s -X POST $SERVER_URL/validate -H 'Content-Type: application/json' -d '{\"license\":\"invalid-license\"}' | jq -e '.valid' 2>/dev/null" \
    "false"

# Test 14: Missing parameters handling
run_test "Missing email parameter handling" \
    "curl -s -w '%{http_code}' -X POST $SERVER_URL/test-email -H 'Content-Type: application/json' -d '{}' | grep -q '400'"

# Test 15: Invalid JSON handling
run_test "Invalid JSON handling" \
    "curl -s -w '%{http_code}' -X POST $SERVER_URL/generate -H 'Content-Type: application/json' -d 'invalid-json' | grep -q '400'"

echo ""
echo "🎯 TEST RESULTS SUMMARY"
echo "======================"
echo -e "Tests run: $TESTS_RUN"
echo -e "Tests passed: ${GREEN}$TESTS_PASSED${NC}"
echo -e "Tests failed: ${RED}$((TESTS_RUN - TESTS_PASSED))${NC}"

if [ $TESTS_PASSED -eq $TESTS_RUN ]; then
    echo -e "\n🎉 ${GREEN}ALL TESTS PASSED! Server is ready for production.${NC}"
    echo "Completed at: $(date)"
    exit 0
else
    echo -e "\n❌ ${RED}Some tests failed. Server needs attention before production deployment.${NC}"
    echo "Completed at: $(date)"
    exit 1
fi
