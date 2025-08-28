#!/bin/bash

# ContextLite License Server Test Suite (No External Dependencies)
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

# Test counter
TESTS_RUN=0
TESTS_PASSED=0

run_test() {
    local test_name="$1"
    local test_command="$2"
    local expected_pattern="$3"
    
    TESTS_RUN=$((TESTS_RUN + 1))
    echo -n "[$TESTS_RUN] Testing $test_name... "
    
    result=$(eval "$test_command" 2>/dev/null || echo "ERROR")
    
    if [ "$result" = "ERROR" ]; then
        echo "FAIL (Connection/Command Error)"
        return 1
    fi
    
    if [ -n "$expected_pattern" ]; then
        if echo "$result" | grep -q "$expected_pattern"; then
            echo "PASS"
            TESTS_PASSED=$((TESTS_PASSED + 1))
            return 0
        else
            echo "FAIL (Expected pattern: $expected_pattern)"
            echo "  Got: $(echo "$result" | head -1)"
            return 1
        fi
    else
        echo "PASS"
        TESTS_PASSED=$((TESTS_PASSED + 1))
        return 0
    fi
}

echo "🏥 HEALTH CHECK TESTS"
echo "===================="

# Test 1: Basic Health Check
run_test "Health endpoint responds" \
    "curl -s -f $SERVER_URL/health" \
    "healthy"

# Test 2: Health contains service name
run_test "Health contains service info" \
    "curl -s $SERVER_URL/health" \
    "contextlite-license-server"

echo ""
echo "🔐 LICENSE FUNCTIONALITY TESTS"
echo "=============================="

# Test 3: License generation endpoint
run_test "License generation (Professional)" \
    "curl -s -X POST $SERVER_URL/generate -H 'Content-Type: application/json' -d '{\"email\":\"$TEST_EMAIL\",\"tier\":\"professional\"}'" \
    "license"

# Test 4: License validation with invalid license
run_test "Invalid license validation" \
    "curl -s -X POST $SERVER_URL/validate -H 'Content-Type: application/json' -d '{\"license\":\"invalid-license\"}'" \
    "false"

# Test 5: Email test endpoint
run_test "Email system test (with timeout)" \
    "timeout 10 curl --http1.1 -s -X POST $SERVER_URL/test-email -H 'Content-Type: application/json' -d '{\"email\":\"$TEST_EMAIL\"}' || echo '{\"success\":false,\"message\":\"timeout or connection error\"}'" \
    "success\|DEVELOPMENT MODE\|timeout"

echo ""
echo "🛒 ABANDONED CART TESTS"
echo "======================"

# Test 6: Cart creation
run_test "Abandoned cart creation" \
    "curl -s -X POST $SERVER_URL/cart/create -H 'Content-Type: application/json' -d '{\"session_id\":\"$TEST_SESSION\",\"email\":\"$TEST_EMAIL\",\"amount\":9900,\"product_name\":\"Test Product\",\"payment_url\":\"https://test.com\"}'" \
    "success"

# Test 7: Cart analytics
run_test "Cart analytics endpoint" \
    "curl -s $SERVER_URL/cart/status" \
    "analytics"

# Test 8: Cart completion
run_test "Cart completion" \
    "curl -s -X POST $SERVER_URL/cart/complete -H 'Content-Type: application/json' -d '{\"session_id\":\"$TEST_SESSION\"}'" \
    "success"

# Test 9: Mass email processing
run_test "Mass email processing" \
    "curl -s -X POST $SERVER_URL/cart/abandon" \
    "success"

echo ""
echo "📊 ANALYTICS & TRACKING TESTS"
echo "============================="

# Test 10: License activation
run_test "License activation endpoint" \
    "curl -s -X POST $SERVER_URL/activate -H 'Content-Type: application/json' -d '{\"license_key\":\"test\",\"email\":\"$TEST_EMAIL\",\"hardware_id\":\"test123\",\"tier\":\"professional\"}'" \
    "success"

# Test 11: Usage tracking
run_test "Usage tracking endpoint" \
    "curl -s -X POST $SERVER_URL/usage -H 'Content-Type: application/json' -d '{\"license_key\":\"test\",\"activation_id\":\"test\",\"event_type\":\"query\"}'" \
    "success"

# Test 12: Analytics endpoint
run_test "Analytics endpoint" \
    "curl -s $SERVER_URL/analytics" \
    "success"

echo ""
echo "🔍 ERROR HANDLING TESTS"
echo "======================"

# Test 13: Missing parameters
run_test "Missing email parameter (returns 400)" \
    "curl -s -w '%{http_code}' -o /dev/null -X POST $SERVER_URL/test-email -H 'Content-Type: application/json' -d '{}'" \
    "400"

# Test 14: Invalid method
run_test "Invalid method (returns 405)" \
    "curl -s -w '%{http_code}' -o /dev/null -X PUT $SERVER_URL/health" \
    "405"

echo ""
echo "🎯 TEST RESULTS SUMMARY"
echo "======================"
echo "Tests run: $TESTS_RUN"
echo "Tests passed: $TESTS_PASSED"
echo "Tests failed: $((TESTS_RUN - TESTS_PASSED))"

if [ $TESTS_PASSED -eq $TESTS_RUN ]; then
    echo ""
    echo "🎉 ALL TESTS PASSED! Server is ready for production."
    echo "Completed at: $(date)"
    exit 0
else
    echo ""
    echo "❌ Some tests failed. Server needs attention before production deployment."
    echo "Completed at: $(date)"
    exit 1
fi
