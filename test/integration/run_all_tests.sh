#!/bin/bash
set -e

echo "🧪 ContextLite Integration Test Suite"
echo "======================================="
echo "Date: $(date)"
echo "Testing all deployment channels..."
echo ""

# Get the script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
RESULTS_DIR="$REPO_ROOT/test/integration/results/$(date +%Y%m%d-%H%M%S)"

# Create results directory
mkdir -p "$RESULTS_DIR"

echo "📁 Results will be saved to: $RESULTS_DIR"
echo ""

# Test each channel
TESTS=(
    "test_direct_binary.sh"
    "test_npm_package.sh" 
    "test_pypi_package.sh"
    "test_docker_container.sh"
    "test_hugging_face.sh"
)

PASSED=0
FAILED=0
FAILED_TESTS=()

for test in "${TESTS[@]}"; do
    echo "🔄 Running $test..."
    if bash "$SCRIPT_DIR/$test" > "$RESULTS_DIR/$test.log" 2>&1; then
        echo "✅ $test PASSED"
        ((PASSED++))
    else
        echo "❌ $test FAILED"
        ((FAILED++))
        FAILED_TESTS+=("$test")
        echo "   Check log: $RESULTS_DIR/$test.log"
        
        # Show last few lines of the failure log
        echo "   Last few lines of error:"
        tail -5 "$RESULTS_DIR/$test.log" | sed 's/^/     /'
    fi
    echo ""
done

echo "📊 RESULTS SUMMARY"
echo "=================="
echo "✅ Passed: $PASSED"
echo "❌ Failed: $FAILED"
echo "📁 Logs: $RESULTS_DIR"

if [ $FAILED -gt 0 ]; then
    echo ""
    echo "⚠️  Failed tests:"
    for failed_test in "${FAILED_TESTS[@]}"; do
        echo "   - $failed_test"
    done
fi

echo ""
if [ $FAILED -eq 0 ]; then
    echo "🎉 ALL TESTS PASSED!"
    echo "🚀 All deployment channels are working correctly!"
    exit 0
else
    echo "⚠️  SOME TESTS FAILED - REVIEW REQUIRED"
    echo "📋 Check the logs above and fix issues before proceeding"
    exit 1
fi
