#!/bin/bash

echo "🚀 ContextLite Integration Test Launcher"
echo "========================================"
echo ""
echo "This will test all deployed packages to ensure they work correctly."
echo "Tests include: Direct binary, npm, PyPI, Docker, and Hugging Face"
echo ""

# Check if we're in the right directory
if [ ! -f "go.mod" ] || [ ! -d "test/integration" ]; then
    echo "❌ Please run this from the ContextLite repository root"
    exit 1
fi

echo "Ready to test? This will:"
echo "  1. Download and test the latest GitHub release"
echo "  2. Install and test the npm package"
echo "  3. Install and test the PyPI package"
echo "  4. Test the Docker container (if Docker is available)"
echo "  5. Verify the Hugging Face deployment"
echo ""

read -p "Continue? (y/N): " -n 1 -r
echo ""

if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "Test cancelled."
    exit 0
fi

echo ""
echo "🧪 Starting integration tests..."
echo ""

# Run the master test suite
./test/integration/run_all_tests.sh

echo ""
echo "Integration testing completed!"
echo "Check the results above and any log files generated."
