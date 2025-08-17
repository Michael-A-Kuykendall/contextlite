#!/bin/bash

# ContextLite Integration Test Suite
# Comprehensive testing of all client adapters against a real ContextLite server

set -e  # Exit on any error

echo "=================================================="
echo "   ContextLite Integration Test Suite"
echo "=================================================="

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Test configuration
SERVER_URL="http://127.0.0.1:8083"
AUTH_TOKEN="test-token-12345"
TEST_DB="contextlite_integration_test.db"

# Function to print colored output
print_status() {
    echo -e "${BLUE}[$(date +'%H:%M:%S')]${NC} $1"
}

print_success() {
    echo -e "${GREEN}âœ… $1${NC}"
}

print_warning() {
    echo -e "${YELLOW}âš ï¸  $1${NC}"
}

print_error() {
    echo -e "${RED}âŒ $1${NC}"
}

# Function to check if a command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Function to wait for server to be ready
wait_for_server() {
    local url=$1
    local timeout=30
    local count=0
    
    print_status "Waiting for ContextLite server at $url..."
    
    while [ $count -lt $timeout ]; do
        if curl -s -f "$url/health" >/dev/null 2>&1; then
            print_success "Server is ready!"
            return 0
        fi
        sleep 1
        count=$((count + 1))
        printf "."
    done
    
    echo ""
    print_error "Server failed to start within $timeout seconds"
    return 1
}

# Function to run a test and capture results
run_test() {
    local test_name=$1
    local test_command=$2
    local start_time=$(date +%s)
    
    print_status "Running $test_name..."
    
    if eval "$test_command"; then
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        print_success "$test_name completed successfully (${duration}s)"
        return 0
    else
        print_error "$test_name failed"
        return 1
    fi
}

# Function to check prerequisites
check_prerequisites() {
    print_status "Checking prerequisites..."
    
    local missing_deps=()
    
    # Check for Go
    if ! command_exists go; then
        missing_deps+=("Go")
    fi
    
    # Check for Python
    if ! command_exists python3 && ! command_exists python; then
        missing_deps+=("Python")
    fi
    
    # Check for Node.js
    if ! command_exists node; then
        missing_deps+=("Node.js")
    fi
    
    # Check for Rust (optional)
    if ! command_exists cargo; then
        print_warning "Rust/Cargo not found - Rust tests will be skipped"
    fi
    
    if [ ${#missing_deps[@]} -gt 0 ]; then
        print_error "Missing required dependencies: ${missing_deps[*]}"
        print_error "Please install the missing dependencies and try again"
        exit 1
    fi
    
    print_success "All required dependencies are available"
}

# Function to start ContextLite server
start_server() {
    print_status "Starting ContextLite server..."
    
    # Build ContextLite if needed
    if [ ! -f "../../build/contextlite" ]; then
        print_status "Building ContextLite..."
        cd ../..
        make build
        cd test/integration_suite
    fi
    
    # Clean up any existing test database
    rm -f "$TEST_DB"
    
    # Start server in background
    ../../build/contextlite server \
        --port 8083 \
        --database "$TEST_DB" \
        --auth-token "$AUTH_TOKEN" \
        --log-level info \
        > server.log 2>&1 &
    
    SERVER_PID=$!
    echo $SERVER_PID > server.pid
    
    # Wait for server to be ready
    if wait_for_server "$SERVER_URL"; then
        print_success "ContextLite server started (PID: $SERVER_PID)"
        return 0
    else
        print_error "Failed to start ContextLite server"
        if [ -f server.log ]; then
            echo "Server log:"
            tail -n 20 server.log
        fi
        cleanup_server
        exit 1
    fi
}

# Function to cleanup server
cleanup_server() {
    if [ -f server.pid ]; then
        local pid=$(cat server.pid)
        print_status "Stopping ContextLite server (PID: $pid)..."
        
        if kill "$pid" 2>/dev/null; then
            # Wait for graceful shutdown
            sleep 2
            
            # Force kill if still running
            if kill -0 "$pid" 2>/dev/null; then
                kill -9 "$pid" 2>/dev/null
            fi
            
            print_success "Server stopped"
        else
            print_warning "Server was not running"
        fi
        
        rm -f server.pid
    fi
    
    # Clean up test database
    rm -f "$TEST_DB"
    rm -f "${TEST_DB}-shm"
    rm -f "${TEST_DB}-wal"
}

# Function to run all integration tests
run_integration_tests() {
    local total_tests=0
    local passed_tests=0
    local failed_tests=()
    
    print_status "Running integration tests..."
    
    # Go client test
    if [ -f "go_test.go" ]; then
        total_tests=$((total_tests + 1))
        if run_test "Go Client" "go run go_test.go"; then
            passed_tests=$((passed_tests + 1))
        else
            failed_tests+=("Go Client")
        fi
    fi
    
    # Python client test
    if [ -f "python_test.py" ]; then
        total_tests=$((total_tests + 1))
        if run_test "Python Client" "python3 python_test.py || python python_test.py"; then
            passed_tests=$((passed_tests + 1))
        else
            failed_tests+=("Python Client")
        fi
    fi
    
    # Node.js MCP server test
    if [ -f "mcp_test.js" ]; then
        total_tests=$((total_tests + 1))
        if run_test "Node.js MCP Server" "node mcp_test.js"; then
            passed_tests=$((passed_tests + 1))
        else
            failed_tests+=("Node.js MCP Server")
        fi
    fi
    
    # Rust client test (if Rust is available)
    if command_exists cargo && [ -f "rust_test.rs" ]; then
        total_tests=$((total_tests + 1))
        if run_test "Rust Client" "rustc rust_test.rs && ./rust_test"; then
            passed_tests=$((passed_tests + 1))
        else
            failed_tests+=("Rust Client")
        fi
    fi
    
    # Print summary
    echo ""
    echo "=================================================="
    echo "              Test Summary"
    echo "=================================================="
    
    print_status "Total tests: $total_tests"
    print_success "Passed: $passed_tests"
    
    if [ ${#failed_tests[@]} -gt 0 ]; then
        print_error "Failed: ${#failed_tests[@]}"
        for test in "${failed_tests[@]}"; do
            print_error "  - $test"
        done
        echo ""
        print_error "Integration test suite FAILED"
        return 1
    else
        echo ""
        print_success "All integration tests PASSED! í¾‰"
        return 0
    fi
}

# Main execution
main() {
    local start_time=$(date +%s)
    
    # Handle cleanup on exit
    trap cleanup_server EXIT
    
    # Check prerequisites
    check_prerequisites
    
    # Start server
    start_server
    
    # Run tests
    if run_integration_tests; then
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        print_success "Integration test suite completed successfully in ${duration}s"
        exit 0
    else
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        print_error "Integration test suite failed after ${duration}s"
        exit 1
    fi
}

# Check if script is being run directly
if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
    main "$@"
fi
