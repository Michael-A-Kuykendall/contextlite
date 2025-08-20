#!/bin/bash
set -e

echo "🧪 Testing npm Package Installation"

# Create a temporary directory for testing
TEST_DIR="/tmp/npm-test-$(date +%s)"
mkdir -p "$TEST_DIR"
cd "$TEST_DIR"

# Test global installation
echo "📥 Installing contextlite via npm..."
npm install -g contextlite || {
    echo "❌ npm install failed"
    exit 1
}

# Test command availability
echo "🔍 Testing command availability..."
which contextlite || {
    echo "❌ contextlite command not found in PATH"
    exit 1
}

# Test version
echo "🔍 Testing version..."
VERSION=$(contextlite --version 2>&1 || echo "FAILED")
echo "Version output: $VERSION"

# Test server functionality
echo "🚀 Testing server functionality..."
PORT=19002
echo "Starting server on port $PORT..."
timeout 15s contextlite --port $PORT &
SERVER_PID=$!
sleep 10

# Test endpoints
echo "🌐 Testing endpoints..."
curl -f "http://localhost:$PORT/health" && echo "✅ Health check passed" || echo "❌ Health check failed"
curl -f "http://localhost:$PORT/api/v1/trial/info" && echo "✅ Trial info passed" || echo "❌ Trial info failed"

# Cleanup
kill $SERVER_PID 2>/dev/null || true
npm uninstall -g contextlite

# Clean up test directory
cd /
rm -rf "$TEST_DIR"

echo "✅ npm package test completed"
