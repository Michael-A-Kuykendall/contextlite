#!/bin/bash
set -e

echo "🧪 Testing Docker Container"

# Check if Docker is available
if ! command -v docker &> /dev/null; then
    echo "❌ Docker not found - skipping Docker tests"
    echo "   Install Docker Desktop to run these tests"
    exit 0
fi

# Test docker pull
echo "📥 Pulling Docker image..."
docker pull michaelakuykendall/contextlite:latest || {
    echo "❌ Docker pull failed"
    exit 1
}

# Test version
echo "🔍 Testing version..."
VERSION=$(docker run --rm michaelakuykendall/contextlite:latest --version 2>&1 || echo "FAILED")
echo "Version output: $VERSION"

# Test server in container
echo "🚀 Testing containerized server..."
PORT=19004
echo "Starting container on port $PORT..."
docker run -d --name contextlite-test -p $PORT:8080 michaelakuykendall/contextlite:latest
sleep 15

# Test endpoints
echo "🌐 Testing endpoints..."
curl -f "http://localhost:$PORT/health" && echo "✅ Health check passed" || echo "❌ Health check failed"
curl -f "http://localhost:$PORT/api/v1/trial/info" && echo "✅ Trial info passed" || echo "❌ Trial info failed"

# Test logs
echo "📋 Checking logs..."
docker logs contextlite-test | head -20

# Cleanup
docker stop contextlite-test
docker rm contextlite-test

echo "✅ Docker container test completed"
