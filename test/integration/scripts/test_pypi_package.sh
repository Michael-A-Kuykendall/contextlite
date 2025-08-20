#!/bin/bash
set -e

echo "🧪 Testing PyPI Package Installation"

# Create virtual environment in temp directory
echo "🏗️ Creating virtual environment..."
VENV_DIR="/tmp/contextlite-pypi-test-$(date +%s)"
python -m venv "$VENV_DIR"

# Activate virtual environment (Windows-compatible)
if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "cygwin" ]]; then
    source "$VENV_DIR/Scripts/activate"
else
    source "$VENV_DIR/bin/activate"
fi

# Install package
echo "📥 Installing contextlite via pip..."
pip install contextlite || {
    echo "❌ pip install failed"
    deactivate
    rm -rf "$VENV_DIR"
    exit 1
}

# Test command availability
echo "🔍 Testing command availability..."
which contextlite || {
    echo "❌ contextlite command not found"
    deactivate
    rm -rf "$VENV_DIR"
    exit 1
}

# Test version
echo "🔍 Testing version..."
VERSION=$(contextlite --version 2>&1 || echo "FAILED")
echo "Version output: $VERSION"

# Test Python import
echo "🐍 Testing Python import..."
python -c "import contextlite; print('Python import successful')" || {
    echo "❌ Python import failed"
}

# Test server functionality
echo "🚀 Testing server functionality..."
PORT=19003
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
deactivate
rm -rf "$VENV_DIR"

echo "✅ PyPI package test completed"
