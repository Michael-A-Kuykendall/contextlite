#!/bin/bash
set -e

echo "🧪 Testing Direct Binary Installation (Windows)"
TEST_DIR="/tmp/contextlite-integration-test-$(date +%s)"
mkdir -p "$TEST_DIR"
cd "$TEST_DIR"

# Download latest release
echo "📥 Downloading latest Windows release..."
# Since the latest is a prerelease, we need to get the specific version
RELEASE_URL="https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v1.0.4/contextlite-1.0.4-windows-amd64.zip"
curl -L -o contextlite.zip "$RELEASE_URL"

# Extract and verify
echo "📦 Extracting..."
unzip -q contextlite.zip
chmod +x contextlite-windows-amd64.exe 2>/dev/null || true

# Create a config file for testing (copy from repository default but use test port)
mkdir -p configs
cat > configs/test.yaml << 'EOF'
server:
  port: 19001
  host: "127.0.0.1"
  cors_enabled: false
  auth_token: "test-token"
  rate_limiting:
    enabled: true
    requests_per_minute: 60
    burst: 10
  
storage:
  database_path: "./test.db"
  cache_size_mb: 64
  
optimization:
  solver_timeout_ms: 250
  max_opt_gap: 0.05
  max_candidates: 200
  max_pairs_per_doc: 5
  integer_scaling: 10000
  objective_style: "weighted-sum"
  
weights:
  relevance: 0.30
  recency: 0.20
  entanglement: 0.15
  prior: 0.15
  authority: 0.10
  specificity: 0.05
  uncertainty: 0.05
  redundancy_penalty: 0.3
  coherence_bonus: 0.2
  weight_update_rate: 0.01
  weight_caps: [0.01, 0.5]

lexicographic:
  compute_at_runtime: true
  
epsilon_budget:
  max_redundancy: 0.4
  min_coherence: 0.3
  min_recency: 0.2
  
tokenizer:
  model_id: "gpt-4"
  max_tokens_default: 4000
  
cache:
  l1_size: 1000
  l2_ttl_minutes: 30
  l3_enabled: true
  
logging:
  level: "info"
  include_timings: true
  include_optimization_metrics: true
EOF

# Test version
echo "🔍 Testing version..."
VERSION=$(./contextlite-windows-amd64.exe -version 2>&1 || echo "FAILED")
echo "Version output: $VERSION"

# Test server startup
echo "🚀 Testing server startup..."
PORT=19001
echo "Starting server on port $PORT..."
timeout 15s ./contextlite-windows-amd64.exe -config configs/test.yaml &
SERVER_PID=$!
sleep 10

# Test endpoints
echo "🌐 Testing endpoints..."
curl -f "http://localhost:$PORT/health" && echo "✅ Health check passed" || echo "❌ Health check failed"
curl -f "http://localhost:$PORT/api/v1/trial/info" && echo "✅ Trial info passed" || echo "❌ Trial info failed"
curl -f "http://localhost:$PORT/license/status" && echo "✅ License status passed" || echo "❌ License status failed"

# Cleanup
kill $SERVER_PID 2>/dev/null || true
cd /
rm -rf "$TEST_DIR"

echo "✅ Direct binary test completed"
