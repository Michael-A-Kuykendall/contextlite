#!/bin/bash

# Quick test script to verify Z3 integration and API fields
cd /c/Users/micha/repos/contextlite

echo "Starting server in background..."
timeout 30s go run ./cmd/contextlite/main.go &
SERVER_PID=$!

# Wait for server to start
sleep 3

echo "Testing context assembly with SMT..."
RESPONSE=$(curl -s -X POST http://localhost:8080/api/v1/context/assemble \
  -H "Content-Type: application/json" \
  -H "Authorization: Bearer contextlite-dev-token-2025" \
  -d '{"query": "authentication systems", "max_documents": 3, "use_smt": true}')

echo "Full Response:"
echo "$RESPONSE" | head -c 2000

echo -e "\n\nExtracting SMT Metrics:"
echo "$RESPONSE" | grep -o '"smt_metrics":{[^}]*}' || echo "SMT metrics not found"

echo -e "\n\nChecking for required fields:"
echo "$RESPONSE" | grep -o '"solver_used":"[^"]*"' || echo "solver_used not found"
echo "$RESPONSE" | grep -o '"z3_status":"[^"]*"' || echo "z3_status not found" 
echo "$RESPONSE" | grep -o '"objective":[0-9]*' || echo "objective not found"

# Clean up
kill $SERVER_PID 2>/dev/null || true

echo -e "\n\n=== VERIFICATION COMPLETE ==="
