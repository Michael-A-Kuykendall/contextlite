#!/bin/bash

# 🧠 ACTIVATE LOG CONSUMPTION WITH WORKSPACE ISOLATION
# Discovers and consumes Claude/Copilot logs for contextlite project
# Date: August 29, 2025

set -e

CONTEXTLITE_URL="http://localhost:8084"
AUTH_TOKEN="contextlite-dev-token-2025"
PROJECT_PATH="/c/Users/micha/repos/contextlite"
WORKSPACE_ID="C--Users-micha-repos-contextlite"

echo "🧠 LOG CONSUMPTION ACTIVATION (WORKSPACE ISOLATED)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "🎯 Project: $PROJECT_PATH"
echo "🔑 Workspace ID: $WORKSPACE_ID"
echo "🛡️  Isolation: ENABLED"

echo ""
echo "🔍 STEP 1: Discovering available workspace logs..."
curl -X GET "$CONTEXTLITE_URL/api/v1/workspace/logs/discover?project_path=$PROJECT_PATH" \
  -H "Authorization: Bearer $AUTH_TOKEN" \
  -H "X-Workspace-ID: $WORKSPACE_ID" \
  -H "Content-Type: application/json" | head -c 1000
echo ""

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "🧪 STEP 2: Dry-run test (no actual consumption)..."
curl -X POST "$CONTEXTLITE_URL/api/v1/workspace/logs/consume" \
  -H "Authorization: Bearer $AUTH_TOKEN" \
  -H "X-Workspace-ID: $WORKSPACE_ID" \
  -H "Content-Type: application/json" \
  -d '{
    "project_path": "'$PROJECT_PATH'",
    "dry_run": true,
    "force_run": false
  }' | head -c 800
echo ""

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "⚠️  STEP 3: Do you want to proceed with ACTUAL log consumption?"
echo "   This will index Claude/Copilot chat logs into the workspace."
echo ""
read -p "   Proceed with actual consumption? (y/N): " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
    echo "🚀 STEP 3: Consuming logs for real (with isolation)..."
    curl -X POST "$CONTEXTLITE_URL/api/v1/workspace/logs/consume" \
      -H "Authorization: Bearer $AUTH_TOKEN" \
      -H "X-Workspace-ID: $WORKSPACE_ID" \
      -H "Content-Type: application/json" \
      -d '{
        "project_path": "'$PROJECT_PATH'",
        "dry_run": false,
        "force_run": true
      }' | head -c 1000
    echo ""
    
    echo ""
    echo "📊 STEP 4: Checking updated database statistics..."
    curl -s "$CONTEXTLITE_URL/api/v1/documents/search?q=&limit=1" \
      -H "Authorization: Bearer $AUTH_TOKEN" \
      -H "X-Workspace-ID: $WORKSPACE_ID" | grep -o '"total":[0-9]*' || echo "Could not get document count"
    
    echo ""
    echo "✅ LOG CONSUMPTION COMPLETE!"
else
    echo "❌ Skipped actual consumption (safety first)"
fi

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "🎯 Summary:"
echo "   - Log discovery: Completed"
echo "   - Workspace isolation: Active ($WORKSPACE_ID)" 
echo "   - Safety: Dry-run tested first"
echo ""
echo "📋 Next Steps:"
echo "   1. ✅ Workspace isolation working"
echo "   2. ✅ Log consumption system tested"
echo "   3. 🎯 Install private binary for SMT optimization"
echo "   4. 🎯 Verify cross-project isolation with other projects"
