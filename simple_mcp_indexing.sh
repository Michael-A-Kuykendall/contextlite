#!/bin/bash

# Simple MCP Workspace Indexing Script - API Approach
# Date: August 28, 2025

set -e

CONTEXTLITE_URL="http://localhost:8084"
AUTH_TOKEN="contextlite-dev-token-2025"
WORKSPACE_ROOT="/c/Users/micha/repos/contextlite"

echo "🎯 MCP Workspace Indexing via API"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Check server status
echo "🔍 Checking server status..."
curl -s "$CONTEXTLITE_URL/health" | head -c 200
echo ""

# Use workspace scanning API to index current directory
echo "📁 Scanning workspace directory..."
curl -X POST "$CONTEXTLITE_URL/api/v1/documents/workspace" \
  -H "Authorization: Bearer $AUTH_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "path": "'$WORKSPACE_ROOT'",
    "include_patterns": ["*.go", "*.md", "*.yaml", "*.yml", "*.json", "*.js", "*.ts"],
    "exclude_patterns": ["node_modules", ".git", "build", "dist", "*.log", "*.tmp", "vendor", "*.exe"],
    "max_files": 100
  }' || echo "Workspace scan failed"

echo ""
echo "📊 Checking database statistics..."
curl -s "$CONTEXTLITE_URL/api/v1/storage/stats" \
  -H "Authorization: Bearer $AUTH_TOKEN" || echo "Could not get stats"

echo ""
echo "✅ Basic workspace indexing complete!"
echo ""
echo "🧠 Adding key Claude conversation logs manually..."

# Add a few key Claude conversation excerpts via individual document API
cat > /tmp/claude_excerpt.json << 'EOF'
{
  "id": "claude_coverage_session",
  "path": "claude_logs/coverage_testing_session.md",
  "content": "# Claude Coverage Testing Session\n\nUser request: autonomous Do while loop mission to finish all coverage to 100 percent until complete\n\nKey achievements:\n- Registry: 93.3% → 94.2%\n- Storage: 86.5% → 87.2%\n- Middleware: 84.7% → 91.5%\n- Engine: 97.9% → 98.3%\n\nSurgical testing approach:\n- Target specific uncovered lines\n- Error path testing\n- Function signature analysis",
  "category": "claude_sessions",
  "title": "Claude Coverage Testing Session"
}
EOF

echo "📄 Adding Claude coverage session excerpt..."
curl -X POST "$CONTEXTLITE_URL/api/v1/documents" \
  -H "Authorization: Bearer $AUTH_TOKEN" \
  -H "Content-Type: application/json" \
  -d @/tmp/claude_excerpt.json || echo "Failed to add Claude excerpt"

# Add copilot instructions
cat > /tmp/copilot_excerpt.json << 'EOF'
{
  "id": "copilot_instructions",
  "path": ".github/copilot-instructions.md",
  "content": "# ContextLite AI Coding Agent Instructions\n\nPurpose: Enable an AI agent to be productive immediately in this repo.\n\nCurrent Mission: DEPLOYMENT ECOSYSTEM HARDENING\nStatus: PRODUCTION LIVE → DEPLOYMENT AUDIT & FIXES\n\nArchitecture:\n- Dual-Engine System: CoreEngine + JSONCLIEngine\n- Enhanced Feature Gate: Trial-aware licensing\n- Multi-Platform Releases: Cross-platform builds\n\nDeployment Status:\n- Working: npm, PyPI, GitHub Packages, Chocolatey\n- Failing: build-and-release, Docker, Homebrew, AUR, Crates",
  "category": "documentation",
  "title": "GitHub Copilot Instructions"
}
EOF

echo "📄 Adding Copilot instructions excerpt..."
curl -X POST "$CONTEXTLITE_URL/api/v1/documents" \
  -H "Authorization: Bearer $AUTH_TOKEN" \
  -H "Content-Type: application/json" \
  -d @/tmp/copilot_excerpt.json || echo "Failed to add Copilot instructions"

echo ""
echo "🎯 Final verification..."
curl -s "$CONTEXTLITE_URL/api/v1/storage/stats" \
  -H "Authorization: Bearer $AUTH_TOKEN" | head -c 300

echo ""
echo ""
echo "✅ MCP Indexing Complete!"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "🎯 Ready for MCP testing!"
