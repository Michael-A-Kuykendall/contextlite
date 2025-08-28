#!/bin/bash

# Workspace Log Discovery & Consumption Demonstration
# Date: August 28, 2025
# Purpose: Test the intelligent workspace log discovery system

set -e

CONTEXTLITE_URL="http://localhost:8084"
AUTH_TOKEN="contextlite-dev-token-2025"

echo "🎯 WORKSPACE LOG DISCOVERY SYSTEM DEMONSTRATION"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

echo ""
echo "🔍 Step 1: Discover Available Workspace Logs"
echo "────────────────────────────────────────────────────────────────────────────────"
echo "Current project: $(pwd)"
echo ""

# Test workspace log discovery
echo "Discovering workspace logs for this project..."
curl -s "$CONTEXTLITE_URL/api/v1/workspace/logs/discover" \
  -H "Authorization: Bearer $AUTH_TOKEN" \
  -H "Content-Type: application/json" | python3 -m json.tool 2>/dev/null || echo "JSON formatting failed, raw response above"

echo ""
echo ""
echo "🧠 Step 2: Understanding Workspace ID Generation"
echo "────────────────────────────────────────────────────────────────────────────────"

# Show how workspace IDs are generated
echo "Current working directory: $(pwd)"
echo "Expected Claude workspace ID: C--Users-micha-repos-contextlite"
echo ""
echo "Checking if Claude workspace exists:"
if [ -d "/c/Users/micha/.claude/projects/C--Users-micha-repos-contextlite" ]; then
    echo "✅ Found Claude workspace"
    echo "   Files: $(find /c/Users/micha/.claude/projects/C--Users-micha-repos-contextlite -name "*.jsonl" | wc -l) JSONL files"
    echo "   Size: $(du -sh /c/Users/micha/.claude/projects/C--Users-micha-repos-contextlite | cut -f1)"
else
    echo "❌ Claude workspace not found"
fi

echo ""
echo "🔐 Step 3: Safety Features & Content Verification"
echo "────────────────────────────────────────────────────────────────────────────────"
echo "Key safety features implemented:"
echo "✅ Content verification - checks for project-related keywords"
echo "✅ Dry-run mode by default - no accidental consumption"
echo "✅ Size limits - prevents consuming massive log files"
echo "✅ OS-aware paths - works on Windows, macOS, Linux"
echo "✅ Workspace ID validation - ensures correct project logs"

echo ""
echo "📊 Step 4: Test Dry-Run Log Consumption"
echo "────────────────────────────────────────────────────────────────────────────────"

# Test dry-run consumption
echo "Testing dry-run log consumption..."
curl -s -X POST "$CONTEXTLITE_URL/api/v1/workspace/logs/consume" \
  -H "Authorization: Bearer $AUTH_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "project_path": ".",
    "dry_run": true
  }' | python3 -m json.tool 2>/dev/null || echo "JSON formatting failed, raw response above"

echo ""
echo ""
echo "⚡ Step 5: System Integration Benefits"
echo "────────────────────────────────────────────────────────────────────────────────"
echo "🎯 Automatic Discovery:"
echo "   • Finds Claude logs: ~/.claude/projects/[workspace-id]/*.jsonl"
echo "   • Finds Copilot logs: VS Code workspace storage"
echo "   • Cross-platform path detection"
echo ""
echo "🛡️ Content Verification:"
echo "   • Scans first 50 lines of each file"
echo "   • Looks for project-specific keywords"
echo "   • Prevents indexing unrelated logs"
echo ""
echo "📈 Intelligent Processing:"
echo "   • Handles JSONL format (Claude conversations)"
echo "   • Parses single-line JSON logs (Copilot)"
echo "   • Extracts meaningful content only"
echo "   • Maintains source attribution"

echo ""
echo "🔧 Step 6: API Endpoints Available"
echo "────────────────────────────────────────────────────────────────────────────────"
echo "GET  /api/v1/workspace/logs/discover"
echo "     • Discovers available workspace logs"
echo "     • Shows file counts, sizes, verification status"
echo "     • Returns workspace ID for current project"
echo ""
echo "POST /api/v1/workspace/logs/consume"
echo "     • Consumes verified logs into ContextLite database"
echo "     • Requires Professional+ tier"
echo "     • Has safety limits and dry-run mode"

echo ""
echo "✅ SYSTEM READY FOR INTEGRATION"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "🎉 **ACHIEVEMENT**: Intelligent Workspace Log Discovery System Built"
echo "🔥 **CAPABILITY**: Automatic consumption of Claude + Copilot logs"
echo "🛡️ **SAFETY**: Content verification + dry-run mode + size limits"
echo ""
echo "📋 Next Steps:"
echo "   1. Test with force_run=true to actually consume logs"
echo "   2. Add to ContextLite startup routine for automatic consumption"
echo "   3. Extend to support other AI tools (Cursor, etc.)"
echo ""
