#!/bin/bash

# Comprehensive MCP Workspace Indexing Script
# Purpose: Index ALL relevant context sources for complete MCP functionality
# Date: August 28, 2025

set -e

CONTEXTLITE_URL="http://localhost:8084"
WORKSPACE_ROOT="/c/Users/micha/repos/contextlite"
CLAUDE_WORKSPACE="/c/Users/micha/.claude/projects/C--Users-micha-repos-contextlite"
CLAUDE_COMMANDS="/c/Users/micha/.claude/projects/C--Users-micha--claude-commands"

echo "🎯 MCP Comprehensive Indexing Started"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Function to add a document via API
add_document() {
    local path="$1"
    local content="$2"
    local category="$3"
    local title="$4"

    echo "📄 Adding: $title"
    
    # Create document JSON
    local doc_json=$(cat <<EOF
{
    "id": "$(echo "$path" | sha256sum | cut -d' ' -f1)",
    "path": "$path",
    "content": "$content",
    "category": "$category",
    "title": "$title",
    "indexed_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF
)
    
    # Send to ContextLite
    curl -s -X POST "$CONTEXTLITE_URL/api/v1/documents" \
        -H "Content-Type: application/json" \
        -d "$doc_json" || echo "Failed to add document"
}

# Function to process a file
process_file() {
    local file_path="$1"
    local category="$2"
    
    if [[ ! -f "$file_path" ]]; then
        echo "⚠️  File not found: $file_path"
        return
    fi
    
    local relative_path=$(echo "$file_path" | sed "s|$WORKSPACE_ROOT/||")
    local content=$(cat "$file_path" 2>/dev/null || echo "Could not read file")
    local title="$(basename "$file_path")"
    
    add_document "$relative_path" "$content" "$category" "$title"
}

# Function to process Claude JSONL logs
process_claude_logs() {
    local claude_dir="$1"
    local category="$2"
    
    echo "🔍 Processing Claude logs from: $claude_dir"
    
    find "$claude_dir" -name "*.jsonl" | while read -r jsonl_file; do
        if [[ -f "$jsonl_file" ]]; then
            local filename=$(basename "$jsonl_file")
            local file_size=$(stat -c%s "$jsonl_file" 2>/dev/null || echo "0")
            local human_size=$(numfmt --to=iec "$file_size" 2>/dev/null || echo "${file_size}B")
            
            echo "📊 Processing: $filename ($human_size)"
            
            # Read and process JSONL content
            local content=$(head -c 50000 "$jsonl_file" 2>/dev/null || echo "Could not read JSONL file")
            local title="Claude Session: $filename"
            local relative_path="claude_logs/$filename"
            
            add_document "$relative_path" "$content" "$category" "$title"
        fi
    done
}

echo "🚀 Step 1: Current Workspace Code Files"
echo "────────────────────────────────────────────────────────────────────────────────"

# Index current workspace Go files
find "$WORKSPACE_ROOT" -name "*.go" -not -path "*/vendor/*" -not -path "*/.git/*" | head -20 | while read -r go_file; do
    process_file "$go_file" "golang_source"
done

echo ""
echo "📚 Step 2: Documentation & Configuration"
echo "────────────────────────────────────────────────────────────────────────────────"

# Index key documentation files
for doc_file in \
    "$WORKSPACE_ROOT/.github/copilot-instructions.md" \
    "$WORKSPACE_ROOT/CONTEXTLITE_WIKI.md" \
    "$WORKSPACE_ROOT/CRITICAL_TASK_MASTER_LIST.md" \
    "$WORKSPACE_ROOT/DEPLOYMENT_STATUS_AUDIT.md" \
    "$WORKSPACE_ROOT/README.md" \
    "$WORKSPACE_ROOT/configs/default.yaml"
do
    process_file "$doc_file" "documentation"
done

echo ""
echo "🧠 Step 3: Claude Conversation Logs (ContextLite Sessions)"
echo "────────────────────────────────────────────────────────────────────────────────"

process_claude_logs "$CLAUDE_WORKSPACE" "claude_contextlite_sessions"

echo ""
echo "⚡ Step 4: Claude Commands Workspace"
echo "────────────────────────────────────────────────────────────────────────────────"

process_claude_logs "$CLAUDE_COMMANDS" "claude_commands"

echo ""
echo "🔧 Step 5: API & Engine Files"
echo "────────────────────────────────────────────────────────────────────────────────"

# Index critical API and engine files
for api_file in \
    "$WORKSPACE_ROOT/internal/api/server.go" \
    "$WORKSPACE_ROOT/internal/engine/core.go" \
    "$WORKSPACE_ROOT/internal/storage/sqlite.go" \
    "$WORKSPACE_ROOT/adapters/node/mcp-server/package.json" \
    "$WORKSPACE_ROOT/adapters/node/mcp-server/server.js"
do
    process_file "$api_file" "system_core"
done

echo ""
echo "📊 Step 6: Verification & Statistics"
echo "────────────────────────────────────────────────────────────────────────────────"

# Get storage info
echo "📈 Database Statistics:"
curl -s "$CONTEXTLITE_URL/api/v1/storage/stats" || echo "Could not get stats"

echo ""
echo "✅ MCP Indexing Complete!"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "🎯 Next Steps:"
echo "   1. Test MCP search: Use mcp_contextlite_search_documents"
echo "   2. Test context assembly: Use mcp_contextlite_assemble_context"
echo "   3. Verify VS Code Copilot integration"
echo ""
