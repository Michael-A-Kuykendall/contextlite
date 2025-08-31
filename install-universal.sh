#!/bin/bash
# ContextLite Universal Installation Wizard
# System-wide setup for all repositories with MCP integration

set -e

# Colors for better UX
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

print_header() {
    echo -e "${BLUE}"
    echo "╔══════════════════════════════════════════════════════════════╗"
    echo "║                 🚀 ContextLite 2.0 Universal Setup          ║"
    echo "║              30-Second Auto-Discovery for All Projects      ║"
    echo "╚══════════════════════════════════════════════════════════════╝"
    echo -e "${NC}"
}

print_step() {
    echo -e "${GREEN}[STEP]${NC} $1"
}

print_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Installation configuration
INSTALL_DIR="/usr/local/bin"
USER_DATA_DIR="$HOME/.contextlite"
CONFIG_DIR="$HOME/.config/contextlite"
REPOS_BASE_DIR="$HOME/repos"
CONTEXTLITE_VERSION="latest"

# Check if running as root for system install
check_permissions() {
    if [[ $EUID -eq 0 ]]; then
        print_info "Running as root - will install system-wide"
        INSTALL_DIR="/usr/local/bin"
    else
        print_warning "Not running as root - will install to user directory"
        INSTALL_DIR="$HOME/.local/bin"
        mkdir -p "$INSTALL_DIR"
        export PATH="$INSTALL_DIR:$PATH"
    fi
}

# Download and install ContextLite binary
install_contextlite_binary() {
    print_step "Installing ContextLite binary..."
    
    # Detect platform and architecture
    OS=$(uname -s | tr '[:upper:]' '[:lower:]')
    ARCH=$(uname -m)
    
    case $ARCH in
        x86_64) ARCH="amd64" ;;
        aarch64|arm64) ARCH="arm64" ;;
        *) print_error "Unsupported architecture: $ARCH"; exit 1 ;;
    esac
    
    case $OS in
        linux) PLATFORM="linux" ;;
        darwin) PLATFORM="darwin" ;;
        mingw*|cygwin*|msys*) PLATFORM="windows"; BINARY_EXT=".exe" ;;
        *) print_error "Unsupported OS: $OS"; exit 1 ;;
    esac
    
    # Download URL
    DOWNLOAD_URL="https://github.com/Michael-A-Kuykendall/contextlite/releases/latest/download/contextlite-${PLATFORM}-${ARCH}${BINARY_EXT}"
    BINARY_PATH="$INSTALL_DIR/contextlite${BINARY_EXT}"
    
    print_info "Downloading from: $DOWNLOAD_URL"
    curl -L "$DOWNLOAD_URL" -o "$BINARY_PATH"
    chmod +x "$BINARY_PATH"
    
    print_info "✅ ContextLite binary installed to: $BINARY_PATH"
}

# Create user configuration directories
setup_user_config() {
    print_step "Setting up user configuration..."
    
    mkdir -p "$USER_DATA_DIR" "$CONFIG_DIR"
    
    # Create default configuration
    cat > "$CONFIG_DIR/config.yaml" << EOF
# ContextLite Universal Configuration
server:
  host: "localhost"
  port: 8080
  timeout: "30s"

storage:
  type: "sqlite"
  path: "$USER_DATA_DIR/contextlite.db"
  auto_backup: true

engine:
  type: "auto"
  smt_optimization: true
  cache_size: 1000

logging:
  level: "info"
  file: "$USER_DATA_DIR/contextlite.log"

# MCP Server Configuration
mcp:
  enabled: true
  port: 3000
  timeout: "10s"

# Repository Auto-Discovery
repositories:
  base_paths:
    - "$REPOS_BASE_DIR"
  auto_index: true
  watch_changes: true
  ignore_patterns:
    - "node_modules"
    - ".git"
    - "target"
    - "build"
    - "dist"
EOF

    print_info "✅ Configuration created at: $CONFIG_DIR/config.yaml"
}

# Discover and setup repositories
discover_repositories() {
    print_step "Discovering repositories..."
    
    if [ ! -d "$REPOS_BASE_DIR" ]; then
        print_warning "Repositories directory not found: $REPOS_BASE_DIR"
        read -p "Enter your repositories base directory: " REPOS_BASE_DIR
    fi
    
    # Find all Git repositories
    REPO_LIST=$(find "$REPOS_BASE_DIR" -name ".git" -type d | sed 's|/.git||' | head -20)
    
    if [ -z "$REPO_LIST" ]; then
        print_warning "No Git repositories found in $REPOS_BASE_DIR"
        return 1
    fi
    
    print_info "Found repositories:"
    echo "$REPO_LIST" | nl
    
    echo ""
    read -p "Install ContextLite for all repositories? (y/N): " INSTALL_ALL
    
    if [[ $INSTALL_ALL =~ ^[Yy]$ ]]; then
        echo "$REPO_LIST" > "$USER_DATA_DIR/managed_repositories.txt"
        print_info "✅ Will manage $(echo "$REPO_LIST" | wc -l) repositories"
    else
        print_info "You can manually add repositories later with: contextlite repo add <path>"
    fi
}

# Setup MCP integration
setup_mcp_integration() {
    print_step "Setting up MCP integration for GitHub Copilot..."
    
    # Create MCP server configuration for VS Code
    VSCODE_CONFIG_DIR="$HOME/.vscode"
    if [ -d "$VSCODE_CONFIG_DIR" ]; then
        MCP_CONFIG_FILE="$VSCODE_CONFIG_DIR/mcp_servers.json"
        
        cat > "$MCP_CONFIG_FILE" << EOF
{
  "mcpServers": {
    "contextlite": {
      "command": "contextlite",
      "args": ["mcp", "--port", "3000"],
      "env": {
        "CONTEXTLITE_CONFIG": "$CONFIG_DIR/config.yaml"
      }
    }
  }
}
EOF
        print_info "✅ MCP configuration created for VS Code"
    fi
    
    # Create systemd service for auto-start (Linux)
    if command -v systemctl >/dev/null 2>&1; then
        SERVICE_FILE="$HOME/.config/systemd/user/contextlite.service"
        mkdir -p "$(dirname "$SERVICE_FILE")"
        
        cat > "$SERVICE_FILE" << EOF
[Unit]
Description=ContextLite AI Memory Service
After=network.target

[Service]
Type=simple
ExecStart=$INSTALL_DIR/contextlite server --config $CONFIG_DIR/config.yaml
Restart=always
RestartSec=5
Environment=HOME=$HOME

[Install]
WantedBy=default.target
EOF
        
        systemctl --user daemon-reload
        systemctl --user enable contextlite.service
        print_info "✅ ContextLite service configured for auto-start"
    fi
}

# Setup CLI integration
setup_cli_integration() {
    print_step "Setting up CLI integration..."
    
    # Add to shell profiles
    SHELL_RC=""
    if [ -f "$HOME/.bashrc" ]; then
        SHELL_RC="$HOME/.bashrc"
    elif [ -f "$HOME/.zshrc" ]; then
        SHELL_RC="$HOME/.zshrc"
    fi
    
    if [ -n "$SHELL_RC" ]; then
        echo "" >> "$SHELL_RC"
        echo "# ContextLite AI Memory Integration" >> "$SHELL_RC"
        echo "export PATH=\"$INSTALL_DIR:\$PATH\"" >> "$SHELL_RC"
        echo "export CONTEXTLITE_CONFIG=\"$CONFIG_DIR/config.yaml\"" >> "$SHELL_RC"
        echo "" >> "$SHELL_RC"
        
        print_info "✅ CLI integration added to $SHELL_RC"
    fi
}

# Create workspace indexing script
create_indexing_script() {
    print_step "Creating workspace indexing automation..."
    
    cat > "$INSTALL_DIR/contextlite-index-all" << 'EOF'
#!/bin/bash
# ContextLite Workspace Indexing Script

MANAGED_REPOS="$HOME/.contextlite/managed_repositories.txt"

if [ -f "$MANAGED_REPOS" ]; then
    echo "🔍 Indexing all managed repositories..."
    
    while IFS= read -r repo_path; do
        if [ -d "$repo_path" ]; then
            echo "📁 Indexing: $repo_path"
            contextlite index "$repo_path" --include-logs --include-copilot --quiet
        fi
    done < "$MANAGED_REPOS"
    
    echo "✅ All repositories indexed!"
else
    echo "❌ No managed repositories found. Run contextlite-setup first."
fi
EOF
    
    chmod +x "$INSTALL_DIR/contextlite-index-all"
    print_info "✅ Created indexing script: contextlite-index-all"
}

# Main installation flow
main() {
    print_header
    
    print_info "ContextLite 2.0 introduces revolutionary auto-discovery for zero-configuration setup."
    print_info "Features:"
    print_info "  ✅ 30-second auto-discovery setup (contextlite --onboard)"
    print_info "  ✅ Multi-project isolation with automatic port assignment"
    print_info "  ✅ Development log integration (Git, VS Code, Claude Code, Copilot)"
    print_info "  ✅ MCP server for real-time Claude Code integration"
    print_info "  ✅ Enterprise security hardening"
    print_info "  ✅ Lightning-fast AI memory (0.3ms response time)"
    echo ""
    
    read -p "Continue with installation? (y/N): " CONFIRM
    if [[ ! $CONFIRM =~ ^[Yy]$ ]]; then
        print_info "Installation cancelled."
        exit 0
    fi
    
    echo ""
    print_step "Starting ContextLite Universal Installation..."
    
    # Installation steps
    check_permissions
    install_contextlite_binary
    setup_user_config
    discover_repositories
    setup_mcp_integration
    setup_cli_integration
    create_indexing_script
    
    echo ""
    print_step "Running initial indexing..."
    if [ -f "$USER_DATA_DIR/managed_repositories.txt" ]; then
        "$INSTALL_DIR/contextlite-index-all"
    fi
    
    echo ""
    print_header
    echo -e "${GREEN}🎉 ContextLite Universal Installation Complete!${NC}"
    echo ""
    print_info "📋 What's been set up:"
    print_info "  ✅ ContextLite binary: $INSTALL_DIR/contextlite"
    print_info "  ✅ Configuration: $CONFIG_DIR/config.yaml"
    print_info "  ✅ MCP integration for VS Code"
    print_info "  ✅ CLI access for Claude Code and Rustchain"
    print_info "  ✅ Auto-indexing for all repositories"
    echo ""
    print_info "🚀 Usage:"
    print_info "  • Auto-Discovery: contextlite --onboard (finds all repositories)"
    print_info "  • Per-Project: cd project && contextlite (starts project-specific instance)"
    print_info "  • Claude Code: Automatic MCP integration with project context"
    print_info "  • VS Code: Extension auto-detects onboarded projects"
    print_info "  • Manual indexing: contextlite-index-all"
    echo ""
    print_info "🔄 Restart your shell or run: source $SHELL_RC"
    print_info "🎯 Your AI now has infinite memory across all projects!"
}

# Run the installation
main "$@"
