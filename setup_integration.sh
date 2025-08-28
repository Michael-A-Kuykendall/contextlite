#!/bin/bash

# ContextLite Integration Setup Script
# Sets up both VS Code integration and CLI discovery tools

set -e

echo "🚀 Setting up ContextLite Integration"
echo "====================================="

# Build the port management tool
echo "📦 Building port management tool..."
cd cmd/contextlite-port
go build -o ../../bin/contextlite-port .
cd ../..

# Install the port manager globally
echo "🔧 Installing port manager..."
sudo cp bin/contextlite-port /usr/local/bin/ 2>/dev/null || cp bin/contextlite-port ~/bin/ || {
    echo "⚠️ Could not install globally, adding to PATH manually"
    export PATH="$PWD/bin:$PATH"
}

# Make CLI tools executable
echo "🛠️ Setting up CLI tools..."
chmod +x cli-tools/contextlite-cli
sudo ln -sf "$PWD/cli-tools/contextlite-cli" /usr/local/bin/contextlite-cli 2>/dev/null || {
    echo "⚠️ Could not create global symlink, use: $PWD/cli-tools/contextlite-cli"
}

# Install Python dependencies for MCP server
echo "🐍 Installing Python dependencies..."
pip3 install aiohttp requests sqlite3 2>/dev/null || {
    echo "⚠️ Failed to install Python deps. Install manually: pip3 install aiohttp requests"
}

# Build VS Code extension
echo "🆚 Building VS Code extension..."
cd vscode-extension
npm install
npm run compile
cd ..

echo "✅ Setup complete!"
echo ""
echo "🎯 Next Steps:"
echo "1. Install VS Code extension:"
echo "   code --install-extension $PWD/vscode-extension"
echo ""
echo "2. Test port management:"
echo "   contextlite-port assign $PWD"
echo "   contextlite-port list"
echo ""
echo "3. Test CLI discovery:"
echo "   contextlite-cli discover"
echo "   contextlite-cli status"
echo ""
echo "4. Configure MCP for Copilot:"
echo "   Add mcp-server/mcp_settings.json to your VS Code settings"
echo ""
echo "🎉 Ready for per-project ContextLite with intelligent port management!"
