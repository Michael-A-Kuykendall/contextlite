#!/bin/bash

# ContextLite Deployment Diagnostics Script
# This script checks all deployment prerequisites and identifies missing components

echo "🔍 ContextLite Deployment Diagnostics"
echo "====================================="
echo

# Check basic prerequisites
echo "📁 Checking package wrapper directories..."
for dir in npm-wrapper python-wrapper chocolatey vscode-extension homebrew snap; do
    if [ -d "$dir" ]; then
        echo "✅ $dir - Found"
    else
        echo "❌ $dir - Missing"
    fi
done
echo

# Check if release binaries exist
echo "🏗️ Checking build artifacts..."
if [ -d "build" ]; then
    ls -la build/ | head -10
else
    echo "❌ build/ directory missing"
fi
echo

# Check Go module
echo "📦 Checking Go module..."
if [ -f "go.mod" ]; then
    echo "✅ go.mod found"
    echo "Module: $(grep '^module' go.mod)"
else
    echo "❌ go.mod missing"
fi
echo

# Check package.json files
echo "📋 Checking npm wrapper..."
if [ -f "npm-wrapper/package.json" ]; then
    echo "✅ npm-wrapper/package.json found"
    echo "Name: $(grep '"name"' npm-wrapper/package.json)"
    echo "Version: $(grep '"version"' npm-wrapper/package.json)"
else
    echo "❌ npm-wrapper/package.json missing"
fi
echo

# Check Python setup
echo "🐍 Checking Python wrapper..."
if [ -f "python-wrapper/pyproject.toml" ]; then
    echo "✅ python-wrapper/pyproject.toml found"
    echo "Name: $(grep '^name' python-wrapper/pyproject.toml)"
    echo "Version: $(grep '^version' python-wrapper/pyproject.toml)"
else
    echo "❌ python-wrapper/pyproject.toml missing"
fi
echo

# Check VS Code extension
echo "🆚 Checking VS Code extension..."
if [ -f "vscode-extension/package.json" ]; then
    echo "✅ vscode-extension/package.json found"
    echo "Name: $(grep '"name"' vscode-extension/package.json)"
    echo "Version: $(grep '"version"' vscode-extension/package.json)"
else
    echo "❌ vscode-extension/package.json missing"
fi
echo

# Check Chocolatey
echo "🍫 Checking Chocolatey package..."
if [ -f "chocolatey/contextlite.nuspec" ]; then
    echo "✅ chocolatey/contextlite.nuspec found"
    echo "ID: $(grep '<id>' chocolatey/contextlite.nuspec)"
    echo "Version: $(grep '<version>' chocolatey/contextlite.nuspec)"
else
    echo "❌ chocolatey/contextlite.nuspec missing"
fi
echo

# Test basic Go build
echo "🔨 Testing Go build..."
if go version >/dev/null 2>&1; then
    echo "✅ Go is available: $(go version)"
    if go build -o test-build ./cmd/contextlite/main.go 2>/dev/null; then
        echo "✅ Go build successful"
        rm -f test-build
    else
        echo "❌ Go build failed"
        go build -o test-build ./cmd/contextlite/main.go
    fi
else
    echo "❌ Go not available"
fi
echo

# Check if GitHub Actions workflow files are valid
echo "⚙️ Checking GitHub Actions workflows..."
for workflow in .github/workflows/*.yml; do
    if [ -f "$workflow" ]; then
        echo "✅ $(basename "$workflow") found"
    fi
done
echo

# Check for secrets that would be needed
echo "🔐 Required secrets checklist:"
echo "📝 For deployments, these secrets should be configured in GitHub:"
echo "   - NPM_TOKEN (for npm publishing)"
echo "   - PYPI_TOKEN (for PyPI publishing)"
echo "   - VSCODE_MARKETPLACE_TOKEN (for VS Code extension)"
echo "   - CHOCOLATEY_API_KEY (for Chocolatey)"
echo "   - SNAPCRAFT_STORE_CREDENTIALS (for Snap packages)"
echo "   - AUR_SSH_KEY (for Arch User Repository)"
echo

echo "🎯 Summary:"
echo "- Check the GitHub Actions runs for specific error messages"
echo "- Ensure all required secrets are configured in repository settings"
echo "- Verify package wrapper files are correctly configured"
echo "- Test individual package builds locally before pushing"
echo

echo "🔗 Quick links:"
echo "- Repository secrets: https://github.com/Michael-A-Kuykendall/contextlite/settings/secrets/actions"
echo "- Actions runs: https://github.com/Michael-A-Kuykendall/contextlite/actions"
echo "- PyPI project: https://pypi.org/project/contextlite/"
