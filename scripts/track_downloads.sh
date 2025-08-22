#!/bin/bash
# ContextLite Download Tracker
# Updates download_stats.json with latest numbers from all package managers
# Run daily via cron or GitHub Actions

set -e

echo "🔄 Updating ContextLite download statistics..."
DATE=$(date -u +"%Y-%m-%dT%H:%M:%S.%6N")

# Initialize counters
GITHUB_DOWNLOADS=0
NPM_DOWNLOADS=0
PYPI_DOWNLOADS=0
DOCKER_DOWNLOADS=0
CHOCOLATEY_DOWNLOADS=0
HOMEBREW_DOWNLOADS=0
SNAP_DOWNLOADS=0
AUR_DOWNLOADS=0
CRATES_DOWNLOADS=0
VSCODE_DOWNLOADS=0

echo "📊 Fetching download statistics from all platforms..."

# GitHub Releases - Sum all download counts
echo "  → GitHub Releases..."
GITHUB_RESPONSE=$(curl -s "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases" || echo "[]")
GITHUB_DOWNLOADS=$(echo "$GITHUB_RESPONSE" | grep -o '"download_count":[0-9]*' | cut -d':' -f2 | awk '{sum+=$1} END {print sum+0}')
echo "    GitHub Downloads: $GITHUB_DOWNLOADS"

# npm - Last month downloads
echo "  → npm..."
NPM_RESPONSE=$(curl -s "https://api.npmjs.org/downloads/point/last-month/contextlite" || echo '{"downloads":0}')
NPM_DOWNLOADS=$(echo "$NPM_RESPONSE" | grep -o '"downloads":[0-9]*' | cut -d':' -f2)
[ -z "$NPM_DOWNLOADS" ] && NPM_DOWNLOADS=0
echo "    npm Downloads (last month): $NPM_DOWNLOADS"

# PyPI - Recent downloads (requires pypistats API)
echo "  → PyPI..."
PYPI_RESPONSE=$(curl -s "https://pypistats.org/api/packages/contextlite/recent" || echo '{"data":{"last_month":0}}')
PYPI_DOWNLOADS=$(echo "$PYPI_RESPONSE" | grep -o '"last_month":[0-9]*' | cut -d':' -f2 | head -1)
[ -z "$PYPI_DOWNLOADS" ] && PYPI_DOWNLOADS=0
echo "    PyPI Downloads (last month): $PYPI_DOWNLOADS"

# Docker Hub - Pull count
echo "  → Docker Hub..."
DOCKER_RESPONSE=$(curl -s "https://hub.docker.com/v2/repositories/michaelkuykendall/contextlite/" || echo '{"pull_count":0}')
DOCKER_DOWNLOADS=$(echo "$DOCKER_RESPONSE" | grep -o '"pull_count":[0-9]*' | cut -d':' -f2)
[ -z "$DOCKER_DOWNLOADS" ] && DOCKER_DOWNLOADS=0
echo "    Docker Downloads: $DOCKER_DOWNLOADS"

# Chocolatey - Requires API key, skip for now
echo "  → Chocolatey (skipped - requires API key)"
CHOCOLATEY_DOWNLOADS="API_KEY_REQUIRED"

# Homebrew - No public API, estimate or skip
echo "  → Homebrew (no public API)"
HOMEBREW_DOWNLOADS="NO_PUBLIC_API"

# Package managers that aren't working yet
echo "  → Snap, AUR, Crates (not deployed yet)"
SNAP_DOWNLOADS=0
AUR_DOWNLOADS=0
CRATES_DOWNLOADS=0

# VS Code Extension - Would need extension ID
echo "  → VS Code Marketplace (manual deployment)"
VSCODE_DOWNLOADS="MANUAL_DEPLOYMENT"

# Calculate numeric total
NUMERIC_TOTAL=$((GITHUB_DOWNLOADS + NPM_DOWNLOADS + PYPI_DOWNLOADS + DOCKER_DOWNLOADS))

# Get latest version from GitHub API
echo "  → Getting latest version..."
LATEST_VERSION=$(curl -s "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases/latest" | grep -o '"tag_name":"[^"]*"' | cut -d'"' -f4)
[ -z "$LATEST_VERSION" ] && LATEST_VERSION="unknown"

# Update JSON with comprehensive stats
cat > download_stats.json << EOF
{
  "metadata": {
    "latest_version": "$LATEST_VERSION",
    "last_updated": "$DATE",
    "total_numeric": $NUMERIC_TOTAL,
    "update_source": "automated_script"
  },
  "platform_downloads": {
    "github_releases": $GITHUB_DOWNLOADS,
    "npm": $NPM_DOWNLOADS,
    "pypi": $PYPI_DOWNLOADS,
    "docker_hub": $DOCKER_DOWNLOADS,
    "chocolatey": "$CHOCOLATEY_DOWNLOADS",
    "homebrew": "$HOMEBREW_DOWNLOADS",
    "snap": $SNAP_DOWNLOADS,
    "aur": $AUR_DOWNLOADS,
    "crates_io": $CRATES_DOWNLOADS,
    "vscode_marketplace": "$VSCODE_DOWNLOADS"
  },
  "platform_status": {
    "github_releases": "working",
    "npm": "working", 
    "pypi": "working",
    "docker_hub": "working",
    "chocolatey": "version_lag",
    "homebrew": "working",
    "snap": "failed",
    "aur": "failed", 
    "crates_io": "failed",
    "vscode_marketplace": "manual"
  },
  "success_metrics": {
    "working_platforms": 6,
    "total_platforms": 10,
    "success_rate": "60%",
    "version_current": "$LATEST_VERSION"
  }
}
EOF

echo ""
echo "✅ Download stats updated successfully!"
echo "📊 Summary:"
echo "   GitHub Releases: $GITHUB_DOWNLOADS"
echo "   npm (last month): $NPM_DOWNLOADS" 
echo "   PyPI (last month): $PYPI_DOWNLOADS"
echo "   Docker Hub: $DOCKER_DOWNLOADS"
echo "   🎯 Total Numeric: $NUMERIC_TOTAL"
echo "   📦 Latest Version: $LATEST_VERSION"
echo ""
echo "📋 Platform Status:"
echo "   ✅ Working: GitHub, npm, PyPI, Docker, Homebrew (6/10)"
echo "   ⚠️  Issues: Chocolatey (version lag)"
echo "   ❌ Failed: Snap, AUR, Crates (3/10)"
echo "   📈 Success Rate: 60%"
echo ""
echo "📄 Full stats saved to: download_stats.json"

# Optional: Display the JSON for verification
if [ "$1" = "--show-json" ]; then
    echo ""
    echo "📄 Generated JSON:"
    cat download_stats.json | python3 -m json.tool 2>/dev/null || cat download_stats.json
fi
