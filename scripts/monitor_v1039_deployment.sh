#!/bin/bash
# Real-time deployment monitoring for ContextLite v1.0.39 test
# Monitor GitHub Actions workflow and package manager status

set -e

REPO="Michael-A-Kuykendall/contextlite"
VERSION="1.0.39"

echo "🚀 ContextLite Deployment Monitor - v$VERSION"
echo "=================================================="
echo "$(date): Starting deployment monitoring..."

# Function to check workflow status
check_workflow() {
    echo ""
    echo "📊 GitHub Actions Status:"
    curl -s -H "Authorization: token $GITHUB_TOKEN" \
        "https://api.github.com/repos/$REPO/actions/runs?per_page=1" | \
        grep -E '"name"|"status"|"conclusion"|"created_at"' | \
        head -6
}

# Function to check package managers
check_packages() {
    echo ""
    echo "📦 Package Manager Status:"
    
    # npm
    echo -n "  npm: "
    if npm view contextlite@$VERSION >/dev/null 2>&1; then
        echo "✅ v$VERSION available"
    else
        echo "❌ v$VERSION not found"
    fi
    
    # PyPI
    echo -n "  PyPI: "
    if curl -f "https://pypi.org/pypi/contextlite/$VERSION/json" >/dev/null 2>&1; then
        echo "✅ v$VERSION available"
    else
        echo "❌ v$VERSION not found"
    fi
    
    # Docker Hub
    echo -n "  Docker: "
    if curl -s "https://hub.docker.com/v2/repositories/makuykendall/contextlite/tags/" | grep -q "\"$VERSION\"" 2>/dev/null; then
        echo "✅ v$VERSION available"
    else
        echo "❌ v$VERSION not found"
    fi
    
    # GitHub Releases
    echo -n "  GitHub: "
    if curl -f "https://api.github.com/repos/$REPO/releases/tags/v$VERSION" >/dev/null 2>&1; then
        echo "✅ v$VERSION available"
    else
        echo "❌ v$VERSION not found"
    fi
}

# Function to check download stats
check_downloads() {
    echo ""
    echo "📈 Download Statistics:"
    
    # npm downloads
    npm_downloads=$(curl -s "https://api.npmjs.org/downloads/point/last-month/contextlite" | grep -o '"downloads":[0-9]*' | cut -d: -f2)
    echo "  npm: $npm_downloads downloads (last month)"
    
    # Docker pulls
    docker_pulls=$(curl -s "https://hub.docker.com/v2/repositories/makuykendall/contextlite/" | grep -o '"pull_count":[0-9]*' | cut -d: -f2)
    echo "  Docker: $docker_pulls pulls (total)"
}

# Main monitoring loop
for i in {1..10}; do
    echo ""
    echo "🔄 Check #$i at $(date)"
    echo "----------------------------------------"
    
    check_workflow
    check_packages
    check_downloads
    
    if [ $i -lt 10 ]; then
        echo ""
        echo "⏳ Waiting 2 minutes for next check..."
        sleep 120
    fi
done

echo ""
echo "✅ Monitoring complete!"
echo "📋 Check DEPLOYMENT_COMPREHENSIVE_ANALYSIS.md for next steps"
