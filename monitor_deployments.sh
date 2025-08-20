#!/bin/bash

echo "🔍 ContextLite Deployment Health Monitor"
echo "======================================="
echo "Date: $(date)"
echo ""

# Track overall health
TOTAL_CHECKS=0
PASSED_CHECKS=0
FAILED_CHECKS=0

# Function to check an endpoint
check_endpoint() {
    local name="$1"
    local url="$2"
    local expected_code="${3:-200}"
    
    ((TOTAL_CHECKS++))
    echo -n "🌐 Checking $name... "
    
    RESPONSE_CODE=$(curl -s -o /dev/null -w "%{http_code}" "$url" 2>/dev/null || echo "000")
    
    if [ "$RESPONSE_CODE" = "$expected_code" ]; then
        echo "✅ (HTTP $RESPONSE_CODE)"
        ((PASSED_CHECKS++))
    else
        echo "❌ (HTTP $RESPONSE_CODE)"
        ((FAILED_CHECKS++))
        echo "   URL: $url"
    fi
}

# Check all critical endpoints
echo "📦 Package Registry Endpoints:"
check_endpoint "npm Registry" "https://registry.npmjs.org/contextlite"
check_endpoint "PyPI Project" "https://pypi.org/project/contextlite/"
check_endpoint "Docker Hub" "https://hub.docker.com/r/michaelakuykendall/contextlite"

echo ""
echo "🌐 Web Interfaces:"
check_endpoint "Hugging Face Space" "https://huggingface.co/spaces/MikeKuykendall/contextlite-download"
check_endpoint "Gradio App" "https://mikekuykendall-contextlite-download.hf.space/"

echo ""
echo "📋 GitHub Integration:"
check_endpoint "Latest Release API" "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases/latest"
check_endpoint "Repository" "https://github.com/Michael-A-Kuykendall/contextlite"

echo ""
echo "🎯 Results Summary:"
echo "=================="
echo "Total checks: $TOTAL_CHECKS"
echo "✅ Passed: $PASSED_CHECKS"
echo "❌ Failed: $FAILED_CHECKS"

if [ $FAILED_CHECKS -eq 0 ]; then
    echo ""
    echo "🎉 ALL ENDPOINTS HEALTHY!"
    echo "All deployment channels are accessible."
else
    echo ""
    echo "⚠️  ISSUES DETECTED!"
    echo "Some endpoints are not responding correctly."
    echo "Consider running full integration tests: ./test_all_deployments.sh"
fi

# Check GitHub releases specifically
echo ""
echo "📦 Latest Release Information:"
LATEST_RELEASE=$(curl -s "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases/latest" 2>/dev/null | grep '"tag_name"' | cut -d'"' -f4)
if [ -n "$LATEST_RELEASE" ]; then
    echo "Latest version: $LATEST_RELEASE"
    
    # Check if binaries are available
    ASSET_COUNT=$(curl -s "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases/latest" 2>/dev/null | grep -c '"browser_download_url"' || echo "0")
    echo "Available assets: $ASSET_COUNT"
    
    if [ "$ASSET_COUNT" -gt 0 ]; then
        echo "✅ Release assets are available"
    else
        echo "❌ No release assets found"
    fi
else
    echo "❌ Could not fetch latest release information"
fi

echo ""
echo "🔍 Health check completed at $(date)"
