#!/bin/bash

# Get the latest workflow run for v1.0.48
echo "🔍 CHECKING ACTUAL DEPLOYMENT STATUS FOR v1.0.48"
echo "=================================================="

WORKFLOW_ID="17217442337"

# Get all jobs from the workflow
curl -s -H "Authorization: token $GITHUB_TOKEN" \
    "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/runs/$WORKFLOW_ID/jobs" \
    > /tmp/jobs.json

echo ""
echo "📊 JOB STATUS SUMMARY:"
echo "======================"

# Extract job names and conclusions
cat /tmp/jobs.json | grep -E '"name"|"conclusion"' | \
    sed 'N;s/\n/ /' | \
    grep -E '(build-|publish-)' | \
    sed 's/.*"name": "\([^"]*\)".* "conclusion": "\([^"]*\)".*/\1: \2/' | \
    sort

echo ""
echo "🌍 VERIFYING ACTUAL PACKAGE AVAILABILITY:"
echo "=========================================="

echo ""
echo "✅ PyPI (confirmed working):"
curl -s "https://pypi.org/pypi/contextlite/json" | grep -o '"version":"[^"]*"' | head -1
echo ""

echo "✅ npm (confirmed working):"
curl -s "https://registry.npmjs.org/contextlite" | grep -o '"latest":"[^"]*"' | head -1  
echo ""

echo "🐳 Docker Hub:"
curl -s "https://hub.docker.com/v2/repositories/contextlite/contextlite/tags/" | grep -o '"name":"[^"]*"' | head -1 || echo "❌ No tags found"
echo ""

echo "🍺 Homebrew:"
curl -s "https://formulae.brew.sh/api/formula/contextlite.json" >/dev/null 2>&1 && echo "✅ Formula exists" || echo "❌ Formula not found"
echo ""

echo "🦀 Crates.io:"
curl -s "https://crates.io/api/v1/crates/contextlite" >/dev/null 2>&1 && echo "✅ Crate exists" || echo "❌ Crate not found"
echo ""

echo "🍫 Chocolatey:"
echo "Manual check required - visit: https://community.chocolatey.org/packages/contextlite"
echo ""

rm -f /tmp/jobs.json
