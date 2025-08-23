#!/bin/bash

# ContextLite Deployment Script
# Usage: ./deploy.sh [platform] [version] [force_deploy]

PLATFORM="${1:-chocolatey}"
VERSION="${2:-1.0.47}"
FORCE_DEPLOY="${3:-false}"

if [ -z "$GITHUB_TOKEN" ]; then
    echo "❌ GITHUB_TOKEN environment variable is required"
    echo "Set it with: export GITHUB_TOKEN='your_token_here'"
    exit 1
fi

echo "🚀 Deploying ContextLite"
echo "📦 Platform: $PLATFORM"
echo "🏷️ Version: $VERSION"
echo "💪 Force Deploy: $FORCE_DEPLOY"
echo ""

# Trigger GitHub Actions workflow
RESPONSE=$(curl -s -w "\n%{http_code}" -X POST \
  -H "Accept: application/vnd.github+json" \
  -H "Authorization: token $GITHUB_TOKEN" \
  -H "X-GitHub-Api-Version: 2022-11-28" \
  https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/workflows/publish-packages.yml/dispatches \
  -d "{\"ref\":\"main\",\"inputs\":{\"platforms\":\"$PLATFORM\",\"version\":\"$VERSION\",\"force_deploy\":\"$FORCE_DEPLOY\"}}")

HTTP_CODE=$(echo "$RESPONSE" | tail -n1)
BODY=$(echo "$RESPONSE" | head -n -1)

if [ "$HTTP_CODE" -eq 204 ]; then
    echo "✅ Deployment triggered successfully!"
    echo "🔍 Check status at: https://github.com/Michael-A-Kuykendall/contextlite/actions"
    echo ""
    echo "📊 Monitor with:"
    echo "   curl -s -H 'Authorization: token \$GITHUB_TOKEN' 'https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/runs?per_page=5'"
else
    echo "❌ Deployment failed to trigger (HTTP $HTTP_CODE)"
    echo "Response: $BODY"
    echo "Check your GITHUB_TOKEN and try again"
    exit 1
fi
