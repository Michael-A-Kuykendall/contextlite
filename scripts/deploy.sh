#!/bin/bash

# ContextLite Smart Deployment Script
# Usage: ./deploy.sh [package] [version]
# Example: ./deploy.sh crates 1.0.43

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

PACKAGE=$1
VERSION=$2

if [ -z "$PACKAGE" ] || [ -z "$VERSION" ]; then
    echo -e "${RED}Usage: $0 [package] [version]${NC}"
    echo -e "${BLUE}Packages: all, crates, docker, npm, pypi${NC}"
    echo -e "${BLUE}Example: $0 crates 1.0.43${NC}"
    exit 1
fi

if [ -z "$GITHUB_TOKEN" ]; then
    echo -e "${RED}Error: GITHUB_TOKEN environment variable not set${NC}"
    echo -e "${YELLOW}Export your GitHub token: export GITHUB_TOKEN=your_token${NC}"
    exit 1
fi

echo -e "${BLUE}🚀 Deploying ContextLite ${PACKAGE} v${VERSION}...${NC}"

if [ "$PACKAGE" = "all" ]; then
    # Deploy all packages using main workflow
    echo -e "${YELLOW}📦 Triggering full deployment...${NC}"
    
    curl -X POST \
        -H "Authorization: token $GITHUB_TOKEN" \
        -H "Accept: application/vnd.github.v3+json" \
        "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/workflows/publish-packages.yml/dispatches" \
        -d "{\"ref\": \"main\", \"inputs\": {\"version\": \"$VERSION\"}}" \
        -w "\nHTTP Status: %{http_code}\n"
        
    echo -e "${GREEN}✅ Full deployment triggered for v${VERSION}${NC}"
    echo -e "${BLUE}Monitor: https://github.com/Michael-A-Kuykendall/contextlite/actions${NC}"
    
else
    # Deploy single package using quick deploy workflow
    echo -e "${YELLOW}📦 Triggering ${PACKAGE} deployment...${NC}"
    
    curl -X POST \
        -H "Authorization: token $GITHUB_TOKEN" \
        -H "Accept: application/vnd.github.v3+json" \
        "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/workflows/quick-deploy.yml/dispatches" \
        -d "{\"ref\": \"main\", \"inputs\": {\"package\": \"$PACKAGE\", \"version\": \"$VERSION\"}}" \
        -w "\nHTTP Status: %{http_code}\n"
        
    echo -e "${GREEN}✅ ${PACKAGE} deployment triggered for v${VERSION}${NC}"
    echo -e "${BLUE}Monitor: https://github.com/Michael-A-Kuykendall/contextlite/actions${NC}"
fi

echo -e "${YELLOW}⏱️  Deployment started, check GitHub Actions for progress${NC}"
