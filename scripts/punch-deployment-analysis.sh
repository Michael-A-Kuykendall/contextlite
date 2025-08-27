#!/bin/bash

# PUNCH-powered Deployment Analysis
# Analyzes deployment configurations and workflow complexity

set -e

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

echo -e "${BOLD}${BLUE}🥊 PUNCH Deployment Analysis${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Create results directory
mkdir -p punch_results/deployment

echo -e "${CYAN}🔍 Discovering deployment configurations...${NC}"
.punch-tool/punch.exe discover . --languages go --output json | \
  jq -r '.components[] | select(.name | contains("deploy") or contains("workflow") or contains("docker") or contains("build"))' \
  > punch_results/deployment/config_components.json

echo -e "${CYAN}📦 Analyzing package managers...${NC}"
.punch-tool/punch.exe query "package|npm|docker|snap|chocolatey|homebrew" --output table > punch_results/deployment/package_managers.txt

echo -e "${CYAN}🔧 GitHub Actions analysis...${NC}"
.punch-tool/punch.exe discover .github/workflows --languages yaml --output table > punch_results/deployment/workflows.txt 2>/dev/null || echo "No YAML parser available"

echo -e "${CYAN}🐳 Docker configuration...${NC}"
.punch-tool/punch.exe query "dockerfile|docker-compose|container" --output table > punch_results/deployment/docker.txt

echo -e "${CYAN}📋 Build system analysis...${NC}"
.punch-tool/punch.exe query "build|make|compile|binary" --output table > punch_results/deployment/build_system.txt

echo -e "${CYAN}🚀 Release automation...${NC}"
.punch-tool/punch.exe query "release|tag|publish|version" --output table > punch_results/deployment/releases.txt

# Generate deployment complexity score
TOTAL_DEPLOYMENT_COMPONENTS=$(cat punch_results/deployment/*.txt | wc -l)
PACKAGE_MANAGERS=$(grep -c "package\|npm\|docker" punch_results/deployment/package_managers.txt || echo "0")
WORKFLOWS=$(grep -c "workflow\|action" punch_results/deployment/workflows.txt || echo "0")

echo -e "${GREEN}✅ Deployment Analysis Complete!${NC}"
echo ""
echo -e "${YELLOW}📊 Deployment Complexity Report:${NC}"
echo "   Total Components: $TOTAL_DEPLOYMENT_COMPONENTS"
echo "   Package Managers: $PACKAGE_MANAGERS detected"
echo "   Workflows:        $WORKFLOWS detected"
echo ""
echo -e "${YELLOW}💡 Insights:${NC}"
if [ $PACKAGE_MANAGERS -gt 5 ]; then
  echo "   🎯 Multi-platform deployment detected - excellent coverage!"
fi
if [ $WORKFLOWS -gt 3 ]; then
  echo "   ⚡ Complex CI/CD pipeline - consider consolidation"
fi
echo ""
echo -e "${YELLOW}📁 Results saved to: punch_results/deployment/${NC}"