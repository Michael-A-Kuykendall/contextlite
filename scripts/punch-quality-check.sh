#!/bin/bash

# PUNCH Quality Analysis Integration
# Runs comprehensive code quality analysis using PUNCH discovery

set -e

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

echo -e "${BOLD}${BLUE}🥊 PUNCH Quality Analysis${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Create results directory
mkdir -p punch_results/quality

echo -e "${CYAN}🔍 Discovering all components...${NC}"
COMPONENT_COUNT=$(.punch-tool/punch.exe discover . --languages go --output json | jq '.components | length')

echo -e "${CYAN}📊 Analyzing function complexity...${NC}"
.punch-tool/punch.exe list --type=function --output table > punch_results/quality/functions.txt

echo -e "${CYAN}🔗 Checking dependency complexity...${NC}"
.punch-tool/punch.exe list --type=struct --output table > punch_results/quality/structs.txt

echo -e "${CYAN}⚡ Performance hotspot detection...${NC}"
.punch-tool/punch.exe query "benchmark|performance|optimize" --output table > punch_results/quality/performance.txt

echo -e "${CYAN}🛡️ Security pattern analysis...${NC}"
.punch-tool/punch.exe query "auth|security|crypto|license" --output table > punch_results/quality/security.txt

echo -e "${CYAN}🧪 Test coverage analysis...${NC}"
.punch-tool/punch.exe query "Test*|*_test.go" --output table > punch_results/quality/tests.txt

# Generate summary
echo -e "${GREEN}✅ Quality Analysis Complete!${NC}"
echo ""
echo -e "${YELLOW}📋 Quality Report Summary:${NC}"
echo "   Total Components: $COMPONENT_COUNT"
echo "   Functions:        $(wc -l < punch_results/quality/functions.txt) analyzed"
echo "   Structs:          $(wc -l < punch_results/quality/structs.txt) analyzed"
echo "   Performance:      $(wc -l < punch_results/quality/performance.txt) hotspots"
echo "   Security:         $(wc -l < punch_results/quality/security.txt) patterns"
echo "   Tests:            $(wc -l < punch_results/quality/tests.txt) test files"
echo ""
echo -e "${YELLOW}📁 Results saved to: punch_results/quality/${NC}"