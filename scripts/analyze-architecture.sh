#!/bin/bash

# PUNCH-powered Architecture Analysis Script
# Analyzes ContextLite codebase and generates comprehensive documentation

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

echo -e "${BOLD}${BLUE}"
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║          🥊 PUNCH-POWERED ARCHITECTURE ANALYSIS             ║"
echo "║                    ContextLite Codebase                     ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo -e "${NC}"

# Create output directory
mkdir -p punch_results

echo -e "${CYAN}🔍 Discovering components...${NC}"
.punch-tool/punch.exe discover . --languages go --verbose --output json > punch_results/components.json

echo -e "${CYAN}📊 Analyzing architecture patterns...${NC}"
.punch-tool/punch.exe query "HTTP handlers" --output table > punch_results/http_handlers.txt

echo -e "${CYAN}📈 Generating statistics...${NC}"  
.punch-tool/punch.exe stats --output json > punch_results/stats.json

echo -e "${CYAN}🔗 Mapping dependencies...${NC}"
.punch-tool/punch.exe list --type=function --output table > punch_results/functions.txt

echo -e "${GREEN}✅ Analysis complete! Results saved to punch_results/${NC}"
echo ""
echo -e "${YELLOW}📋 Generated Files:${NC}"
echo "   • punch_results/components.json     - All discovered components"
echo "   • punch_results/http_handlers.txt   - HTTP handler analysis"
echo "   • punch_results/stats.json          - Codebase statistics" 
echo "   • punch_results/functions.txt       - All discovered functions"
echo ""
echo -e "${YELLOW}🚀 Quick Actions:${NC}"
echo "   View components:  cat punch_results/components.json | jq '.'"
echo "   View stats:       cat punch_results/stats.json"
echo "   View handlers:    cat punch_results/http_handlers.txt"