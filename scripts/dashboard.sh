#!/bin/bash

# ContextLite Download Dashboard
# Shows current download statistics in a dashboard format

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

clear

echo -e "${BOLD}${BLUE}"
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║                   📊 CONTEXTLITE DOWNLOADS                  ║"
echo "║                      Distribution Analytics                  ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo -e "${NC}"

# Check if stats file exists
if [ ! -f "download_stats.json" ]; then
    echo -e "${YELLOW}⚠️  No statistics file found. Running tracker first...${NC}"
    echo ""
    ./scripts/download_tracker.sh
    echo ""
fi

echo -e "${BOLD}${CYAN}📈 DOWNLOAD SUMMARY${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Function to format numbers with commas
format_number() {
    local num=$1
    if [ "$num" = "null" ] || [ -z "$num" ]; then
        echo "N/A"
    else
        echo "$num" | sed ':a;s/\B[0-9]\{3\}\>/,&/;ta'
    fi
}

# Function to show status with icons
show_status() {
    local downloads=$1
    local platform=$2
    
    if [ "$downloads" = "null" ] || [ -z "$downloads" ]; then
        echo -e "   ${RED}❌ Not Available${NC}"
    elif [ "$downloads" = "0" ]; then
        echo -e "   ${YELLOW}📭 No Downloads${NC}"
    else
        local formatted=$(format_number "$downloads")
        echo -e "   ${GREEN}📈 $formatted downloads${NC}"
    fi
}

# Read current stats
if [ -f "download_stats.json" ]; then
    TIMESTAMP=$(grep '"timestamp"' download_stats.json | grep -o '[0-9T:Z-]*')
    TOTAL=$(grep '"total_downloads":' download_stats.json | tail -1 | grep -o '[0-9]*')
    
    echo -e "${BOLD}Last Updated:${NC} $TIMESTAMP"
    echo -e "${BOLD}Total Downloads:${NC} ${GREEN}$(format_number "$TOTAL")${NC}"
    echo ""
    
    echo -e "${BOLD}${YELLOW}🏆 TOP PERFORMING CHANNELS${NC}"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    
    # Extract and sort by downloads
    NPM_DL=$(grep -A3 '"npm"' download_stats.json | grep '"downloads":' | grep -o '[0-9]*' | head -1)
    DOCKER_DL=$(grep -A3 '"docker"' download_stats.json | grep '"downloads":' | grep -o '[0-9]*' | head -1)
    CRATES_DL=$(grep -A3 '"crates"' download_stats.json | grep '"downloads":' | grep -o '[0-9]*' | head -1)
    GITHUB_DL=$(grep -A3 '"github"' download_stats.json | grep '"downloads":' | grep -o '[0-9]*' | head -1)
    
    echo -e "${BOLD}NPM Package${NC}"
    show_status "$NPM_DL" "npm"
    echo ""
    
    echo -e "${BOLD}Docker Hub${NC}"
    show_status "$DOCKER_DL" "docker"
    echo ""
    
    echo -e "${BOLD}Crates.io (Rust)${NC}"
    show_status "$CRATES_DL" "crates"
    echo ""
    
    echo -e "${BOLD}GitHub Releases${NC}"
    show_status "$GITHUB_DL" "github"
    echo ""
    
    echo -e "${BOLD}${YELLOW}📦 PACKAGE MANAGER STATUS${NC}"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    
    # Check deployment status
    PYPI_STATUS=$(grep -A3 '"pypi"' download_stats.json | grep '"status":' | grep -o '"[^"]*"' | tr -d '"')
    HOMEBREW_STATUS=$(grep -A3 '"homebrew"' download_stats.json | grep '"status":' | grep -o '"[^"]*"' | tr -d '"')
    SNAP_STATUS=$(grep -A3 '"snap"' download_stats.json | grep '"status":' | grep -o '"[^"]*"' | tr -d '"')
    AUR_STATUS=$(grep -A3 '"aur"' download_stats.json | grep '"status":' | grep -o '"[^"]*"' | tr -d '"')
    VSCODE_STATUS=$(grep -A3 '"vscode"' download_stats.json | grep '"status":' | grep -o '"[^"]*"' | tr -d '"')
    CHOCO_STATUS=$(grep -A3 '"chocolatey"' download_stats.json | grep '"status":' | grep -o '"[^"]*"' | tr -d '"')
    
    echo -e "PyPI:         $(if [ "$PYPI_STATUS" = "success" ]; then echo -e "${GREEN}✅ Published${NC}"; else echo -e "${RED}❌ Not Published${NC}"; fi)"
    echo -e "Homebrew:     $(if [ "$HOMEBREW_STATUS" = "success" ]; then echo -e "${GREEN}✅ Published${NC}"; else echo -e "${YELLOW}⏳ Pending${NC}"; fi)"
    echo -e "Snap Store:   $(if [ "$SNAP_STATUS" = "success" ]; then echo -e "${GREEN}✅ Published${NC}"; else echo -e "${YELLOW}⏳ Pending${NC}"; fi)"
    echo -e "AUR (Arch):   $(if [ "$AUR_STATUS" = "success" ]; then echo -e "${GREEN}✅ Published${NC}"; else echo -e "${YELLOW}⏳ Pending${NC}"; fi)"
    echo -e "VS Code:      $(if [ "$VSCODE_STATUS" = "success" ]; then echo -e "${GREEN}✅ Published${NC}"; else echo -e "${YELLOW}⏳ Pending${NC}"; fi)"
    echo -e "Chocolatey:   $(if [ "$CHOCO_STATUS" = "success" ]; then echo -e "${GREEN}✅ Published${NC}"; else echo -e "${YELLOW}⏳ Pending${NC}"; fi)"
    
    echo ""
    echo -e "${BOLD}${CYAN}📋 QUICK ACTIONS${NC}"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo -e "${YELLOW}Update Stats:${NC}    ./scripts/download_tracker.sh"
    echo -e "${YELLOW}Quick Check:${NC}     ./scripts/quick_stats.sh"
    echo -e "${YELLOW}View JSON:${NC}       cat download_stats.json"
    echo -e "${YELLOW}Track Changes:${NC}   git add download_stats.json && git commit -m \"Update download stats\""
    
else
    echo -e "${RED}❌ No statistics available. Run ./scripts/download_tracker.sh first${NC}"
fi

echo ""
echo -e "${BLUE}═══════════════════════════════════════════════════════════════${NC}"
