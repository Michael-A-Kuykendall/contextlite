#!/bin/bash

# Real-time Phase 1 monitoring - checks every 30 seconds for release completion

echo "🚀 ContextLite Phase 1 - REAL-TIME AUTOMATION MONITORING"
echo "========================================================"
echo "Monitoring v0.9.0-alpha5 automation execution..."
echo "Started: $(date)"
echo ""

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
PURPLE='\033[0;35m'
NC='\033[0m'

check_count=0
max_checks=40  # Monitor for 20 minutes (40 checks * 30 seconds)

while [ $check_count -lt $max_checks ]; do
    check_count=$((check_count + 1))
    echo -e "${BLUE}=== Real-time Check #$check_count at $(date) ===${NC}"
    
    # Check GitHub releases (without jq dependency)
    releases_response=$(curl -s https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases)
    
    if echo "$releases_response" | grep -q '"tag_name"'; then
        echo -e "${GREEN}🎉 BREAKTHROUGH! GitHub releases detected!${NC}"
        echo ""
        
        # Get release details (without jq)
        echo "📦 Release Information:"
        echo "$releases_response" | grep -E '"tag_name"|"name"|"published_at"' | head -6
        
        echo ""
        echo -e "${PURPLE}🚀 AUTOMATION COMPLETE! Running full marketplace validation...${NC}"
        ./validate_marketplaces.sh
        
        validation_result=$?
        if [ $validation_result -eq 0 ]; then
            echo -e "${GREEN}🏆 PHASE 1 VICTORY! All marketplaces successfully validated!${NC}"
            echo "Ready to proceed to Phase 2."
            exit 0
        elif [ $validation_result -eq 1 ]; then
            echo -e "${YELLOW}⚡ Partial success! Some marketplaces still processing...${NC}"
            echo "Will continue monitoring for complete success."
        fi
    else
        echo -e "${YELLOW}⏳ Build in progress... GitHub releases not yet available${NC}"
    fi
    
    # Quick status indicators
    echo -n "Quick checks: "
    
    # npm
    if npm view contextlite version 2>/dev/null | grep -q "0.9.0"; then
        echo -n "npm✅ "
    else
        echo -n "npm⏳ "
    fi
    
    # PyPI (check for actual package, not just HTTP 200)
    if curl -s https://pypi.org/project/contextlite/ | grep -q "contextlite.*0\.9\.0"; then
        echo -n "PyPI✅ "
    else
        echo -n "PyPI⏳ "
    fi
    
    # Docker Hub
    if docker search contextlite 2>/dev/null | grep -q "contextlite"; then
        echo -n "Docker✅"
    else
        echo -n "Docker⏳"
    fi
    
    echo ""
    echo ""
    
    if [ $check_count -lt $max_checks ]; then
        echo "⏱️  Next check in 30 seconds..."
        sleep 30
    fi
done

echo -e "${RED}⏰ Monitoring timeout after 20 minutes${NC}"
echo "GitHub Actions may need manual investigation."
