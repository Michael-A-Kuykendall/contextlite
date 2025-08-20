#!/bin/bash

# Continuous monitoring script for Phase 1 Integration Testing
# Checks marketplace availability every 2 minutes

echo "🔄 ContextLite Phase 1 - Continuous Monitoring"
echo "=============================================="
echo "Monitoring marketplace automation progress..."
echo "Started: $(date)"
echo "Target version: v0.9.0-alpha3"
echo ""

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

check_count=0
max_checks=30  # Monitor for 1 hour (30 checks * 2 minutes)

while [ $check_count -lt $max_checks ]; do
    check_count=$((check_count + 1))
    echo -e "${BLUE}=== Check #$check_count at $(date) ===${NC}"
    
    # Quick GitHub releases check
    echo "📦 Checking GitHub Releases..."
    if curl -s https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases | grep -q "v0.9.0-alpha"; then
        echo -e "${GREEN}✅ GitHub Releases: Available${NC}"
        
        # If releases are available, check all marketplaces
        echo ""
        echo "🚀 Releases detected! Running full marketplace validation..."
        ./validate_marketplaces.sh
        
        validation_result=$?
        if [ $validation_result -eq 0 ]; then
            echo -e "${GREEN}🎉 Phase 1 SUCCESS! All marketplaces validated.${NC}"
            echo "Ready to proceed to Phase 2."
            exit 0
        elif [ $validation_result -eq 1 ]; then
            echo -e "${YELLOW}⚠️  Partial success - continuing monitoring...${NC}"
        fi
    else
        echo -e "${RED}❌ GitHub Releases: Still processing${NC}"
    fi
    
    # Quick npm check
    echo "📦 Quick npm check..."
    if npm view contextlite version 2>/dev/null | grep -q "0.9.0"; then
        echo -e "${GREEN}✅ npm: Package available${NC}"
    else
        echo -e "${RED}❌ npm: Not available yet${NC}"
    fi
    
    # Quick PyPI check
    echo "📦 Quick PyPI check..."
    if curl -s https://pypi.org/project/contextlite/ | grep -q "contextlite"; then
        echo -e "${GREEN}✅ PyPI: Package available${NC}"
    else
        echo -e "${RED}❌ PyPI: Not available yet${NC}"
    fi
    
    echo ""
    
    if [ $check_count -lt $max_checks ]; then
        echo "⏳ Waiting 2 minutes before next check..."
        sleep 120
    fi
done

echo -e "${YELLOW}⏰ Monitoring timeout reached after $max_checks checks${NC}"
echo "Manual investigation recommended if automation hasn't completed."
