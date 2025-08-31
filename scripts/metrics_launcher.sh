#!/bin/bash

# ContextLite Deployment Metrics Launcher
# Easy access to deployment analytics regardless of deployment chaos

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
PURPLE='\033[0;35m'
NC='\033[0m' # No Color

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo -e "${BLUE}🚀 ContextLite Deployment Metrics Suite${NC}"
echo -e "${YELLOW}Choose your analysis:${NC}"
echo ""
echo "1. 📈 Executive Dashboard (recommended)"
echo "2. 📊 Visual Trends Analysis (NEW!)"
echo "3. 🔍 Full Deployment Metrics"
echo "4. 🏥 Workflow Health Analysis"
echo "5. 🐍 PyPI Detailed Analytics"
echo "6. 💰 Business Conversion Analysis"
echo "7. 🔄 All Reports (comprehensive)"
echo ""

read -p "Enter choice (1-7): " choice

case $choice in
    1)
        echo -e "${GREEN}📈 Running Executive Dashboard...${NC}"
        py "$SCRIPT_DIR/master_deployment_dashboard.py" --mode executive
        ;;
    2)
        echo -e "${GREEN}📊 Running Visual Trends Analysis...${NC}"
        py "$SCRIPT_DIR/quick_trends_dashboard.py"
        ;;
    3)
        echo -e "${GREEN}🔍 Running Full Deployment Metrics...${NC}"
        py "$SCRIPT_DIR/deployment_metrics.py"
        ;;
    4)
        echo -e "${GREEN}🏥 Running Workflow Health Analysis...${NC}"
        if [ -z "$GITHUB_TOKEN" ]; then
            echo -e "${RED}❌ GITHUB_TOKEN environment variable required${NC}"
            echo "Set it with: export GITHUB_TOKEN='your_token_here'"
            exit 1
        fi
        py "$SCRIPT_DIR/workflow_health_monitor.py"
        ;;
    5)
        echo -e "${GREEN}🐍 Running PyPI Analytics...${NC}"
        py "$SCRIPT_DIR/pypi_stats_collector.py"
        ;;
    6)
        echo -e "${GREEN}💰 Running Business Conversion Analysis...${NC}"
        py "$SCRIPT_DIR/deployment_metrics.py" --conversions
        ;;
    7)
        echo -e "${GREEN}🔄 Running All Reports...${NC}"
        py "$SCRIPT_DIR/master_deployment_dashboard.py" --mode full
        ;;
    *)
        echo -e "${RED}Invalid choice. Exiting.${NC}"
        exit 1
        ;;
esac

echo ""
echo -e "${BLUE}✅ Analysis complete!${NC}"
echo ""
echo -e "${YELLOW}💡 Pro Tips:${NC}"
echo "   • Run this daily to track trends"
echo "   • Use Executive Dashboard for quick business insights"
echo "   • Check Workflow Health after deployment changes"
echo "   • PyPI Analytics shows detailed download patterns"
