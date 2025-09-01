#!/bin/bash

# ContextLite Package Manager Validation Test
# Tests the actual deployment status of each package manager

set -e

# Color output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}📦 ContextLite Package Manager Validation Test${NC}"
echo "================================================================"

# Results tracking
declare -A RESULTS
TOTAL_TESTED=0
TOTAL_WORKING=0

# Test npm
echo -e "${YELLOW}Testing npm...${NC}"
TOTAL_TESTED=$((TOTAL_TESTED + 1))
if curl -s "https://registry.npmjs.org/contextlite" | grep -q '"name":"contextlite"'; then
    echo -e "${GREEN}✅ npm: Package available${NC}"
    RESULTS["npm"]="✅ WORKING"
    TOTAL_WORKING=$((TOTAL_WORKING + 1))
else
    echo -e "${RED}❌ npm: Package not found${NC}"
    RESULTS["npm"]="❌ FAILED"
fi

# Test PyPI
echo -e "${YELLOW}Testing PyPI...${NC}"
TOTAL_TESTED=$((TOTAL_TESTED + 1))
if curl -s "https://pypi.org/pypi/contextlite/json" | grep -q '"name": "contextlite"'; then
    echo -e "${GREEN}✅ PyPI: Package available${NC}"
    RESULTS["pypi"]="✅ WORKING"
    TOTAL_WORKING=$((TOTAL_WORKING + 1))
else
    echo -e "${RED}❌ PyPI: Package not found${NC}"
    RESULTS["pypi"]="❌ FAILED"
fi

# Test Chocolatey
echo -e "${YELLOW}Testing Chocolatey...${NC}"
TOTAL_TESTED=$((TOTAL_TESTED + 1))
if curl -s "https://community.chocolatey.org/api/v2/Packages?\$filter=Id%20eq%20%27contextlite%27" | grep -q "contextlite"; then
    echo -e "${GREEN}✅ Chocolatey: Package available${NC}"
    RESULTS["chocolatey"]="✅ WORKING"
    TOTAL_WORKING=$((TOTAL_WORKING + 1))
else
    echo -e "${RED}❌ Chocolatey: Package not found${NC}"
    RESULTS["chocolatey"]="❌ FAILED"
fi

# Test Docker Hub
echo -e "${YELLOW}Testing Docker Hub...${NC}"
TOTAL_TESTED=$((TOTAL_TESTED + 1))
if curl -s "https://hub.docker.com/v2/repositories/makuykendall/contextlite/" | grep -q '"name": "makuykendall/contextlite"'; then
    echo -e "${GREEN}✅ Docker Hub: Repository available${NC}"
    RESULTS["docker"]="✅ WORKING"
    TOTAL_WORKING=$((TOTAL_WORKING + 1))
else
    echo -e "${RED}❌ Docker Hub: Repository not found${NC}"
    RESULTS["docker"]="❌ FAILED"
fi

# Test GitHub Packages  
echo -e "${YELLOW}Testing GitHub Packages...${NC}"
TOTAL_TESTED=$((TOTAL_TESTED + 1))
if [ -n "$GITHUB_TOKEN" ]; then
    if curl -s -H "Authorization: token $GITHUB_TOKEN" "https://api.github.com/user/packages?package_type=npm" | grep -q "contextlite"; then
        echo -e "${GREEN}✅ GitHub Packages: Package available${NC}"
        RESULTS["github_packages"]="✅ WORKING"
        TOTAL_WORKING=$((TOTAL_WORKING + 1))
    else
        echo -e "${RED}❌ GitHub Packages: Package not found${NC}"
        RESULTS["github_packages"]="❌ FAILED"
    fi
else
    echo -e "${YELLOW}⚠️  GitHub Packages: Skipped (no GITHUB_TOKEN)${NC}"
    RESULTS["github_packages"]="⚠️ SKIPPED"
    TOTAL_TESTED=$((TOTAL_TESTED - 1))
fi

# Test Homebrew
echo -e "${YELLOW}Testing Homebrew...${NC}"
TOTAL_TESTED=$((TOTAL_TESTED + 1))
if curl -s "https://formulae.brew.sh/api/formula/contextlite.json" | grep -q '"name":"contextlite"'; then
    echo -e "${GREEN}✅ Homebrew: Formula available${NC}"
    RESULTS["homebrew"]="✅ WORKING"
    TOTAL_WORKING=$((TOTAL_WORKING + 1))
else
    echo -e "${RED}❌ Homebrew: Formula not found${NC}"
    RESULTS["homebrew"]="❌ FAILED"
fi

# Test Crates.io
echo -e "${YELLOW}Testing Crates.io...${NC}"
TOTAL_TESTED=$((TOTAL_TESTED + 1))
if curl -s "https://crates.io/api/v1/crates/contextlite" | grep -q '"name":"contextlite"'; then
    echo -e "${GREEN}✅ Crates.io: Package available${NC}"
    RESULTS["crates"]="✅ WORKING"
    TOTAL_WORKING=$((TOTAL_WORKING + 1))
else
    echo -e "${RED}❌ Crates.io: Package not found${NC}"
    RESULTS["crates"]="❌ FAILED"
fi

# Test Snap Store
echo -e "${YELLOW}Testing Snap Store...${NC}"
TOTAL_TESTED=$((TOTAL_TESTED + 1))
if curl -s "https://api.snapcraft.io/v2/snaps/info/contextlite" | grep -q '"name": "contextlite"'; then
    echo -e "${GREEN}✅ Snap Store: Package available${NC}"
    RESULTS["snap"]="✅ WORKING"
    TOTAL_WORKING=$((TOTAL_WORKING + 1))
else
    echo -e "${RED}❌ Snap Store: Package not found${NC}"
    RESULTS["snap"]="❌ FAILED"
fi

# Test AUR (Arch User Repository)
echo -e "${YELLOW}Testing AUR...${NC}"
TOTAL_TESTED=$((TOTAL_TESTED + 1))
if curl -s "https://aur.archlinux.org/rpc/?v=5&type=info&arg=contextlite" | grep -q '"Name":"contextlite"'; then
    echo -e "${GREEN}✅ AUR: Package available${NC}"
    RESULTS["aur"]="✅ WORKING"
    TOTAL_WORKING=$((TOTAL_WORKING + 1))
else
    echo -e "${RED}❌ AUR: Package not found${NC}"
    RESULTS["aur"]="❌ FAILED"
fi

# Test Winget
echo -e "${YELLOW}Testing Winget...${NC}"
TOTAL_TESTED=$((TOTAL_TESTED + 1))
if curl -s "https://api.winget.microsoft.com/v1.0/packages/contextlite" | grep -q "contextlite"; then
    echo -e "${GREEN}✅ Winget: Package available${NC}"
    RESULTS["winget"]="✅ WORKING"
    TOTAL_WORKING=$((TOTAL_WORKING + 1))
else
    echo -e "${RED}❌ Winget: Package not found${NC}"
    RESULTS["winget"]="❌ FAILED"
fi

# Summary Report
echo "================================================================"
echo -e "${BLUE}📊 Package Manager Status Summary${NC}"
echo "================================================================"

SUCCESS_RATE=$(echo "scale=1; $TOTAL_WORKING * 100 / $TOTAL_TESTED" | bc -l 2>/dev/null || echo "0")

echo -e "${YELLOW}Overall Success Rate: $TOTAL_WORKING/$TOTAL_TESTED ($SUCCESS_RATE%)${NC}"
echo

for manager in npm pypi chocolatey docker github_packages homebrew crates snap aur winget; do
    if [[ -n "${RESULTS[$manager]}" ]]; then
        echo -e "$manager: ${RESULTS[$manager]}"
    fi
done

# Generate package status report
cat > package_manager_status.md << EOF
# ContextLite Package Manager Status Report

Generated: $(date)

## Summary
- **Total Tested**: $TOTAL_TESTED package managers
- **Working**: $TOTAL_WORKING package managers  
- **Success Rate**: $SUCCESS_RATE%

## Detailed Status

| Package Manager | Status | Notes |
|-----------------|--------|-------|
| npm | ${RESULTS["npm"]} | Node.js package registry |
| PyPI | ${RESULTS["pypi"]} | Python package index |
| Chocolatey | ${RESULTS["chocolatey"]} | Windows package manager |
| Docker Hub | ${RESULTS["docker"]} | Container registry |
| GitHub Packages | ${RESULTS["github_packages"]} | GitHub package registry |
| Homebrew | ${RESULTS["homebrew"]} | macOS package manager |
| Crates.io | ${RESULTS["crates"]} | Rust package registry |
| Snap Store | ${RESULTS["snap"]} | Universal Linux packages |
| AUR | ${RESULTS["aur"]} | Arch Linux user repository |
| Winget | ${RESULTS["winget"]} | Windows package manager |

## Recommendations

### Working Platforms
Deploy updates and test on these platforms first:

EOF

# Add working platforms to recommendations
for manager in npm pypi chocolatey docker github_packages homebrew crates snap aur winget; do
    if [[ "${RESULTS[$manager]}" == "✅ WORKING" ]]; then
        echo "- $manager" >> package_manager_status.md
    fi
done

cat >> package_manager_status.md << EOF

### Failed Platforms  
Address deployment issues on these platforms:

EOF

# Add failed platforms to recommendations
for manager in npm pypi chocolatey docker github_packages homebrew crates snap aur winget; do
    if [[ "${RESULTS[$manager]}" == "❌ FAILED" ]]; then
        echo "- $manager" >> package_manager_status.md
    fi
done

cat >> package_manager_status.md << EOF

### Next Steps
1. Focus on maintaining working platforms
2. Investigate and fix failing platforms
3. Implement automated monitoring for all platforms
4. Set up deployment pipeline with conditional logic

EOF

echo
echo -e "${GREEN}✅ Report generated: package_manager_status.md${NC}"

# Return appropriate exit code
if [ $TOTAL_WORKING -eq 0 ]; then
    echo -e "${RED}🚨 NO PACKAGE MANAGERS WORKING - Critical deployment failure${NC}"
    exit 2
elif [ $TOTAL_WORKING -lt $((TOTAL_TESTED / 2)) ]; then
    echo -e "${YELLOW}⚠️  LESS THAN 50% SUCCESS RATE - Deployment issues detected${NC}"
    exit 1
else
    echo -e "${GREEN}🎉 SUFFICIENT PACKAGE MANAGERS WORKING - Deployment viable${NC}"
    exit 0
fi
