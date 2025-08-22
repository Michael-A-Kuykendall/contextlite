#!/bin/bash

# ContextLite Download Tracker
# Fetches download statistics from all distribution channels

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Output file
OUTPUT_FILE="download_stats.json"
TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

echo -e "${BLUE}🚀 ContextLite Download Tracker${NC}"
echo -e "${CYAN}Fetching download statistics from all channels...${NC}"
echo ""

# Initialize JSON output
cat > $OUTPUT_FILE << EOF
{
  "timestamp": "$TIMESTAMP",
  "total_downloads": 0,
  "channels": {
EOF

TOTAL_DOWNLOADS=0
FIRST_ENTRY=true

# Function to add JSON entry
add_json_entry() {
    local platform=$1
    local downloads=$2
    local url=$3
    local status=$4
    
    if [ "$FIRST_ENTRY" = true ]; then
        FIRST_ENTRY=false
    else
        echo "," >> $OUTPUT_FILE
    fi
    
    cat >> $OUTPUT_FILE << EOF
    "$platform": {
      "downloads": $downloads,
      "url": "$url",
      "status": "$status"
    }
EOF
    
    if [ "$downloads" != "null" ] && [ "$downloads" -ne 0 ] 2>/dev/null; then
        TOTAL_DOWNLOADS=$((TOTAL_DOWNLOADS + downloads))
    fi
}

# Function to safely extract numbers from text
extract_number() {
    local input="$1"
    if [ -z "$input" ]; then
        echo "0"
    else
        echo "$input" | grep -o '[0-9,]\+' | tr -d ',' | head -1 | sed 's/^$/0/'
    fi
}

echo -e "${YELLOW}📦 Checking package managers...${NC}"

# 1. NPM Downloads
echo -n "NPM: "
NPM_DOWNLOADS=$(curl -s "https://api.npmjs.org/downloads/range/last-month/contextlite" | \
    grep -o '"downloads":[0-9]*' | grep -o '[0-9]*' | awk '{sum+=$1} END {print sum+0}' || echo "0")
if [ "$NPM_DOWNLOADS" != "0" ] && [ -n "$NPM_DOWNLOADS" ]; then
    echo -e "${GREEN}$NPM_DOWNLOADS downloads${NC}"
    add_json_entry "npm" "$NPM_DOWNLOADS" "https://www.npmjs.com/package/contextlite" "success"
else
    echo -e "${RED}Failed to fetch${NC}"
    add_json_entry "npm" "null" "https://www.npmjs.com/package/contextlite" "error"
fi

# 2. PyPI Downloads (using pypistats API)
echo -n "PyPI: "
# First check if package exists on PyPI
PYPI_EXISTS=$(curl -s "https://pypi.org/pypi/contextlite/json" | grep -o '"name":"contextlite"' | head -1)
if [ -n "$PYPI_EXISTS" ]; then
    # Package exists, try to get download stats
    PYPI_DOWNLOADS=$(curl -s "https://pypistats.org/api/packages/contextlite/recent" 2>/dev/null | \
        grep -o '"last_month":[0-9]*' | grep -o '[0-9]*' | head -1)
    
    # If pypistats is down or returns error, try alternative sources
    if [ -z "$PYPI_DOWNLOADS" ] || [ "$PYPI_DOWNLOADS" = "0" ]; then
        echo -e "${GREEN}✅ Published${NC} (stats unavailable)"
        add_json_entry "pypi" "null" "https://pypi.org/project/contextlite/" "published_no_stats"
    else
        echo -e "${GREEN}$PYPI_DOWNLOADS downloads${NC}"
        add_json_entry "pypi" "$PYPI_DOWNLOADS" "https://pypi.org/project/contextlite/" "success"
    fi
else
    echo -e "${RED}Not published${NC}"
    add_json_entry "pypi" "null" "https://pypi.org/project/contextlite/" "not_published"
fi

# 3. Docker Hub Downloads
echo -n "Docker Hub: "
DOCKER_DOWNLOADS=$(curl -s "https://hub.docker.com/v2/repositories/makuykendall/contextlite/" | \
    grep -o '"pull_count":[0-9]*' | grep -o '[0-9]*' || echo "0")
if [ "$DOCKER_DOWNLOADS" != "0" ] && [ -n "$DOCKER_DOWNLOADS" ]; then
    echo -e "${GREEN}$DOCKER_DOWNLOADS pulls${NC}"
    add_json_entry "docker" "$DOCKER_DOWNLOADS" "https://hub.docker.com/r/makuykendall/contextlite" "success"
else
    echo -e "${RED}Failed to fetch${NC}"
    add_json_entry "docker" "null" "https://hub.docker.com/r/makuykendall/contextlite" "error"
fi

# 4. Crates.io Downloads
echo -n "Crates.io: "
CRATES_DOWNLOADS=$(curl -s "https://crates.io/api/v1/crates/contextlite-client" | \
    grep -o '"downloads":[0-9]*' | grep -o '[0-9]*' | head -1)
if [ -z "$CRATES_DOWNLOADS" ]; then
    CRATES_DOWNLOADS="0"
fi
if [ "$CRATES_DOWNLOADS" != "0" ] && [ -n "$CRATES_DOWNLOADS" ]; then
    echo -e "${GREEN}$CRATES_DOWNLOADS downloads${NC}"
    add_json_entry "crates" "$CRATES_DOWNLOADS" "https://crates.io/crates/contextlite-client" "success"
else
    echo -e "${RED}Failed to fetch${NC}"
    add_json_entry "crates" "null" "https://crates.io/crates/contextlite-client" "error"
fi

# 5. GitHub Releases Downloads
echo -n "GitHub Releases: "
if [ -n "$GITHUB_TOKEN" ]; then
    GITHUB_DOWNLOADS=$(curl -s -H "Authorization: token $GITHUB_TOKEN" \
        "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases" | \
        grep -o '"download_count":[0-9]*' | grep -o '[0-9]*' | awk '{sum+=$1} END {print sum+0}' || echo "0")
    
    if [ "$GITHUB_DOWNLOADS" != "0" ] && [ -n "$GITHUB_DOWNLOADS" ]; then
        echo -e "${GREEN}$GITHUB_DOWNLOADS downloads${NC}"
        add_json_entry "github" "$GITHUB_DOWNLOADS" "https://github.com/Michael-A-Kuykendall/contextlite/releases" "success"
    else
        echo -e "${YELLOW}0 downloads${NC}"
        add_json_entry "github" "0" "https://github.com/Michael-A-Kuykendall/contextlite/releases" "success"
    fi
else
    echo -e "${RED}GITHUB_TOKEN not set${NC}"
    add_json_entry "github" "null" "https://github.com/Michael-A-Kuykendall/contextlite/releases" "error"
fi

echo ""
echo -e "${YELLOW}🌐 Checking web-based platforms...${NC}"

# 6. Homebrew (scraping)
echo -n "Homebrew: "
HOMEBREW_DOWNLOADS=$(curl -s "https://formulae.brew.sh/api/formula/contextlite.json" | \
    grep -o '"contextlite":[0-9]*' | grep -o '[0-9]*' || echo "0")
if [ "$HOMEBREW_DOWNLOADS" != "0" ] && [ -n "$HOMEBREW_DOWNLOADS" ]; then
    echo -e "${GREEN}$HOMEBREW_DOWNLOADS installs (30d)${NC}"
    add_json_entry "homebrew" "$HOMEBREW_DOWNLOADS" "https://formulae.brew.sh/formula/contextlite" "success"
else
    echo -e "${YELLOW}Not available or 0 installs${NC}"
    add_json_entry "homebrew" "null" "https://formulae.brew.sh/formula/contextlite" "not_available"
fi

# 7. Snap Store (scraping)
echo -n "Snap Store: "
SNAP_DOWNLOADS=$(curl -s "https://snapcraft.io/api/v1/snaps/info/contextlite" | \
    grep -o '"download_size":[0-9]*' | grep -o '[0-9]*' || echo "0")
if [ "$SNAP_DOWNLOADS" != "0" ] && [ -n "$SNAP_DOWNLOADS" ]; then
    echo -e "${GREEN}Data available${NC}"
    add_json_entry "snap" "$SNAP_DOWNLOADS" "https://snapcraft.io/contextlite" "success"
else
    echo -e "${YELLOW}Not published or no data${NC}"
    add_json_entry "snap" "null" "https://snapcraft.io/contextlite" "not_published"
fi

# 8. AUR (Arch User Repository) - scraping
echo -n "AUR: "
AUR_VOTES=$(curl -s "https://aur.archlinux.org/rpc/?v=5&type=info&arg[]=contextlite" | \
    grep -o '"Popularity":[0-9.]*' | grep -o '[0-9.]*' || echo "0")
if [ "$AUR_VOTES" != "0" ] && [ -n "$AUR_VOTES" ]; then
    echo -e "${GREEN}$AUR_VOTES popularity${NC}"
    add_json_entry "aur" "$AUR_VOTES" "https://aur.archlinux.org/packages/contextlite" "success"
else
    echo -e "${YELLOW}Not published or no data${NC}"
    add_json_entry "aur" "null" "https://aur.archlinux.org/packages/contextlite" "not_published"
fi

# 9. VS Code Marketplace
echo -n "VS Code: "
VSCODE_INSTALLS=$(curl -s "https://marketplace.visualstudio.com/items?itemName=contextlite.contextlite" | \
    grep -o '[0-9,]\+ installs' | head -1 | extract_number)
if [ -z "$VSCODE_INSTALLS" ]; then
    VSCODE_INSTALLS="0"
fi
if [ "$VSCODE_INSTALLS" != "0" ] && [ -n "$VSCODE_INSTALLS" ]; then
    echo -e "${GREEN}$VSCODE_INSTALLS installs${NC}"
    add_json_entry "vscode" "$VSCODE_INSTALLS" "https://marketplace.visualstudio.com/items?itemName=contextlite.contextlite" "success"
else
    echo -e "${YELLOW}Not published${NC}"
    add_json_entry "vscode" "null" "https://marketplace.visualstudio.com/items?itemName=contextlite.contextlite" "not_published"
fi

# 10. Chocolatey
echo -n "Chocolatey: "
CHOCO_DOWNLOADS=$(curl -s "https://community.chocolatey.org/api/v2/Packages?\$filter=Id%20eq%20'contextlite'" | \
    grep -o 'DownloadCount="[0-9]*"' | head -1 | extract_number)
if [ -z "$CHOCO_DOWNLOADS" ]; then
    CHOCO_DOWNLOADS="0"
fi
if [ "$CHOCO_DOWNLOADS" != "0" ] && [ -n "$CHOCO_DOWNLOADS" ]; then
    echo -e "${GREEN}$CHOCO_DOWNLOADS downloads${NC}"
    add_json_entry "chocolatey" "$CHOCO_DOWNLOADS" "https://community.chocolatey.org/packages/contextlite" "success"
else
    echo -e "${YELLOW}Not published${NC}"
    add_json_entry "chocolatey" "null" "https://community.chocolatey.org/packages/contextlite" "not_published"
fi

# Close JSON
cat >> $OUTPUT_FILE << EOF
  },
  "total_downloads": $TOTAL_DOWNLOADS
}
EOF

echo ""
echo -e "${BLUE}📊 Summary${NC}"
echo -e "${GREEN}Total Downloads: $TOTAL_DOWNLOADS${NC}"
echo -e "${CYAN}Report saved to: $OUTPUT_FILE${NC}"

# Pretty print the results
echo ""
echo -e "${BLUE}📈 Channel Breakdown:${NC}"

# Simple text processing for results breakdown
if [ -f "$OUTPUT_FILE" ]; then
    echo "  NPM:         $(grep -A3 '"npm"' $OUTPUT_FILE | grep '"downloads":' | grep -o '[0-9]*' || echo 'N/A')"
    echo "  PYPI:        $(grep -A3 '"pypi"' $OUTPUT_FILE | grep '"downloads":' | grep -o '[0-9]*' || echo 'N/A')"
    echo "  DOCKER:      $(grep -A3 '"docker"' $OUTPUT_FILE | grep '"downloads":' | grep -o '[0-9]*' || echo 'N/A')"
    echo "  CRATES:      $(grep -A3 '"crates"' $OUTPUT_FILE | grep '"downloads":' | grep -o '[0-9]*' || echo 'N/A')"
    echo "  GITHUB:      $(grep -A3 '"github"' $OUTPUT_FILE | grep '"downloads":' | grep -o '[0-9]*' || echo 'N/A')"
    echo "  HOMEBREW:    $(grep -A3 '"homebrew"' $OUTPUT_FILE | grep '"downloads":' | grep -o '[0-9]*' || echo 'N/A')"
    echo "  SNAP:        $(grep -A3 '"snap"' $OUTPUT_FILE | grep '"downloads":' | grep -o '[0-9]*' || echo 'N/A')"
    echo "  AUR:         $(grep -A3 '"aur"' $OUTPUT_FILE | grep '"downloads":' | grep -o '[0-9]*' || echo 'N/A')"
    echo "  VSCODE:      $(grep -A3 '"vscode"' $OUTPUT_FILE | grep '"downloads":' | grep -o '[0-9]*' || echo 'N/A')"
    echo "  CHOCOLATEY:  $(grep -A3 '"chocolatey"' $OUTPUT_FILE | grep '"downloads":' | grep -o '[0-9]*' || echo 'N/A')"
fi

echo ""
echo -e "${YELLOW}💡 Usage:${NC}"
echo -e "  View JSON: ${CYAN}cat $OUTPUT_FILE | jq${NC}"
echo -e "  Track changes: ${CYAN}git add $OUTPUT_FILE && git commit -m \"Update download stats\"${NC}"
echo -e "  Schedule: ${CYAN}crontab -e # Add: 0 6 * * * /path/to/download_tracker.sh${NC}"
