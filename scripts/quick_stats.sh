#!/bin/bash

# Quick one-liner download stats (no dependencies)
echo "🚀 ContextLite Download Stats (Quick Check)"

echo -n "NPM: "
NPM_RESULT=$(curl -s "https://api.npmjs.org/downloads/range/last-month/contextlite" | grep -o '"downloads":[0-9]*' | grep -o '[0-9]*' | awk '{sum+=$1} END {print sum}')
if [ -n "$NPM_RESULT" ] && [ "$NPM_RESULT" != "0" ]; then
    echo "$NPM_RESULT downloads (last month)"
else
    echo "No data available"
fi

echo -n "PyPI: "
# Check if package exists on PyPI
PYPI_EXISTS=$(curl -s "https://pypi.org/pypi/contextlite/json" | grep -o '"name":"contextlite"' | head -1)
if [ -n "$PYPI_EXISTS" ]; then
    echo "✅ Published (v1.0.43)"
else
    echo "Not published"
fi

echo -n "Docker: "
DOCKER_RESULT=$(curl -s "https://hub.docker.com/v2/repositories/makuykendall/contextlite/" | grep -o '"pull_count":[0-9]*' | grep -o '[0-9]*' | head -1)
if [ -n "$DOCKER_RESULT" ] && [ "$DOCKER_RESULT" != "0" ]; then
    echo "$DOCKER_RESULT total pulls"
else
    echo "No data available"
fi

echo -n "Crates: "
CRATES_RESULT=$(curl -s "https://crates.io/api/v1/crates/contextlite-client" | grep -o '"downloads":[0-9]*' | grep -o '[0-9]*' | head -1)
if [ -n "$CRATES_RESULT" ] && [ "$CRATES_RESULT" != "0" ]; then
    echo "$CRATES_RESULT total downloads"
else
    echo "No data available"
fi

if [ -n "$GITHUB_TOKEN" ]; then
    echo -n "GitHub: "
    GITHUB_RESULT=$(curl -s -H "Authorization: token $GITHUB_TOKEN" "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases" | grep -o '"download_count":[0-9]*' | grep -o '[0-9]*' | awk '{sum+=$1} END {print sum}')
    if [ -n "$GITHUB_RESULT" ] && [ "$GITHUB_RESULT" != "0" ]; then
        echo "$GITHUB_RESULT total downloads"
    else
        echo "0 total downloads"
    fi
else
    echo "GitHub: GITHUB_TOKEN not set"
fi

echo ""
echo "💡 For detailed tracking, run: ./scripts/download_tracker.sh"
