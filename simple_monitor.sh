#!/bin/bash

# Simple monitoring for GitHub releases
echo "🔍 Simple Release Monitor"
echo "========================"

while true; do
    echo "Checking at $(date)..."
    
    # Simple check for releases
    response=$(curl -s https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases)
    
    if echo "$response" | grep -q '"tag_name"'; then
        echo "✅ RELEASES FOUND!"
        echo "$response" | grep '"tag_name"' | head -3
        echo ""
        echo "🎉 Running validation..."
        ./validate_marketplaces.sh
        break
    else
        echo "⏳ No releases yet, builds still in progress..."
    fi
    
    echo "Waiting 60 seconds..."
    echo ""
    sleep 60
done
