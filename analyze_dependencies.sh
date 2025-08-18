#!/bin/bash

echo "=== CONTEXTLITE DEPENDENCY MAPPING ==="
echo "Analyzing current codebase architecture for perfect repository split"
echo ""

echo "1. CURRENT MODULE STRUCTURE:"
echo "----------------------------"
find . -name "*.go" -path "*/cmd/*" -o -path "*/internal/*" -o -path "*/pkg/*" | \
    grep -v archive | \
    head -30

echo ""
echo "2. IMPORT DEPENDENCY ANALYSIS:"
echo "------------------------------"
echo "Internal package imports:"
grep -r "contextlite/internal" --include="*.go" . 2>/dev/null | \
    grep -v archive | \
    cut -d'"' -f2 | \
    sort | uniq -c | sort -nr

echo ""
echo "PKG package imports:"
grep -r "contextlite/pkg" --include="*.go" . 2>/dev/null | \
    grep -v archive | \
    cut -d'"' -f2 | \
    sort | uniq -c | sort -nr

echo ""
echo "3. EXTERNAL DEPENDENCIES:"
echo "-------------------------"
grep -h "^require" go.mod | head -10

echo ""
echo "4. INTERNAL PACKAGE CROSS-DEPENDENCIES:"
echo "---------------------------------------"
for dir in internal/*/; do
    if [ -d "$dir" ]; then
        dirname=$(basename "$dir")
        echo "=== $dirname ==="
        grep -r "contextlite/internal" "$dir"/*.go 2>/dev/null | \
            grep -v "contextlite/internal/$dirname" | \
            cut -d'"' -f2 | \
            sort | uniq
    fi
done
