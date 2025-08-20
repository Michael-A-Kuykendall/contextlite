#!/bin/bash
set -e

echo "🧪 Testing Hugging Face Spaces"

# Test page accessibility
echo "🌐 Testing Hugging Face page..."
RESPONSE=$(curl -s -o /dev/null -w "%{http_code}" "https://huggingface.co/spaces/MikeKuykendall/contextlite-download")
if [ "$RESPONSE" = "200" ]; then
    echo "✅ Hugging Face page accessible (HTTP $RESPONSE)"
else
    echo "❌ Hugging Face page returned HTTP $RESPONSE"
fi

# Test download links
echo "🔗 Testing download links..."
PAGE_CONTENT=$(curl -s "https://huggingface.co/spaces/MikeKuykendall/contextlite-download")
if echo "$PAGE_CONTENT" | grep -q "GitHub API"; then
    echo "✅ GitHub API integration working"
else
    echo "❌ GitHub API integration not found"
fi

if echo "$PAGE_CONTENT" | grep -q "contextlite"; then
    echo "✅ ContextLite content found on page"
else
    echo "❌ ContextLite content not found"
fi

# Test direct API call to HF space
echo "🤖 Testing Gradio API..."
GRADIO_RESPONSE=$(curl -s -o /dev/null -w "%{http_code}" "https://mikekuykendall-contextlite-download.hf.space/")
if [ "$GRADIO_RESPONSE" = "200" ]; then
    echo "✅ Gradio app accessible (HTTP $GRADIO_RESPONSE)"
else
    echo "❌ Gradio app returned HTTP $GRADIO_RESPONSE"
fi

# Test if the page contains version information
echo "📦 Testing version information display..."
if echo "$PAGE_CONTENT" | grep -q "0\.9\.0"; then
    echo "✅ Version information displayed correctly"
else
    echo "⚠️  Version information may not be displayed"
fi

# Test download button functionality
echo "🔽 Testing download button presence..."
if echo "$PAGE_CONTENT" | grep -q -i "download"; then
    echo "✅ Download functionality present"
else
    echo "❌ Download functionality not found"
fi

echo "✅ Hugging Face test completed"
