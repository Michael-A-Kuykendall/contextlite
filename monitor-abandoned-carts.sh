#!/bin/bash

# 🎯 ContextLite Abandoned Cart Recovery - Monitoring Script

echo "🚀 ContextLite Abandoned Cart Recovery System Monitor"
echo "=================================================="
echo "Date: $(date)"
echo ""

# Health check
echo "🔍 SYSTEM HEALTH:"
HEALTH=$(curl -s "https://contextlite-production.up.railway.app/health")
if echo "$HEALTH" | grep -q "healthy"; then
    echo "✅ Basic health: HEALTHY"
    echo "   Response: $HEALTH"
else
    echo "❌ Basic health: FAILED"
    echo "   Response: $HEALTH"
fi
echo ""

# Abandoned cart endpoints
echo "📊 ABANDONED CART SYSTEM:"
STATS=$(curl -s "https://contextlite-production.up.railway.app/abandoned-carts/stats")
if echo "$STATS" | grep -q "success"; then
    echo "✅ Abandoned cart system: DEPLOYED"
    echo "   Stats: $STATS"
elif echo "$STATS" | grep -q "404"; then
    echo "⚠️  Abandoned cart system: NOT YET DEPLOYED"
    echo "   Railway is likely still building. Check: https://railway.app"
else
    echo "❓ Abandoned cart system: UNKNOWN STATUS"
    echo "   Response: $STATS"
fi
echo ""

# Email test
echo "📧 EMAIL SYSTEM:"
EMAIL_TEST=$(curl -s -X POST "https://contextlite-production.up.railway.app/test-email")
if echo "$EMAIL_TEST" | grep -q "success"; then
    echo "✅ Email system: WORKING"
    echo "   Response: $EMAIL_TEST"
elif echo "$EMAIL_TEST" | grep -q "404"; then
    echo "⚠️  Email system: NOT YET DEPLOYED"
elif echo "$EMAIL_TEST" | grep -q "Invalid"; then
    echo "⚠️  Email system: NEEDS CONFIGURATION"
    echo "   Basic endpoint exists but needs SMTP setup"
else
    echo "❓ Email system: UNKNOWN STATUS"
    echo "   Response: $EMAIL_TEST"
fi
echo ""

# Manual processing test
echo "🔄 PROCESSING TRIGGER:"
PROCESS=$(curl -s -X POST "https://contextlite-production.up.railway.app/abandoned-carts/process")
if echo "$PROCESS" | grep -q "success"; then
    echo "✅ Manual processing: WORKING"
    echo "   Response: $PROCESS"
elif echo "$PROCESS" | grep -q "404"; then
    echo "⚠️  Manual processing: NOT YET DEPLOYED"
else
    echo "❓ Manual processing: UNKNOWN STATUS"
    echo "   Response: $PROCESS"
fi
echo ""

# Summary
echo "📋 DEPLOYMENT STATUS SUMMARY:"
if echo "$STATS" | grep -q "success"; then
    echo "🎉 ABANDONED CART RECOVERY SYSTEM IS LIVE!"
    echo ""
    echo "🎯 IMMEDIATE ACTIONS:"
    echo "1. Add 'checkout.session.expired' to Stripe webhook"
    echo "2. Configure SMTP settings in Railway if email test failed"
    echo "3. Create test abandoned cart to verify email flow"
    echo "4. Monitor stats with: curl https://contextlite-production.up.railway.app/abandoned-carts/stats"
else
    echo "⏳ WAITING FOR RAILWAY DEPLOYMENT..."
    echo ""
    echo "🎯 WHILE YOU WAIT:"
    echo "1. Check Railway deployment: https://railway.app → Your Project → Deployments"
    echo "2. Prepare Stripe webhook: Add 'checkout.session.expired' event"
    echo "3. Verify SMTP credentials in Railway environment variables"
    echo "4. Run this script again in 2-3 minutes"
fi
echo ""

echo "🔄 To run this monitor again: ./monitor-abandoned-carts.sh"
echo "📚 Full testing guide: See ABANDONED_CART_TESTING_GUIDE.md"
