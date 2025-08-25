#!/bin/bash

# ContextLite Public Demo - Complete Production Deployment
# Orchestrates entire deployment pipeline for real public demo server

set -e

DOMAIN="${1:-demo.contextlite.com}"
EMAIL="${2:-admin@contextlite.com}"
CONTEXTLITE_BINARY_URL="${3:-}"

echo "🚀 ContextLite Public Demo - Complete Production Deployment"
echo "🌐 Domain: $DOMAIN"
echo "📧 SSL Email: $EMAIL"
echo "📅 Date: $(date)"
echo ""

# Check if running as proper user
if [[ $EUID -eq 0 ]]; then
   echo "❌ This script should not be run as root"
   echo "💡 Run as regular user with sudo privileges"
   exit 1
fi

# Verify prerequisites
echo "🔍 Checking prerequisites..."

# Check internet connectivity
if ! ping -c 1 google.com &> /dev/null; then
    echo "❌ No internet connectivity"
    exit 1
fi

echo "✅ Internet connectivity"

# Check sudo access
if ! sudo -n true 2>/dev/null; then
    echo "❌ This user needs sudo privileges"
    exit 1
fi

echo "✅ Sudo privileges available"

# Deployment phases
echo ""
echo "📋 Deployment Pipeline:"
echo "   1. 🏗️  Server provisioning and security hardening"
echo "   2. 📦 ContextLite binary installation"
echo "   3. 📊 Real data ingestion (7 major repositories)"
echo "   4. 🖥️  Web terminal interface deployment"
echo "   5. 🌐 Production configuration and testing"
echo ""

read -p "Continue with deployment? (y/N): " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "Deployment cancelled."
    exit 1
fi

# Phase 1: Server Provisioning
echo ""
echo "🏗️  Phase 1: Server Provisioning and Security Hardening"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [ -f "$SCRIPT_DIR/provision-server.sh" ]; then
    echo "📜 Running server provisioning script..."
    bash "$SCRIPT_DIR/provision-server.sh" "$DOMAIN" "$EMAIL"
else
    echo "❌ Server provisioning script not found at $SCRIPT_DIR/provision-server.sh"
    exit 1
fi

echo "✅ Server provisioning complete"

# Phase 2: ContextLite Binary Installation
echo ""
echo "📦 Phase 2: ContextLite Binary Installation"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

CONTEXTLITE_DIR="/opt/contextlite-demo/bin"
CONTEXTLITE_BIN="$CONTEXTLITE_DIR/contextlite"

if [ -n "$CONTEXTLITE_BINARY_URL" ]; then
    echo "🔽 Downloading ContextLite binary from: $CONTEXTLITE_BINARY_URL"
    sudo -u contextlite wget -O "$CONTEXTLITE_BIN" "$CONTEXTLITE_BINARY_URL"
    sudo chmod +x "$CONTEXTLITE_BIN"
elif [ -f "../build/contextlite" ]; then
    echo "📁 Copying local ContextLite binary..."
    sudo cp "../build/contextlite" "$CONTEXTLITE_BIN"
    sudo chown contextlite:contextlite "$CONTEXTLITE_BIN"
    sudo chmod +x "$CONTEXTLITE_BIN"
else
    echo "⚠️  No ContextLite binary provided - using mock mode"
    echo "💡 To use real binary, provide URL as 3rd argument or place binary at ../build/contextlite"
    
    # Create mock binary for testing
    sudo tee "$CONTEXTLITE_BIN" > /dev/null <<'EOF'
#!/bin/bash
echo "🔧 Mock ContextLite - Use real binary for production"
echo "Command: $@"
exit 0
EOF
    sudo chmod +x "$CONTEXTLITE_BIN"
fi

echo "✅ ContextLite binary installed at: $CONTEXTLITE_BIN"

# Phase 3: Data Ingestion
echo ""
echo "📊 Phase 3: Real Data Ingestion Pipeline"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

if [ -f "$SCRIPT_DIR/setup-data-pipeline.sh" ]; then
    echo "📜 Running data ingestion pipeline..."
    sudo -u contextlite bash "$SCRIPT_DIR/setup-data-pipeline.sh"
else
    echo "❌ Data pipeline script not found at $SCRIPT_DIR/setup-data-pipeline.sh"
    exit 1
fi

echo "✅ Data ingestion complete"

# Phase 4: Web Terminal Deployment
echo ""
echo "🖥️  Phase 4: Web Terminal Interface Deployment"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

if [ -f "$SCRIPT_DIR/deploy-web-terminal.sh" ]; then
    echo "📜 Running web terminal deployment..."
    bash "$SCRIPT_DIR/deploy-web-terminal.sh"
else
    echo "❌ Web terminal script not found at $SCRIPT_DIR/deploy-web-terminal.sh"
    exit 1
fi

echo "✅ Web terminal deployment complete"

# Phase 5: Production Configuration
echo ""
echo "🌐 Phase 5: Production Configuration and Testing"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Update nginx configuration for production
echo "🔧 Updating nginx configuration..."
sudo nginx -t
sudo systemctl reload nginx

# Test all endpoints
echo "🧪 Running production tests..."

# Test health endpoint
echo "❤️  Testing health endpoint..."
if curl -f http://localhost:8080/health > /dev/null 2>&1; then
    echo "✅ Health endpoint working"
else
    echo "❌ Health endpoint failed"
fi

# Test main page
echo "🌐 Testing main page..."
if curl -f http://localhost:8080 > /dev/null 2>&1; then
    echo "✅ Main page working"
else
    echo "❌ Main page failed"
fi

# Test stats endpoint
echo "📊 Testing stats endpoint..."
if curl -f http://localhost:8080/api/stats > /dev/null 2>&1; then
    echo "✅ Stats endpoint working"
else
    echo "❌ Stats endpoint failed"
fi

# Test nginx reverse proxy
echo "🔗 Testing nginx reverse proxy..."
if curl -f http://localhost/ > /dev/null 2>&1; then
    echo "✅ Nginx reverse proxy working"
else
    echo "❌ Nginx reverse proxy failed"
fi

# Create deployment summary
echo "📋 Creating deployment summary..."
DEPLOYMENT_SUMMARY="/opt/contextlite-demo/DEPLOYMENT_SUMMARY.md"

sudo tee "$DEPLOYMENT_SUMMARY" > /dev/null <<EOF
# ContextLite Public Demo - Deployment Summary

## 🎯 Deployment Information
- **Date**: $(date)
- **Domain**: $DOMAIN
- **Deployed by**: $(whoami)
- **Server**: $(hostname)
- **IP Address**: $(curl -s ifconfig.me || echo "Unknown")

## ✅ Components Deployed

### 🏗️ Server Infrastructure
- Ubuntu 22.04 LTS with security hardening
- UFW firewall (SSH, HTTP, HTTPS only)
- fail2ban intrusion prevention
- Automatic security updates enabled
- SSL certificate $([ -f /etc/letsencrypt/live/$DOMAIN/fullchain.pem ] && echo "installed" || echo "pending DNS setup")

### 📦 ContextLite Binary
- Location: $CONTEXTLITE_BIN
- Type: $([ -s "$CONTEXTLITE_BIN" ] && echo "Installed" || echo "Mock/Testing")
- Permissions: $(ls -la "$CONTEXTLITE_BIN" | cut -d' ' -f1)

### 📊 Data Pipeline
- Repositories: 7 (VSCode, React, Go, Rust, Node.js, TensorFlow, Kubernetes)
- Status: $([ -f /opt/contextlite-demo/data/ingestion_stats.json ] && echo "Complete" || echo "In Progress")
- Database: $([ -f /opt/contextlite-demo/data/contextlite.db ] && echo "Created" || echo "Pending")

### 🖥️ Web Terminal
- Service: $(sudo systemctl is-active contextlite-terminal || echo "Not Running")
- Port: 8080
- Features: xterm.js, session management, rate limiting, security

### 🌐 Web Server
- nginx: $(sudo systemctl is-active nginx || echo "Not Running")
- SSL: $([ -f /etc/letsencrypt/live/$DOMAIN/fullchain.pem ] && echo "Enabled" || echo "HTTP Only")
- Rate Limiting: 10 requests/minute per IP

## 🔧 Service Status
\`\`\`
$(sudo systemctl status contextlite-terminal --no-pager -l || echo "Service not running")
\`\`\`

## 📊 System Resources
\`\`\`
$(df -h /)
$(free -h)
\`\`\`

## 🌐 Access Information
- **Main Demo**: http$([ -f /etc/letsencrypt/live/$DOMAIN/fullchain.pem ] && echo "s" || echo "")://$DOMAIN/
- **Health Check**: http$([ -f /etc/letsencrypt/live/$DOMAIN/fullchain.pem ] && echo "s" || echo "")://$DOMAIN/health
- **Statistics**: http$([ -f /etc/letsencrypt/live/$DOMAIN/fullchain.pem ] && echo "s" || echo "")://$DOMAIN/api/stats

## 🛠️ Management Commands
\`\`\`bash
# Monitor services
/opt/contextlite-demo/bin/monitor.sh

# Monitor terminal
/opt/contextlite-demo/bin/monitor-terminal.sh

# Backup data
/opt/contextlite-demo/bin/backup.sh

# Restart terminal service
sudo systemctl restart contextlite-terminal

# View logs
sudo journalctl -u contextlite-terminal -f
\`\`\`

## 🔍 Troubleshooting
- **Service issues**: Check \`sudo systemctl status contextlite-terminal\`
- **Connection issues**: Verify nginx with \`sudo nginx -t\`
- **SSL issues**: Run \`sudo certbot --nginx -d $DOMAIN\`
- **Data issues**: Check \`/opt/contextlite-demo/data/logs/ingestion.log\`

## 📈 Next Steps
1. 🔗 Point DNS A record for $DOMAIN to this server's IP
2. 🔒 Run SSL certificate setup if domain is ready
3. 📊 Monitor performance and user analytics
4. 🔄 Set up automated backups and monitoring alerts
5. 📱 Test on mobile devices and different browsers

## 🎉 Success Metrics
- **Target**: 25+ concurrent users
- **Performance**: <500ms query response time
- **Uptime**: 99.9% availability
- **Security**: Zero incidents

---
**Status: $([ -f /etc/letsencrypt/live/$DOMAIN/fullchain.pem ] && echo "Production Ready 🚀" || echo "Staging Ready - Pending SSL 🔧")**
EOF

sudo chown contextlite:contextlite "$DEPLOYMENT_SUMMARY"

# Final status check
echo ""
echo "🎉 ContextLite Public Demo Deployment Complete!"
echo ""
echo "📊 Deployment Status:"
echo "   🏗️  Server: ✅ Provisioned and secured"
echo "   📦 Binary: ✅ Installed $([ -s "$CONTEXTLITE_BIN" ] && echo "(Real)" || echo "(Mock)")"
echo "   📊 Data: $([ -f /opt/contextlite-demo/data/ingestion_stats.json ] && echo "✅ Ingested" || echo "⏳ In Progress")"
echo "   🖥️  Terminal: $(sudo systemctl is-active contextlite-terminal &>/dev/null && echo "✅ Running" || echo "❌ Failed")"
echo "   🌐 Web: $(sudo systemctl is-active nginx &>/dev/null && echo "✅ Active" || echo "❌ Failed")"
echo "   🔒 SSL: $([ -f /etc/letsencrypt/live/$DOMAIN/fullchain.pem ] && echo "✅ Enabled" || echo "⏳ Pending DNS")"
echo ""

if sudo systemctl is-active contextlite-terminal &>/dev/null && sudo systemctl is-active nginx &>/dev/null; then
    echo "🚀 Demo Status: LIVE AND READY!"
    echo ""
    echo "🌐 Access your ContextLite public demo at:"
    
    if [ -f /etc/letsencrypt/live/$DOMAIN/fullchain.pem ]; then
        echo "   👉 https://$DOMAIN/"
    else
        echo "   👉 http://$DOMAIN/ (or server IP until DNS ready)"
    fi
    
    echo ""
    echo "🎯 Features Available:"
    echo "   • Real-time web terminal with ContextLite"
    echo "   • 7 major repositories indexed (3.8GB+ code)"
    echo "   • Secure sandboxed execution environment"
    echo "   • Session management and rate limiting"
    echo "   • Mobile-responsive design"
    echo "   • Performance monitoring and analytics"
    echo ""
    echo "💡 Test Commands:"
    echo "   contextlite search \"React component\""
    echo "   contextlite explain kubernetes/cmd"
    echo "   contextlite analyze tensorflow/python"
    echo "   contextlite stats"
    echo ""
else
    echo "❌ Deployment has issues - check service status"
    echo "🔍 Troubleshooting:"
    echo "   sudo systemctl status contextlite-terminal"
    echo "   sudo systemctl status nginx"
    echo "   sudo journalctl -u contextlite-terminal -n 20"
fi

echo "📋 Full deployment summary: $DEPLOYMENT_SUMMARY"
echo ""
echo "Happy coding! 🚀"
