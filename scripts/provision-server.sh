#!/bin/bash

# ContextLite Public Demo Server Provisioning Script
# Sets up production Ubuntu server with Docker, nginx, SSL, and security hardening

set -e

DOMAIN="${1:-demo.contextlite.com}"
EMAIL="${2:-admin@contextlite.com}"

echo "🚀 Provisioning ContextLite Public Demo Server"
echo "🌐 Domain: $DOMAIN"
echo "📧 SSL Email: $EMAIL"
echo "📅 Date: $(date)"
echo ""

# Check if running as root
if [[ $EUID -eq 0 ]]; then
   echo "❌ This script should not be run as root for security reasons"
   echo "💡 Run as regular user with sudo privileges"
   exit 1
fi

# Update system
echo "📦 Updating system packages..."
sudo apt update && sudo apt upgrade -y

# Install essential packages
echo "🛠️  Installing essential packages..."
sudo apt install -y \
    curl wget git unzip \
    htop iotop nethogs \
    ufw fail2ban \
    nginx certbot python3-certbot-nginx \
    docker.io docker-compose \
    sqlite3 build-essential \
    jq tree ncdu

# Create contextlite user
echo "👤 Creating contextlite service user..."
if ! id "contextlite" &>/dev/null; then
    sudo adduser --disabled-password --gecos "ContextLite Demo Service" contextlite
    sudo usermod -aG docker contextlite
    sudo usermod -aG sudo contextlite
fi

# Configure Docker
echo "🐳 Configuring Docker..."
sudo systemctl enable docker
sudo systemctl start docker

# Create directory structure
echo "📁 Creating directory structure..."
sudo mkdir -p /opt/contextlite-demo/{bin,data,web,config,logs}
sudo chown -R contextlite:contextlite /opt/contextlite-demo

# Configure UFW firewall
echo "🔥 Configuring UFW firewall..."
sudo ufw --force reset
sudo ufw default deny incoming
sudo ufw default allow outgoing
sudo ufw allow ssh
sudo ufw allow 'Nginx Full'
sudo ufw --force enable

# Configure fail2ban
echo "🛡️  Configuring fail2ban..."
sudo tee /etc/fail2ban/jail.local > /dev/null <<EOF
[DEFAULT]
bantime = 3600
findtime = 600
maxretry = 3
backend = systemd

[sshd]
enabled = true
port = ssh
logpath = /var/log/auth.log
maxretry = 3
bantime = 3600

[nginx-http-auth]
enabled = true
filter = nginx-http-auth
logpath = /var/log/nginx/error.log
maxretry = 3
bantime = 3600

[nginx-limit-req]
enabled = true
filter = nginx-limit-req
logpath = /var/log/nginx/error.log
maxretry = 5
bantime = 600
EOF

sudo systemctl enable fail2ban
sudo systemctl restart fail2ban

# Secure SSH
echo "🔐 Securing SSH configuration..."
sudo cp /etc/ssh/sshd_config /etc/ssh/sshd_config.backup
sudo tee -a /etc/ssh/sshd_config > /dev/null <<EOF

# ContextLite Demo Security Settings
PermitRootLogin no
PasswordAuthentication no
PubkeyAuthentication yes
X11Forwarding no
MaxAuthTries 3
ClientAliveInterval 300
ClientAliveCountMax 2
EOF

sudo systemctl restart sshd

# Configure automatic updates
echo "🔄 Configuring automatic security updates..."
sudo apt install -y unattended-upgrades
echo 'Unattended-Upgrade::Automatic-Reboot "false";' | sudo tee -a /etc/apt/apt.conf.d/50unattended-upgrades

# Configure nginx base
echo "🌐 Configuring nginx..."
sudo tee /etc/nginx/sites-available/contextlite-demo > /dev/null <<EOF
# Rate limiting
limit_req_zone \$binary_remote_addr zone=demo:10m rate=10r/m;

server {
    listen 80;
    server_name $DOMAIN;
    
    # Security headers
    add_header X-Frame-Options "SAMEORIGIN" always;
    add_header X-Content-Type-Options "nosniff" always;
    add_header X-XSS-Protection "1; mode=block" always;
    add_header Referrer-Policy "strict-origin-when-cross-origin" always;
    
    # Rate limiting
    limit_req zone=demo burst=20 nodelay;
    
    # Serve static files
    location /static/ {
        alias /opt/contextlite-demo/web/static/;
        expires 1h;
        add_header Cache-Control "public, immutable";
    }
    
    # Proxy to ContextLite demo app
    location / {
        proxy_pass http://localhost:8080;
        proxy_http_version 1.1;
        proxy_set_header Upgrade \$http_upgrade;
        proxy_set_header Connection 'upgrade';
        proxy_set_header Host \$host;
        proxy_set_header X-Real-IP \$remote_addr;
        proxy_set_header X-Forwarded-For \$proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto \$scheme;
        proxy_cache_bypass \$http_upgrade;
        
        # Timeouts
        proxy_connect_timeout 30s;
        proxy_send_timeout 30s;
        proxy_read_timeout 30s;
    }
    
    # WebSocket support for terminal
    location /ws {
        proxy_pass http://localhost:8080;
        proxy_http_version 1.1;
        proxy_set_header Upgrade \$http_upgrade;
        proxy_set_header Connection "upgrade";
        proxy_set_header Host \$host;
        proxy_set_header X-Real-IP \$remote_addr;
        proxy_set_header X-Forwarded-For \$proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto \$scheme;
    }
}
EOF

# Enable nginx site
sudo ln -sf /etc/nginx/sites-available/contextlite-demo /etc/nginx/sites-enabled/
sudo rm -f /etc/nginx/sites-enabled/default
sudo nginx -t
sudo systemctl enable nginx
sudo systemctl restart nginx

# Install SSL certificate
echo "🔒 Installing SSL certificate..."
if [[ "$DOMAIN" != "demo.contextlite.com" ]]; then
    echo "⚠️  Skipping SSL setup for non-production domain: $DOMAIN"
    echo "💡 Run: sudo certbot --nginx -d $DOMAIN manually after DNS setup"
else
    sudo certbot --nginx -d $DOMAIN --email $EMAIL --agree-tos --non-interactive --redirect
fi

# Create monitoring script
echo "📊 Creating monitoring script..."
sudo tee /opt/contextlite-demo/bin/monitor.sh > /dev/null <<'EOF'
#!/bin/bash

# ContextLite Demo Server Monitoring Script

echo "🖥️  ContextLite Demo Server Status"
echo "📅 $(date)"
echo ""

echo "💾 Disk Usage:"
df -h / | tail -1
echo ""

echo "🧠 Memory Usage:"
free -h | grep -E "(Mem|Swap)"
echo ""

echo "⚡ CPU Usage:"
top -bn1 | grep "Cpu(s)" | awk '{print $2}' | sed 's/%us,//'
echo ""

echo "🐳 Docker Containers:"
docker ps --format "table {{.Names}}\t{{.Status}}\t{{.Ports}}"
echo ""

echo "🌐 Nginx Status:"
sudo systemctl is-active nginx
echo ""

echo "🔐 SSL Certificate:"
if [ -f /etc/letsencrypt/live/demo.contextlite.com/fullchain.pem ]; then
    openssl x509 -in /etc/letsencrypt/live/demo.contextlite.com/fullchain.pem -noout -dates
else
    echo "SSL certificate not found"
fi
echo ""

echo "📈 Active Connections:"
ss -tuln | grep -E "(80|443|8080)"
echo ""

echo "🛡️  Fail2ban Status:"
sudo fail2ban-client status
EOF

chmod +x /opt/contextlite-demo/bin/monitor.sh

# Create backup script
echo "💾 Creating backup script..."
sudo tee /opt/contextlite-demo/bin/backup.sh > /dev/null <<'EOF'
#!/bin/bash

# ContextLite Demo Backup Script

BACKUP_DIR="/opt/contextlite-demo/backups"
DATE=$(date +%Y%m%d_%H%M%S)

mkdir -p $BACKUP_DIR

echo "📦 Creating backup: $DATE"

# Backup database
if [ -f /opt/contextlite-demo/data/contextlite.db ]; then
    echo "💾 Backing up database..."
    sqlite3 /opt/contextlite-demo/data/contextlite.db ".backup $BACKUP_DIR/contextlite_$DATE.db"
fi

# Backup configuration
echo "⚙️  Backing up configuration..."
tar czf $BACKUP_DIR/config_$DATE.tar.gz -C /opt/contextlite-demo config/

# Cleanup old backups (keep 7 days)
find $BACKUP_DIR -name "*.db" -mtime +7 -delete
find $BACKUP_DIR -name "*.tar.gz" -mtime +7 -delete

echo "✅ Backup complete: $BACKUP_DIR"
EOF

chmod +x /opt/contextlite-demo/bin/backup.sh

# Create daily backup cron job
echo "⏰ Setting up daily backups..."
(crontab -l 2>/dev/null; echo "0 2 * * * /opt/contextlite-demo/bin/backup.sh >> /opt/contextlite-demo/logs/backup.log 2>&1") | crontab -

# Configure log rotation
echo "📋 Configuring log rotation..."
sudo tee /etc/logrotate.d/contextlite-demo > /dev/null <<EOF
/opt/contextlite-demo/logs/*.log {
    daily
    missingok
    rotate 30
    compress
    delaycompress
    notifempty
    copytruncate
}
EOF

# Create health check endpoint
echo "❤️  Creating health check..."
mkdir -p /opt/contextlite-demo/web/static
echo '{"status":"ok","timestamp":"'$(date -Iseconds)'","server":"contextlite-demo"}' > /opt/contextlite-demo/web/static/health.json

# Summary
echo ""
echo "🎉 ContextLite Demo Server Provisioning Complete!"
echo ""
echo "✅ Server Security:"
echo "   - UFW firewall configured (SSH, HTTP, HTTPS only)"
echo "   - fail2ban active with custom rules"
echo "   - SSH hardened (no root, key-only auth)"
echo "   - Automatic security updates enabled"
echo ""
echo "✅ Web Server:"
echo "   - nginx configured with rate limiting"
echo "   - SSL certificate installed (if domain ready)"
echo "   - Security headers enabled"
echo "   - WebSocket proxy ready"
echo ""
echo "✅ Monitoring:"
echo "   - System monitoring script: /opt/contextlite-demo/bin/monitor.sh"
echo "   - Daily database backups scheduled"
echo "   - Log rotation configured"
echo "   - Health check endpoint: /static/health.json"
echo ""
echo "✅ Docker Ready:"
echo "   - Docker service enabled and running"
echo "   - ContextLite user added to docker group"
echo ""
echo "🚀 Next Steps:"
echo "   1. Upload ContextLite binary to /opt/contextlite-demo/bin/"
echo "   2. Run data ingestion pipeline"
echo "   3. Deploy web terminal application"
echo "   4. Test all endpoints and security"
echo ""
echo "🌐 Server ready for: $DOMAIN"
echo "📧 SSL contact: $EMAIL"
echo ""
echo "Happy deploying! 🚀"
