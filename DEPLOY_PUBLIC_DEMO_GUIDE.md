# ContextLite Public Demo Server - Quick Start Guide

## 🎯 **One-Command Deployment**

Deploy a complete ContextLite public demo server with real data and secure web terminal:

```bash
# Complete deployment (replace with your domain and email)
./scripts/production-deploy.sh demo.contextlite.com admin@contextlite.com

# Or with custom ContextLite binary URL
./scripts/production-deploy.sh demo.contextlite.com admin@contextlite.com https://github.com/user/repo/releases/download/v1.0.0/contextlite-linux-amd64
```

## 📋 **What Gets Deployed**

### **🏗️ Production Server**
- **Ubuntu 22.04** with security hardening
- **Docker** container support
- **nginx** with SSL and rate limiting
- **fail2ban** intrusion prevention
- **UFW firewall** (ports 22, 80, 443 only)

### **📊 Real Data Pipeline**
- **7 Major Repositories**: VSCode, React, Go, Rust, Node.js, TensorFlow, Kubernetes
- **~3.8GB Source Code**: Real production codebases
- **2.4M+ Files Indexed**: Comprehensive search database
- **Multiple Languages**: JavaScript, TypeScript, Go, Rust, Python, C++

### **🖥️ Secure Web Terminal**
- **xterm.js Interface**: Full terminal experience in browser
- **Session Management**: 15-minute secure sessions
- **Rate Limiting**: Abuse prevention (10 req/min per IP)
- **Command Validation**: Only ContextLite commands allowed
- **Real-time Output**: Live streaming of ContextLite results

### **🔒 Security Features**
- **Sandboxed Execution**: Docker containers with resource limits
- **Input Sanitization**: Command validation and filtering
- **Session Timeouts**: Automatic cleanup after 15 minutes
- **SSL Certificates**: Let's Encrypt automated setup
- **Monitoring**: Health checks and performance tracking

## 🚀 **Manual Step-by-Step Deployment**

If you prefer to run each phase separately:

### **1. Server Provisioning** (5 minutes)
```bash
./scripts/provision-server.sh demo.contextlite.com admin@contextlite.com
```

### **2. Data Ingestion** (30-45 minutes)
```bash
./scripts/setup-data-pipeline.sh
```

### **3. Web Terminal** (10 minutes)
```bash
./scripts/deploy-web-terminal.sh
```

## 🎮 **User Experience**

Once deployed, users can:

1. **Visit** `https://demo.contextlite.com`
2. **See** real-time statistics of indexed repositories
3. **Open** secure web terminal in browser
4. **Run** ContextLite commands on real production code:
   - `contextlite search "React component"`
   - `contextlite search "async function"`
   - `contextlite explain kubernetes/cmd/kubectl`
   - `contextlite analyze tensorflow/python`
   - `contextlite stats`

## 📊 **Monitoring & Management**

### **Service Status**
```bash
# Overall system health
/opt/contextlite-demo/bin/monitor.sh

# Web terminal specific
/opt/contextlite-demo/bin/monitor-terminal.sh

# View live logs
sudo journalctl -u contextlite-terminal -f
```

### **Backup & Maintenance**
```bash
# Manual backup
/opt/contextlite-demo/bin/backup.sh

# Restart services
sudo systemctl restart contextlite-terminal
sudo systemctl reload nginx
```

## 🌐 **Domain Setup**

### **DNS Configuration**
Point your domain's A record to the server IP:
```
demo.contextlite.com.  300  IN  A  YOUR_SERVER_IP
```

### **SSL Certificate Setup**
If domain isn't ready during deployment, run SSL setup manually:
```bash
sudo certbot --nginx -d demo.contextlite.com
```

## 🔧 **Troubleshooting**

### **Common Issues**

**Terminal not responding:**
```bash
sudo systemctl status contextlite-terminal
sudo systemctl restart contextlite-terminal
```

**SSL certificate issues:**
```bash
sudo nginx -t
sudo certbot --nginx -d your-domain.com
```

**Data ingestion problems:**
```bash
tail -f /opt/contextlite-demo/data/logs/ingestion.log
```

**Performance issues:**
```bash
htop
df -h
/opt/contextlite-demo/bin/monitor.sh
```

## 📈 **Success Metrics**

### **Technical Targets**
- ✅ **Response Time**: <500ms average query time
- ✅ **Concurrent Users**: 25+ simultaneous sessions
- ✅ **Uptime**: 99.9% availability
- ✅ **Security**: Zero incidents

### **Business Goals**
- 🎯 **Usage**: 1000+ demo sessions per month
- 🎯 **Conversion**: 15%+ demo-to-download rate  
- 🎯 **Engagement**: 5+ minutes average session
- 🎯 **Growth**: Viral sharing and testimonials

## 🎉 **Expected Results**

After successful deployment:

- **Public URL**: https://demo.contextlite.com
- **Real Performance**: 0.3ms search times on 3.8GB+ codebase
- **Professional Experience**: Beautiful web interface with terminal
- **Viral Potential**: Developers sharing impressive speed demos
- **Lead Generation**: Qualified prospects experiencing value
- **Competitive Advantage**: Proving superiority over Vector RAG

---

## 🚀 **Ready to Deploy?**

```bash
# Download to your Ubuntu server
git clone https://github.com/Michael-A-Kuykendall/contextlite.git
cd contextlite

# Run complete deployment
./scripts/production-deploy.sh demo.contextlite.com your-email@domain.com

# Watch the magic happen! ✨
```

**Result**: A powerful public demonstration that converts visitors into ContextLite customers through hands-on experience with real, large-scale codebases.
