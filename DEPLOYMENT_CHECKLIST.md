# ContextLite Demo Server Deployment Checklist

## 🎯 **Goal**: Deploy live demo at demo.contextlite.com for your sales page

### **📋 Pre-Deployment Checklist**

#### **1. Server Setup** ✅
- [ ] Ubuntu 22.04 server provisioned (8GB RAM, 4 cores, 200GB storage)
- [ ] Server has public IP address: `_________________`
- [ ] SSH access working: `ssh user@your-server-ip`
- [ ] Server can install packages (apt update works)

#### **2. Domain Configuration** ✅  
- [ ] DNS A record set: `demo.contextlite.com` → Server IP
- [ ] DNS propagation complete (test with `nslookup demo.contextlite.com`)
- [ ] SSL email ready: `admin@contextlite.com` (or your preferred email)

#### **3. ContextLite Binary** ✅
- [ ] Latest ContextLite binary available at: `../build/contextlite`
- [ ] OR binary download URL ready: `https://github.com/...`
- [ ] Binary has execute permissions and works

---

## 🚀 **Deployment Steps**

### **Step 1: Connect to Server**
```bash
# SSH to your server
ssh user@YOUR_SERVER_IP

# Verify you're on Ubuntu 22.04
lsb_release -a
```

### **Step 2: Clone Repository**
```bash
# Clone ContextLite with demo scripts
git clone https://github.com/Michael-A-Kuykendall/contextlite.git
cd contextlite

# Verify scripts are present
ls -la scripts/
```

### **Step 3: Run Deployment**
```bash
# Deploy complete demo server (this takes 45-60 minutes)
./scripts/production-deploy.sh demo.contextlite.com admin@contextlite.com

# Optional: Include binary URL if not in ../build/
# ./scripts/production-deploy.sh demo.contextlite.com admin@contextlite.com https://releases.contextlite.com/contextlite-linux-amd64
```

### **Step 4: Monitor Deployment**
```bash
# Watch the deployment progress
# The script will show:
# 🏗️  Phase 1: Server provisioning (10 min)
# 📊 Phase 2: Data ingestion (30-45 min) 
# 🖥️  Phase 3: Web terminal (10 min)
# 🌐 Phase 4: Production config (5 min)
```

### **Step 5: Verify Deployment**
```bash
# Check services are running
sudo systemctl status nginx
sudo systemctl status contextlite-terminal

# Test endpoints
curl http://localhost/health
curl http://localhost/api/stats

# Test SSL (if domain ready)
curl https://demo.contextlite.com/health
```

---

## ✅ **Post-Deployment Testing**

### **1. Basic Functionality**
- [ ] Visit `https://demo.contextlite.com` 
- [ ] Page loads with statistics (2.4M+ files, etc.)
- [ ] Terminal opens in browser
- [ ] Can type commands in terminal

### **2. Core Commands**
Test these commands in the web terminal:
- [ ] `contextlite help` → Shows command list
- [ ] `contextlite search "React component"` → Returns results in <1s
- [ ] `contextlite stats` → Shows database statistics  
- [ ] `contextlite explain kubernetes/cmd` → Provides code analysis

### **3. Performance & Security**
- [ ] Search responses under 500ms
- [ ] Session timeout works (15 minutes)
- [ ] SSL certificate valid and working
- [ ] Rate limiting prevents abuse
- [ ] Mobile responsive design works

### **4. Analytics & Monitoring**
- [ ] Health check: `https://demo.contextlite.com/health`
- [ ] Stats API: `https://demo.contextlite.com/api/stats`
- [ ] Server monitoring: `/opt/contextlite-demo/bin/monitor.sh`

---

## 🌐 **Website Integration Steps**

### **1. Update Sales Page (`/sell`)**
Add the demo section from `WEBSITE_DEMO_CONTENT.md`:
- [ ] Copy demo section HTML to sales page
- [ ] Update demo URL to your domain
- [ ] Test "Try Live Demo" button works
- [ ] Add demo kit section for sales team

### **2. Create Demo Page (`/demo`)**
- [ ] Create new `/demo` page with standalone content
- [ ] Use full HTML from `WEBSITE_DEMO_CONTENT.md`
- [ ] Update all demo links to point to your server
- [ ] Test mobile responsiveness

### **3. Add Demo Links Throughout Site**
- [ ] Homepage hero section
- [ ] Navigation menu ("Demo" link)
- [ ] Email signatures  
- [ ] Social media profiles
- [ ] Documentation pages

---

## 📊 **Success Metrics to Track**

### **Technical Metrics**
- [ ] Demo uptime > 99%
- [ ] Average response time < 500ms
- [ ] SSL certificate auto-renewal working
- [ ] Daily backups running

### **Business Metrics**
- [ ] Demo sessions per day
- [ ] Average session duration (target: 5+ minutes)
- [ ] Most popular commands
- [ ] Demo → contact/download conversion rate

---

## 🛠️ **Maintenance & Troubleshooting**

### **Daily Checks**
```bash
# Run on server daily
/opt/contextlite-demo/bin/monitor.sh
/opt/contextlite-demo/bin/monitor-terminal.sh
```

### **Common Issues & Fixes**

**Terminal not responding:**
```bash
sudo systemctl restart contextlite-terminal
sudo journalctl -u contextlite-terminal -f
```

**SSL certificate expired:**
```bash
sudo certbot --nginx -d demo.contextlite.com
```

**High resource usage:**
```bash
# Check active sessions
/opt/contextlite-demo/bin/monitor.sh
# Clean up old sessions if needed
docker container prune
```

**Data corruption:**
```bash
# Restore from backup
/opt/contextlite-demo/bin/backup.sh
```

---

## 📞 **Need Help?**

### **Self-Service**
- **Documentation**: All scripts include detailed help
- **Logs**: Check `/opt/contextlite-demo/logs/`
- **Monitoring**: Use built-in monitoring scripts

### **Support**
- **Email**: support@contextlite.com
- **Issue Tracking**: GitHub issues on contextlite repo
- **Emergency**: If demo is down during important sales call

---

## 🎉 **Launch Checklist**

Before announcing your demo publicly:

- [ ] **Technical**: All tests pass, monitoring active
- [ ] **Content**: Website updated with demo links
- [ ] **Sales**: Team trained on demo flow and commands
- [ ] **Analytics**: Tracking set up for conversion metrics
- [ ] **Backup**: Verified backup and recovery procedures

### **Ready to Launch! 🚀**

Once everything is checked:
1. **Announce** demo on website and social media
2. **Train** sales team on demo commands  
3. **Monitor** usage and performance
4. **Iterate** based on user feedback
5. **Scale** if traffic increases

**Result**: Professional demo that converts prospects into customers by showing real ContextLite performance on production-scale codebases.

---

*Time to deployment: 60 minutes*  
*Time to ROI: First qualified lead from demo*
