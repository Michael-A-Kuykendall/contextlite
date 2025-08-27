# 🎯 Abandoned Cart Recovery - Testing & Monitoring Guide

## 🚀 **DEPLOYMENT STATUS CHECK**

### **1. Verify Railway Deployment**
```bash
# Check if basic health is working
curl https://contextlite-production.up.railway.app/health

# Test if abandoned cart endpoints are live (should return stats, not 404)
curl https://contextlite-production.up.railway.app/abandoned-carts/stats

# If still getting 404, Railway is rebuilding. Check deployment:
# Go to: https://railway.app → Your Project → Deployments tab
```

### **2. Force Railway Redeploy** (if needed)
Railway should auto-deploy from the git push, but if not:
1. Go to https://railway.app
2. Find your contextlite project  
3. Go to "Deployments" tab
4. Click "Deploy Latest" or trigger manual redeploy

---

## 📧 **EMAIL SYSTEM TESTING**

### **Test Email Configuration**
```bash
# Test if SMTP is configured correctly
curl -X POST https://contextlite-production.up.railway.app/test-email

# Expected response:
# {"success": true, "message": "Test email sent successfully"}
```

### **Manual Email Test** 
Create a test abandoned cart and trigger emails:
```bash
# Manually process abandoned carts (sends any pending emails)
curl -X POST https://contextlite-production.up.railway.app/abandoned-carts/process

# Check response:
# {"success": true, "message": "Abandoned cart processing completed"}
```

---

## 👁️ **MONITORING ABANDONED CARTS**

### **View Current Statistics**
```bash
# Get abandoned cart stats for last 30 days
curl "https://contextlite-production.up.railway.app/abandoned-carts/stats?days=30"

# Expected response when working:
# {
#   "success": true,
#   "stats": {
#     "total_abandoned_carts": 0,
#     "recovered_carts": 0,
#     "recovery_rate_percent": 0,
#     "total_abandoned_value": 0,
#     "recovered_value": 0
#   }
# }
```

### **Different Time Periods**
```bash
# Last 7 days
curl "https://contextlite-production.up.railway.app/abandoned-carts/stats?days=7"

# Last 24 hours  
curl "https://contextlite-production.up.railway.app/abandoned-carts/stats?days=1"

# All time (default 30 days)
curl "https://contextlite-production.up.railway.app/abandoned-carts/stats"
```

---

## 📨 **HOW TO SEE SENT EMAILS**

### **Option 1: Check Your Email Inbox**
- Emails are sent TO the customer who abandoned cart
- Emails are sent FROM your configured FROM_EMAIL address
- **You won't see them unless you create test abandoned carts with your own email**

### **Option 2: Email Logging** (Add this if needed)
Currently emails are sent but not logged. To track sent emails, we can add:
```bash
# Check server logs for email activity (if Railway provides log access)
# Look for messages like: "Sent reminder email to customer@email.com"
```

### **Option 3: Create Test Abandoned Cart**
```bash
# To see actual emails, create a test checkout:
# 1. Go to your Stripe payment link
# 2. Enter YOUR email address
# 3. Close browser without paying
# 4. Wait 1 hour → you'll receive reminder email
# 5. Check: curl "https://contextlite-production.up.railway.app/abandoned-carts/stats?days=1"
```

---

## 🔥 **MASS EMAIL ALL CURRENT ABANDONED CARTS**

### **Trigger Mass Processing**
```bash
# This processes ALL pending abandoned carts and sends appropriate emails
curl -X POST https://contextlite-production.up.railway.app/abandoned-carts/process

# Response indicates how many were processed:
# {"success": true, "message": "Abandoned cart processing completed"}
```

### **How Mass Processing Works:**
1. **Finds all abandoned carts** in database
2. **Checks email sequence status** for each cart
3. **Sends appropriate email** based on timing:
   - **1 hour after abandonment**: Reminder email
   - **24 hours after abandonment**: Benefits comparison email  
   - **72 hours after abandonment**: Discount offer email
4. **Updates email sequence counter** to prevent duplicates
5. **Logs all email activity**

### **Mass Email Scenarios:**
```bash
# Scenario 1: First time running system
# - Processes any existing abandoned carts from Stripe
# - Sends appropriate email based on how long ago cart was abandoned

# Scenario 2: Regular operation  
# - System runs automatically every hour
# - Manual trigger processes any pending immediately

# Scenario 3: After system downtime
# - Catch up on any missed email sequences
# - Send accumulated abandoned cart emails
```

---

## 🎯 **VERIFICATION CHECKLIST**

### **System Health:**
- [ ] Health endpoint responds: `curl https://contextlite-production.up.railway.app/health`
- [ ] Abandoned cart stats work: `curl https://contextlite-production.up.railway.app/abandoned-carts/stats`
- [ ] Email test works: `curl -X POST https://contextlite-production.up.railway.app/test-email`
- [ ] Mass processing works: `curl -X POST https://contextlite-production.up.railway.app/abandoned-carts/process`

### **Email Configuration:**
- [ ] SMTP settings configured in Railway environment variables
- [ ] FROM_EMAIL set to your business email
- [ ] Test email delivers successfully
- [ ] Email templates include ContextLite branding

### **Stripe Integration:**
- [ ] Stripe webhook includes `checkout.session.expired` event
- [ ] Webhook endpoint: `https://contextlite-production.up.railway.app/webhook/stripe`
- [ ] Webhook secret matches Railway environment variable
- [ ] Test abandoned checkout creates database record

---

## 🔍 **TROUBLESHOOTING**

### **If Endpoints Return 404:**
```bash
# Railway might still be deploying
# Check: https://railway.app → Your Project → Deployments
# Wait 2-5 minutes for rebuild to complete
```

### **If Email Test Fails:**
```bash
# Check Railway environment variables:
# SMTP_HOST, SMTP_PORT, SMTP_USER, SMTP_PASSWORD, FROM_EMAIL
# Verify SMTP credentials work
```

### **If No Abandoned Carts Appear:**
```bash
# 1. Verify Stripe webhook is receiving events
# 2. Create test checkout and abandon it
# 3. Check webhook logs in Stripe dashboard
# 4. Verify webhook secret matches Railway env var
```

### **If Emails Not Sending:**
```bash
# 1. Test SMTP configuration: curl -X POST .../test-email
# 2. Check Railway logs for email errors
# 3. Verify FROM_EMAIL domain has SPF/DKIM records
# 4. Check spam folder for test emails
```

---

## 📊 **SUCCESS METRICS TO TRACK**

### **Daily Checks:**
```bash
# Check abandoned cart stats
curl "https://contextlite-production.up.railway.app/abandoned-carts/stats?days=1"

# Manually trigger processing
curl -X POST https://contextlite-production.up.railway.app/abandoned-carts/process
```

### **Weekly Analysis:**
```bash
# Get 7-day performance
curl "https://contextlite-production.up.railway.app/abandoned-carts/stats?days=7"

# Calculate recovery rate and revenue impact
```

### **What to Expect:**
- **First week**: 5-15 abandoned carts (from 9,891+ downloads)
- **Recovery rate**: 15-25% (2-4 recovered carts)
- **Revenue**: $200-400 additional
- **Email deliverability**: >95% successful sends

---

## 🚀 **NEXT STEPS**

1. **Verify deployment**: Check health and stats endpoints
2. **Test email system**: Send test email and verify delivery
3. **Create test abandoned cart**: Use your own email to see the flow
4. **Monitor first week**: Track abandoned carts and recovery rates
5. **Optimize emails**: Improve subject lines and content based on performance

The system is designed to work automatically once deployed! 🎉
