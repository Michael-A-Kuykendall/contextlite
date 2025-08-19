# 🔗 ContextLite Product Site - Critical Links Migration Guide

**Date**: August 19, 2025  
**Purpose**: Transfer all important links from current site to new product site

---

## 🎯 CRITICAL STRIPE PAYMENT LINKS

### Stripe Configuration
- **Live Publishable Key**: `pk_live_51RwqRv1g5xy1QMw5P01z0dVCQWSnSqc2VQEfmscQyrfy2LAe1Un2gqE3b3kmxxxFlP8XyosxJVu2K1p81ShmgyDw009RQ8xU6Q`
- **Professional License Price ID**: `price_1Rx9ed1g5xy1QMw5YnahvAPg`
- **Payment Mode**: `payment` (one-time)
- **Success URL**: `/success.html`
- **Cancel URL**: `/index.html`

### Payment Buttons Implementation
```javascript
// Stripe Integration Code
const stripe = Stripe('pk_live_51RwqRv1g5xy1QMw5P01z0dVCQWSnSqc2VQEfmscQyrfy2LAe1Un2gqE3b3kmxxxFlP8XyosxJVu2K1p81ShmgyDw009RQ8xU6Q');

function handlePurchase() {
  stripe.redirectToCheckout({
    lineItems: [{
      price: 'price_1Rx9ed1g5xy1QMw5YnahvAPg',
      quantity: 1,
    }],
    mode: 'payment',
    successUrl: window.location.origin + '/success.html',
    cancelUrl: window.location.origin + '/index.html',
  });
}
```

---

## 💰 PRICING STRUCTURE

### Professional License
- **Price**: $99 (one-time payment)
- **Stripe Price ID**: `price_1Rx9ed1g5xy1QMw5YnahvAPg`
- **Features**: 
  - Unlimited workspaces
  - Unlimited documents
  - Advanced SMT optimization
  - Local binary deployment
  - Commercial usage rights

### Enterprise License
- **Contact**: Custom pricing (no Stripe integration yet)
- **Features**:
  - Everything in Professional
  - Team deployment tools
  - Priority support
  - Custom integrations
  - SLA guarantees

---

## 🌐 OFFICIAL DOMAIN LINKS

### Primary Domains
- **Main Site**: `https://contextlite.com`
- **Documentation**: `https://docs.contextlite.com`
- **Download Page**: `https://contextlite.com/download`

### Community Links
- **Discord**: `https://discord.gg/contextlite`
- **GitHub Issues**: `https://github.com/Michael-A-Kuykendall/contextlite/issues`

---

## 📦 PACKAGE DISTRIBUTION LINKS

### GitHub Repository
- **Main Repo**: `https://github.com/Michael-A-Kuykendall/contextlite`
- **Clone URL**: `git clone https://github.com/Michael-A-Kuykendall/contextlite.git`
- **Releases**: `https://github.com/Michael-A-Kuykendall/contextlite/releases`
- **Latest Binary**: `https://github.com/Michael-A-Kuykendall/contextlite/releases/latest/download/contextlite_linux_amd64`

### Package Managers
- **PyPI**: `https://pypi.org/project/contextlite/`
- **PyPI Badge**: `https://badge.fury.io/py/contextlite.svg`
- **npm**: `https://www.npmjs.com/package/contextlite`
- **npm Badge**: `https://badge.fury.io/js/contextlite.svg`
- **VS Code Extension**: Visual Studio Marketplace (ID to be confirmed)
- **Rust Crates**: `https://crates.io/crates/contextlite` (when published)

---

## 🔧 TECHNICAL INTEGRATION ENDPOINTS

### Local Development
- **Default Server**: `http://localhost:8080`
- **Health Check**: `http://localhost:8080/health`
- **API Base**: `http://localhost:8080/api/v1`

### API Endpoints
```bash
# Core Context Assembly
POST http://localhost:8080/api/v1/context/assemble

# Document Management  
POST http://localhost:8080/api/v1/documents
GET  http://localhost:8080/api/v1/documents/search

# Workspace Management
GET  http://localhost:8080/api/v1/weights
POST http://localhost:8080/api/v1/weights/update

# System Information
GET  http://localhost:8080/api/v1/storage/info
GET  http://localhost:8080/api/v1/smt/stats
GET  http://localhost:8080/api/v1/cache/stats
```

---

## 📊 PERFORMANCE BADGES & METRICS

### Badge URLs
- **License**: `https://img.shields.io/badge/License-MIT-yellow.svg`
- **Python Versions**: `https://img.shields.io/pypi/pyversions/contextlite.svg`
- **Node Versions**: `https://img.shields.io/node/v/contextlite.svg`

### Key Performance Numbers
- **Query Speed**: 0.3-0.6ms per query
- **Processing Rate**: 2,406 files/second
- **Test Coverage**: 87.7%
- **Scale Test**: 12GB codebase (190,000+ files)
- **Developer Rating**: ⭐⭐⭐⭐⭐ 4.9/5

---

## 🛠️ VS CODE EXTENSION SPECIFICS

### Extension Details
- **Marketplace**: Visual Studio Code Marketplace
- **Install Command**: Extensions > Search "ContextLite"
- **GitHub Issues**: `https://github.com/Michael-A-Kuykendall/contextlite/issues`
- **Repository**: Same as main repo

### Requirements
1. Install ContextLite binary from `https://contextlite.com/download`
2. Install VS Code extension from marketplace
3. Configure workspace settings

---

## 🔐 LICENSE LINKS

### Open Source
- **MIT License**: `https://opensource.org/licenses/MIT`
- **Repository License**: Located in `/LICENSE` file

### Commercial
- **Professional License**: Included with $99 purchase
- **Enterprise License**: Custom terms via contact

---

## 📱 SOCIAL PROOF ELEMENTS

### Testimonials (Reference)
- **Senior Developer** (AI Startup, Series A): Context retrieval 45ms → 0.4ms
- **Full-Stack Engineer** (FinTech): Accuracy improvement + $400/month savings  
- **Tech Lead** (Gaming): Performance boost + development velocity

### Performance Claims
- **50-100x faster** than vector databases
- **$300-500/month** cloud hosting savings
- **Zero dependencies** - single binary deployment
- **100% local** - no data leaves your machine

---

## ⚡ CRITICAL MIGRATION CHECKLIST

### Must Transfer
- [ ] Stripe live publishable key
- [ ] Professional license price ID (`price_1Rx9ed1g5xy1QMw5YnahvAPg`)
- [ ] Success/cancel page URLs
- [ ] Payment button event handlers
- [ ] All GitHub repository links
- [ ] Package manager URLs
- [ ] Community Discord link
- [ ] Performance metrics & badges

### Must Update
- [ ] Domain references (`contextlite.com`)
- [ ] Documentation URLs (`docs.contextlite.com`)
- [ ] Download page links (`contextlite.com/download`)
- [ ] Support/contact information

### Must Test
- [ ] Stripe payment flow (Professional $99)
- [ ] GitHub repository access
- [ ] Package download links
- [ ] VS Code extension install
- [ ] API endpoint documentation

---

## 🚨 SECURITY NOTES

### Public Information (Safe to Migrate)
- Stripe publishable key (starts with `pk_live_`)
- Price IDs (starts with `price_`)
- GitHub repository URLs
- Package manager links
- Performance metrics

### Private Information (DO NOT MIGRATE)
- Stripe secret keys
- Webhook secrets
- Private RSA keys
- Business strategy documents
- Internal performance details

---

**This document contains all critical links and configuration needed to migrate the ContextLite product site while maintaining full payment functionality and user experience.**
