# 🚀 ContextLite Deployment Guide

This directory contains **ONLY the essential workflows** for deploying ContextLite. All redundant and confusing workflows have been removed.

## 📋 **Available Workflows**

### 1. **`deploy-selective.yml`** ⭐ **PRIMARY DEPLOYMENT**
**Purpose:** Deploy to specific platforms selectively  
**Trigger:** Manual dispatch with platform selection  
**Best For:** Quick deployments, single platform updates, testing

**How to use:**
1. Go to **Actions** → **Selective Package Deployment**
2. Choose platforms (dropdown with common combinations)
3. Enter version (e.g., `1.0.47`)
4. Set `force_deploy` if overriding existing versions
5. Click **Run workflow**

**Supported Platforms:**
- ✅ **Chocolatey** (Windows package manager)
- ✅ **npm** (Node.js package manager) 
- ✅ **PyPI** (Python package manager)
- ✅ **Docker** (Container registry)
- ✅ **Crates** (Rust package manager)

### 2. **`publish-packages.yml`** 📦 **FULL DEPLOYMENT**
**Purpose:** Deploy to ALL supported platforms simultaneously  
**Trigger:** Git tag creation (e.g., `git tag v1.0.47`)  
**Best For:** Major releases, comprehensive deployment

**How to use:**
```bash
git tag v1.0.47
git push --tags
```

**Supported Platforms:** All 12+ package managers including Homebrew, AUR, Snap, GitHub Packages, etc.

### 3. **`simple-release.yml`** 📋 **GITHUB RELEASE ONLY**
**Purpose:** Create GitHub release with binaries  
**Trigger:** Git tag creation  
**Best For:** Binary-only releases, testing builds

## 🎯 **Recommended Usage Patterns**

### **For Chocolatey-only deployment:**
1. Use `deploy-selective.yml`
2. Select **"chocolatey"** from dropdown
3. Enter version
4. Run workflow

### **For testing multiple platforms:**
1. Use `deploy-selective.yml` 
2. Select **"chocolatey,npm,pypi"** combination
3. Monitor individual platform results

### **For major releases:**
1. Use `publish-packages.yml`
2. Create git tag: `git tag v1.0.47 && git push --tags`
3. All platforms deploy automatically

## 🔧 **Troubleshooting**

### **Common Issues:**

**"Version already exists":**
- Set `force_deploy: true` in selective deployment
- Or increment version number

**"Missing secrets":**
- Check repository secrets are configured
- Each platform needs specific API tokens

**"Binary not found":**
- Ensure `build-binaries` job completed successfully
- Check GitHub release artifacts were created

### **Monitoring Deployments:**

1. **GitHub Actions tab** - See workflow status
2. **Platform dashboards** - Check individual package managers
3. **Email notifications** - Chocolatey moderation emails

## 📁 **Files in this directory:**

```
.github/workflows/
├── deploy-selective.yml    ⭐ Primary: Selective platform deployment
├── publish-packages.yml    📦 Full: All platforms at once  
└── simple-release.yml      📋 Basic: GitHub release only
```

## ✅ **What was cleaned up:**

**Removed redundant workflows:**
- ❌ `publish-npm-only.yml` (replaced by selective deployment)
- ❌ `quick-deploy.yml` (replaced by better selective deployment)  
- ❌ `test-homebrew.yml` (testing-specific, not needed)
- ❌ `release.yml` (was disabled, caused conflicts)

**Result:** Clear, simple deployment process with no confusion.
