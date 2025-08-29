# GoReleaser Deployment Requirements & Fixes

## 🚨 CURRENT STATUS
- **Workflow Status**: FAILED at Snapcraft setup
- **Root Cause**: Missing/incorrect authentication secrets
- **Impact**: NO platforms deployed (GoReleaser never ran)

## 🔧 IMMEDIATE FIXES APPLIED

### 1. Fixed Snapcraft Authentication
- **Issue**: `--with` flag deprecated in snapcraft 8.11.2
- **Fix**: Updated to use `SNAPCRAFT_STORE_CREDENTIALS` environment variable
- **Status**: ✅ Code updated (conditional execution)

## 📋 SECRETS YOU NEED TO ADD TO GITHUB

Go to: `https://github.com/Michael-A-Kuykendall/contextlite/settings/secrets/actions`

### 🍫 **CHOCOLATEY_API_KEY** (PRIORITY 1 - Your Pain Point)
```bash
# Get your API key from: https://chocolatey.org/account
# Navigate to: Account → API Keys → Create New Key
# Set scope: "Push New Packages and Package Versions"
```

### 📦 **SNAPCRAFT_TOKEN** (PRIORITY 2 - Currently Blocking)
```bash
# Get token from: https://snapcraft.io/account/
# Or run locally: snapcraft export-login snapcraft-token.txt
# Copy the token content into GitHub secret
```

### 🏗️ **AUR_KEY** (PRIORITY 3 - Arch Linux)
```bash
# Generate GPG key for AUR:
gpg --full-generate-key
gpg --export-secret-keys YOUR_EMAIL > aur-private.key
# Add the private key content to GitHub secret
```

### 🏗️ **AUR_SSH_KEY** (PRIORITY 3 - Arch Linux)
```bash
# Generate SSH key for AUR:
ssh-keygen -t rsa -b 4096 -f ~/.ssh/aur
# Add private key content to GitHub secret
# Add public key to: https://aur.archlinux.org/account/
```

## 🎯 PLATFORM STATUS AFTER FIXES

### ✅ **WILL WORK IMMEDIATELY** (No secrets needed)
- GitHub Releases (uses GITHUB_TOKEN - already available)
- Docker GHCR (uses GITHUB_TOKEN - already available) 
- Homebrew (uses GITHUB_TOKEN to update tap repo)
- Scoop (uses GITHUB_TOKEN to update bucket repo)

### 🔑 **NEEDS SECRETS** (Will be skipped without them)
- Chocolatey → needs `CHOCOLATEY_API_KEY`
- Snapcraft → needs `SNAPCRAFT_TOKEN` 
- AUR → needs `AUR_KEY` + `AUR_SSH_KEY`

### 📦 **WRAPPER PLATFORMS** (Separate from GoReleaser)
- npm → uses your existing deploy.sh script
- PyPI → uses your existing deploy.sh script

## 🚀 TESTING STRATEGY

### Phase 1: Core Platforms (No secrets needed)
```bash
# This will work immediately after the fix:
git tag v1.1.21 && git push --tags
```
**Expected to work**: GitHub Releases, Docker, Homebrew, Scoop

### Phase 2: Add Chocolatey (Your priority)
1. Get Chocolatey API key
2. Add to GitHub secrets as `CHOCOLATEY_API_KEY`
3. Test with new tag

### Phase 3: Add remaining platforms
1. Get Snapcraft token → add as `SNAPCRAFT_TOKEN`
2. Generate AUR keys → add as `AUR_KEY` + `AUR_SSH_KEY`
3. Test with new tag

## 📝 STEP-BY-STEP CHOCOLATEY SETUP

### 1. Create Chocolatey Account
- Go to: https://chocolatey.org/
- Sign up or login

### 2. Generate API Key
- Navigate to: https://chocolatey.org/account
- Click "API Keys" 
- Click "Create New Key"
- Set description: "ContextLite Package Publishing"
- Set scope: "Push New Packages and Package Versions"
- Copy the generated key

### 3. Add to GitHub Secrets
- Go to: https://github.com/Michael-A-Kuykendall/contextlite/settings/secrets/actions
- Click "New repository secret"
- Name: `CHOCOLATEY_API_KEY`
- Value: [paste your API key]
- Click "Add secret"

### 4. Test Deployment
```bash
git tag v1.1.21 && git push --tags
```

## 🔍 MONITORING DEPLOYMENT

### Check Status
```bash
# Watch live: https://github.com/Michael-A-Kuykendall/contextlite/actions
# Or via API:
curl -s -H "Authorization: token $GITHUB_TOKEN" \
  "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/runs?per_page=1"
```

### Verify Chocolatey Package
```bash
# After successful deployment:
choco search contextlite
# Should show your package
```

## ⚡ QUICK WINS AVAILABLE NOW

Even without any secrets, you can immediately get:
- ✅ Professional GitHub releases with beautiful notes
- ✅ Cross-platform binaries (6 platforms)
- ✅ Docker images on GHCR
- ✅ Homebrew formula updates
- ✅ Scoop bucket updates

**Bottom Line**: The core GoReleaser functionality will work immediately. Chocolatey just needs your API key to complete your original pain point solution.
