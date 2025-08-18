# 🏢 BUSINESS ACCOUNT SETUP GUIDE - PHASE 3 EXECUTION
**Mission**: Create all required business accounts for 8-channel distribution  
**Goal**: Professional presence across all major package managers  
**Timeline**: Complete within 6-8 hours

---

## 📋 ACCOUNT CREATION CHECKLIST

### 1. 🐍 PyPI (Python Package Index) - DETAILED WALKTHROUGH
**URL**: https://pypi.org/account/register/  
**Priority**: HIGH - 3.8M+ weekly downloads for Python packages

#### Step 1: Create PyPI Account ✅ (COMPLETED)
- [x] Username: `contextlite` or `michael-kuykendall`
- [x] Email: Use primary business email
- [x] 2FA: Enable immediately

#### Step 2: Setup Trusted Publisher (DETAILED INSTRUCTIONS)

**What is Trusted Publisher?**
PyPI's trusted publisher feature allows GitHub Actions to publish packages without API tokens using OpenID Connect (OIDC). This is more secure than traditional API keys.

**Exact Steps:**

1. **Navigate to Publishing Settings**
   - Go to https://pypi.org/manage/account/publishing/
   - Or: Login → Account Settings → Publishing → "Add a new pending publisher"

2. **Fill Out the Form EXACTLY:**
   ```
   PyPI project name: contextlite
   Owner: Michael-A-Kuykendall
   Repository name: contextlite
   Workflow filename: release.yml
   Environment name: (leave empty for now, or use "pypi")
   ```

3. **Click "Add"**
   - This creates a "pending" trusted publisher
   - You don't need to create the package first
   - The first successful workflow run will create the package

#### Step 3: Create GitHub Release Workflow

**Create this file**: `.github/workflows/release.yml`

```yaml
name: Release to PyPI

on:
  release:
    types: [published]

jobs:
  pypi-publish:
    name: Upload release to PyPI
    runs-on: ubuntu-latest
    environment:
      name: pypi
      url: https://pypi.org/p/contextlite
    permissions:
      id-token: write  # IMPORTANT: this permission is mandatory for trusted publishing
    steps:
    - uses: actions/checkout@v4
    - name: Set up Python
      uses: actions/setup-python@v4
      with:
        python-version: '3.x'
    - name: Install dependencies
      run: |
        python -m pip install --upgrade pip
        pip install build twine
    - name: Build package
      run: python -m build
      working-directory: ./python-wrapper
    - name: Publish package distributions to PyPI
      uses: pypa/gh-action-pypi-publish@release/v1
      with:
        packages-dir: python-wrapper/dist/
```

#### Step 4: Test the Setup
1. Create a test release in GitHub (use version like `v0.1.0-test`)
2. Watch the GitHub Actions workflow run
3. Verify package appears on PyPI

**Troubleshooting Common Issues:**
- **Error: "Repository not found"** → Double-check owner/repo names match exactly
- **Error: "Workflow not found"** → Ensure `.github/workflows/release.yml` exists and is committed
- **Error: "Permission denied"** → Make sure `id-token: write` permission is set

---

### 2. 📦 npm (Node Package Manager) - DETAILED WALKTHROUGH
**URL**: https://www.npmjs.com/signup  
**Priority**: HIGH - 18M+ weekly downloads for CLI tools

#### Step 1: Create npm Account

1. **Go to**: https://www.npmjs.com/signup
2. **Fill out registration:**
   ```
   Username: contextlite (or michael-kuykendall if taken)
   Email: your-business-email@domain.com
   Password: [strong password]
   ```
3. **Verify email** (check inbox and click verification link)

#### Step 2: Enable Two-Factor Authentication

1. **Go to**: https://www.npmjs.com/settings/profile
2. **Click**: "Two-Factor Authentication" tab
3. **Choose**: "Authorization and Publishing" (most secure)
4. **Use your authenticator app** (Google Authenticator, Authy, etc.)
5. **Save backup codes** somewhere secure

#### Step 3: Create Organization (Optional but Recommended)

1. **Go to**: https://www.npmjs.com/org/create
2. **Organization name**: `contextlite`
3. **Choose plan**: Free plan is fine to start
4. **Add yourself** as owner

#### Step 4: Create Access Token for CI/CD

1. **Go to**: https://www.npmjs.com/settings/tokens
2. **Click**: "Generate New Token"
3. **Choose**: "Automation" token type
4. **Scope**: "Publish" permission
5. **Copy the token** (you'll only see it once)
6. **Add to GitHub Secrets**:
   - Go to your GitHub repo → Settings → Secrets and variables → Actions
   - Click "New repository secret"
   - Name: `NPM_TOKEN`
   - Value: [paste the token]

#### Step 5: Create GitHub Workflow for npm

**Create/update**: `.github/workflows/release.yml` (add this job)

```yaml
  npm-publish:
    name: Upload release to npm
    runs-on: ubuntu-latest
    needs: pypi-publish
    steps:
    - uses: actions/checkout@v4
    - name: Set up Node.js
      uses: actions/setup-node@v4
      with:
        node-version: '18'
        registry-url: 'https://registry.npmjs.org'
    - name: Install dependencies
      run: npm ci
      working-directory: ./node-wrapper
    - name: Build package
      run: npm run build
      working-directory: ./node-wrapper
    - name: Publish to npm
      run: npm publish
      working-directory: ./node-wrapper
      env:
        NODE_AUTH_TOKEN: ${{ secrets.NPM_TOKEN }}
```

---

### 3. 🦀 crates.io (Rust Package Registry) - DETAILED WALKTHROUGH
**URL**: https://crates.io/  
**Priority**: MEDIUM - 6B+ downloads per year, growing fast

#### Step 1: Create crates.io Account

1. **Go to**: https://crates.io/
2. **Click**: "Log in with GitHub" (easiest method)
3. **Authorize**: crates.io to access your GitHub account
4. **Complete profile**: Add name, email (will be public)

#### Step 2: Generate API Token

1. **Go to**: https://crates.io/settings/tokens
2. **Click**: "New Token"
3. **Name**: "GitHub Actions CI/CD"
4. **Scope**: Select all for full access (or just "publish-new" and "publish-update")
5. **Copy token** (save it immediately)

#### Step 3: Add Token to GitHub Secrets

1. **GitHub repo** → Settings → Secrets and variables → Actions
2. **New repository secret**:
   - Name: `CARGO_REGISTRY_TOKEN`
   - Value: [paste the crates.io token]

#### Step 4: Reserve Package Name

1. **Go to**: https://crates.io/crates/new
2. **Package name**: `contextlite`
3. **Check availability** (if taken, try `contextlite-cli` or `contextlite-rs`)
4. **Reserve it** by uploading a minimal package first

---

### 4. 🐳 Docker Hub - DETAILED WALKTHROUGH
**URL**: https://hub.docker.com/signup  
**Priority**: HIGH - Container distribution essential

#### Step 1: Create Docker Hub Account

1. **Go to**: https://hub.docker.com/signup
2. **Fill out form:**
   ```
   Docker ID: contextlite (or michaelkuykendall)
   Email: your-business-email@domain.com
   Password: [strong password]
   ```
3. **Verify email**

#### Step 2: Create Repository

1. **Click**: "Create Repository"
2. **Name**: `contextlite`
3. **Description**: "Fast, embedded context engine for AI applications"
4. **Visibility**: Public
5. **Click**: "Create"

#### Step 3: Generate Access Token

1. **Go to**: Account Settings → Security
2. **Click**: "New Access Token"
3. **Description**: "GitHub Actions CI/CD"
4. **Access permissions**: Read, Write, Delete
5. **Copy token**

#### Step 4: Add to GitHub Secrets

1. **GitHub repo** → Settings → Secrets and variables → Actions
2. **Add these secrets:**
   - `DOCKERHUB_USERNAME`: your Docker Hub username
   - `DOCKERHUB_TOKEN`: the access token you just created

---

### 5. 🛍️ VS Code Marketplace - DETAILED WALKTHROUGH
**URL**: https://marketplace.visualstudio.com/manage  
**Priority**: HIGH - 1B+ installs, direct developer reach

#### Step 1: Create Publisher Account

1. **Go to**: https://marketplace.visualstudio.com/manage
2. **Sign in** with Microsoft account (create one if needed)
3. **Create publisher**:
   ```
   Publisher name: contextlite
   Display name: ContextLite
   Description: AI-powered context management tools
   ```

#### Step 2: Generate Personal Access Token

1. **Go to**: https://dev.azure.com/
2. **User settings** → Personal access tokens
3. **New Token**:
   ```
   Name: VS Code Marketplace
   Organization: All accessible organizations
   Expiration: 1 year
   Scopes: Custom defined → Marketplace → Manage
   ```
4. **Copy token**

#### Step 3: Install vsce CLI Tool

```bash
npm install -g vsce
vsce login contextlite
# Enter the PAT when prompted
```

---

### 6. 🍺 Homebrew - DETAILED WALKTHROUGH
**URL**: No account needed, but formula submission required  
**Priority**: MEDIUM - macOS/Linux CLI distribution

#### Step 1: Understand the Process

Homebrew doesn't require an account, but you need to:
1. Create a formula file
2. Submit a pull request to homebrew-core
3. Or create your own tap (recommended for faster updates)

#### Step 2: Create Your Own Tap (Recommended)

1. **Create repo**: `homebrew-contextlite` on GitHub
2. **Structure**:
   ```
   homebrew-contextlite/
   └── Formula/
       └── contextlite.rb
   ```

#### Step 3: Formula Template

**File**: `Formula/contextlite.rb`

```ruby
class Contextlite < Formula
  desc "Fast, embedded context engine for AI applications"
  homepage "https://github.com/Michael-A-Kuykendall/contextlite"
  url "https://github.com/Michael-A-Kuykendall/contextlite/archive/v1.0.0.tar.gz"
  sha256 "YOUR_SHA256_HASH_HERE"
  license "MIT"

  depends_on "go" => :build

  def install
    system "go", "build", *std_go_args(ldflags: "-s -w"), "./cmd/contextlite"
  end

  test do
    system "#{bin}/contextlite", "--version"
  end
end
```

---

### 7. 🍫 Chocolatey (Windows) - DETAILED WALKTHROUGH
**URL**: https://community.chocolatey.org/account/Register  
**Priority**: MEDIUM - Windows CLI distribution

#### Step 1: Create Account

1. **Go to**: https://community.chocolatey.org/account/Register
2. **Fill out registration form**
3. **Verify email**

#### Step 2: Generate API Key

1. **Go to**: https://community.chocolatey.org/account
2. **Copy your API key**
3. **Add to GitHub secrets** as `CHOCOLATEY_API_KEY`

#### Step 3: Create Package Structure

```
chocolatey-package/
├── contextlite.nuspec
├── tools/
│   ├── chocolateyinstall.ps1
│   └── chocolateyuninstall.ps1
```

---

### 8. 🐙 GitHub Releases - DETAILED WALKTHROUGH
**Priority**: HIGH - Universal access, base for all other distributions

#### Step 1: Create Release Workflow

**File**: `.github/workflows/release.yml` (comprehensive version)

```yaml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  build:
    name: Build binaries
    runs-on: ubuntu-latest
    strategy:
      matrix:
        goos: [linux, windows, darwin]
        goarch: [amd64, arm64]
        exclude:
          - goos: windows
            goarch: arm64
    steps:
    - uses: actions/checkout@v4
    - name: Set up Go
      uses: actions/setup-go@v4
      with:
        go-version: '1.21'
    - name: Build binary
      env:
        GOOS: ${{ matrix.goos }}
        GOARCH: ${{ matrix.goarch }}
      run: |
        go build -ldflags "-s -w" -o contextlite-${{ matrix.goos }}-${{ matrix.goarch }}${{ matrix.goos == 'windows' && '.exe' || '' }} ./cmd/contextlite
    - name: Upload artifacts
      uses: actions/upload-artifact@v4
      with:
        name: contextlite-${{ matrix.goos }}-${{ matrix.goarch }}
        path: contextlite-*

  release:
    name: Create release
    runs-on: ubuntu-latest
    needs: build
    steps:
    - uses: actions/checkout@v4
    - name: Download all artifacts
      uses: actions/download-artifact@v4
    - name: Create Release
      uses: softprops/action-gh-release@v1
      with:
        files: |
          */contextlite-*
        generate_release_notes: true
      env:
        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
```

---

## 🎯 EXECUTION TIMELINE

### Phase 1 (Day 1): Core Accounts
- [x] PyPI account + trusted publisher
- [ ] npm account + automation token
- [ ] Docker Hub account + repository
- [ ] GitHub release workflow

### Phase 2 (Day 2): Extended Distribution
- [ ] VS Code Marketplace publisher
- [ ] crates.io account + token
- [ ] Homebrew tap setup
- [ ] Chocolatey account + package

### Phase 3 (Day 3): Testing & Polish
- [ ] Test all release workflows
- [ ] Verify package installations
- [ ] Update documentation
- [ ] Announce across channels

---

## 🔑 CREDENTIALS MANAGEMENT

### GitHub Secrets Needed:
```
NPM_TOKEN=npm_xxxxx...
CARGO_REGISTRY_TOKEN=crates_xxxxx...
DOCKERHUB_USERNAME=contextlite
DOCKERHUB_TOKEN=dckr_pat_xxxxx...
CHOCOLATEY_API_KEY=xxxxx...
VSCODE_PAT=xxxxx...
```

### Local Environment:
```bash
# VS Code Extension CLI
npm install -g vsce
vsce login contextlite

# Docker CLI
docker login

# Cargo (Rust)
cargo login [token]
```

---

**Next Step**: Complete npm setup following the detailed instructions above!
   - Email: Use primary business email
   - 2FA: Enable immediately

2. **Repository Setup**
   - Create `contextlite/contextlite` repository
   - Enable automated builds
   - Connect to GitHub repository

3. **Access Tokens**
   - Create access token with read/write permissions
   - Store in GitHub secrets as `DOCKER_TOKEN`

**Alternative**: Use GitHub Container Registry (already configured)

---

### 4. 🧠 JetBrains Marketplace
**URL**: https://plugins.jetbrains.com/  
**Priority**: MEDIUM - IntelliJ platform developer reach

#### Steps:
1. **JetBrains Account**
   - Use existing JetBrains account or create new
   - Verify email and enable 2FA

2. **Plugin Developer Agreement**
   - Review and accept JetBrains plugin terms
   - Setup vendor profile with business information

3. **Plugin Upload**
   - Use `jetbrains-plugin/` directory
   - Build with `gradle buildPlugin`
   - Upload via web interface or CI/CD

**API Keys Needed**: Plugin repository token

---

### 5. 💼 VS Code Marketplace (Azure DevOps)
**URL**: https://marketplace.visualstudio.com/manage  
**Priority**: HIGH - 150M+ VS Code users

#### Steps:
1. **Azure DevOps Organization**
   - Create organization: `contextlite` or `michael-kuykendall`
   - Enable required services
   - Setup billing if needed

2. **Publisher Profile**
   - Create publisher: `contextlite`
   - Add business information and branding
   - Verify domain ownership (optional)

3. **Personal Access Token**
   - Create PAT with Marketplace publish permissions
   - Store in GitHub secrets as `VSCE_TOKEN`

**Tools Needed**: `vsce` (Visual Studio Code Extensions CLI)

---

### 6. 🍫 Chocolatey
**URL**: https://community.chocolatey.org/account/Register  
**Priority**: MEDIUM - Windows package management

#### Steps:
1. **Chocolatey Account**
   - Username: `contextlite` or `michael.kuykendall`
   - Email: Use primary business email
   - Complete profile setup

2. **API Key Setup**
   - Generate API key from account settings
   - Store securely for package publishing
   - Test with `choco apikey`

3. **Package Submission**
   - Use `chocolatey/` directory
   - Submit via `choco push`
   - Monitor moderation queue

**API Keys Needed**: CHOCOLATEY_API_KEY

---

### 7. 📱 Snap Store (Canonical)
**URL**: https://login.ubuntu.com/  
**Priority**: LOW - Linux snap packages

#### Steps:
1. **Ubuntu One Account**
   - Create or use existing Ubuntu account
   - Enable 2FA for security

2. **Snap Store Developer**
   - Register as snap developer
   - Accept developer agreement
   - Setup publisher profile

3. **Package Upload**
   - Use `snapcraft` CLI
   - Build with `snapcraft`
   - Upload with `snapcraft upload`

**Tools Needed**: `snapcraft` CLI

---

### 8. 🍺 Homebrew (No Account Required)
**URL**: https://github.com/Homebrew/homebrew-core  
**Priority**: HIGH - macOS/Linux package management

#### Steps:
1. **Formula Creation**
   - Auto-generated by goreleaser ✅
   - Located in `dist/homebrew/contextlite.rb`

2. **Submission Process**
   - Fork `homebrew/homebrew-core`
   - Submit PR with formula
   - Follow Homebrew contribution guidelines

3. **Tap Repository** (Alternative)
   - Create `homebrew-tap` repository
   - Auto-publish via goreleaser
   - Users install with `brew tap`

**No API Keys Needed**

---

## 🔐 SECURITY CONSIDERATIONS

### API Key Management
1. **GitHub Secrets Storage**
   - Store all API keys in repository secrets
   - Use environment-specific secrets where possible
   - Never commit keys to repository

2. **Key Rotation Policy**
   - Rotate keys quarterly or after security incidents
   - Monitor key usage and access logs
   - Implement least-privilege access

### Account Security
1. **Two-Factor Authentication**
   - Enable 2FA on ALL accounts
   - Use authenticator apps, not SMS
   - Store backup codes securely

2. **Business Email**
   - Use dedicated business email for all accounts
   - Implement email security best practices
   - Monitor for suspicious activity

---

## 📊 EXECUTION TIMELINE

### Day 1 (2-3 hours): High Priority Accounts
1. PyPI account + trusted publisher setup
2. npm account + access token
3. VS Code Marketplace + Azure DevOps setup

### Day 2 (2-3 hours): Medium Priority Accounts  
4. Docker Hub account + access token
5. JetBrains Marketplace developer setup
6. Chocolatey account + API key

### Day 3 (1-2 hours): Final Setup
7. Snap Store developer registration
8. Test all account access and API keys
9. Update GitHub secrets with all tokens

---

## ✅ VERIFICATION CHECKLIST

Before proceeding to Phase 4:
- [ ] All 8 accounts created with business information
- [ ] 2FA enabled on all accounts
- [ ] API keys stored in GitHub secrets
- [ ] Test uploads completed successfully
- [ ] Account verification emails confirmed
- [ ] Professional profiles completed with branding

---

**Next Phase**: Phase 4 - Distribution Execution (Guerrilla Launch)
