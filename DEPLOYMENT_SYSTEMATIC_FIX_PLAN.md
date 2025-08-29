# ContextLite Deployment Systematic Fix Plan
**Date**: August 29, 2025  
**Status**: CRITICAL - Multiple deployment failures across all platforms  
**Priority**: IMMEDIATE ACTION REQUIRED

## 🚨 CRITICAL ISSUES IDENTIFIED

### 1. **PRIMARY ROOT CAUSE: Go Test Failures**
**Status**: ❌ BLOCKING ALL DEPLOYMENTS  
**Impact**: GoReleaser workflow fails at test stage, preventing all package builds

**Specific Failures**:
- `TestJSONCLI_100Percent/callPrivateBinary_AllErrorPaths` - Multiple test cases failing
- `TestLoader100Percent/isExecutable_AllBranches/Directory_WindowsHandling` - Cross-platform logic error
- Mock binary execution failures on Linux (exec format error)

**Root Cause**: Test suite assumes Windows `.bat` files can execute on Linux runners

### 2. **SECONDARY ISSUES: Missing Secrets & Dependencies**

**Missing GitHub Secrets**:
- `CHOCOLATEY_API_KEY` - Required for Chocolatey deployment (YOUR MAIN PAIN POINT)
- `AUR_KEY` - Required for Arch Linux AUR deployment
- Potential Snapcraft authentication issues

**Missing Dependencies**:
- `snapcraft` not available in runner environment
- Cross-platform binary execution assumptions in tests

---

## 📋 SYSTEMATIC FIX PLAN

### **PHASE 1: IMMEDIATE FIXES (30 minutes)**

#### 1.1 Fix Critical Test Failures
**Action**: Fix cross-platform test execution issues
**Files to Modify**: `internal/engine/*_test.go`

```go
// Fix platform-specific executable detection in tests
// Replace .bat file creation with proper cross-platform approach
```

#### 1.2 Add Missing GitHub Secrets
**Action**: You need to add these secrets to your GitHub repository
**Location**: GitHub Repository → Settings → Secrets and variables → Actions

**Required Secrets**:
```bash
CHOCOLATEY_API_KEY=your_chocolatey_api_key_here
AUR_KEY=your_aur_ssh_private_key_here
```

**How to get Chocolatey API Key**:
1. Create account at https://chocolatey.org/
2. Go to your profile → API Keys
3. Generate new API key
4. Add to GitHub secrets as `CHOCOLATEY_API_KEY`

### **PHASE 2: TEST FIXES (45 minutes)**

#### 2.1 Fix `callPrivateBinary_AllErrorPaths` Test
**Issue**: Test creates `.bat` files on Linux which can't execute
**Solution**: Create proper executable files for each platform

#### 2.2 Fix `Directory_WindowsHandling` Test  
**Issue**: Directory executable detection inconsistent across platforms
**Solution**: Update test expectations based on actual OS

#### 2.3 Disable Snapcraft Temporarily
**Action**: Already done in `.goreleaser.yaml` - keep commented out until snapcraft available

### **PHASE 3: DEPLOYMENT VERIFICATION (1 hour)**

#### 3.1 Test Each Package Manager Individually
**Use existing VS Code tasks**:
- `🍫 Deploy Chocolatey Only`
- `📦 Deploy npm Only`  
- `🐍 Deploy PyPI Only`
- `🐳 Deploy Docker Only`

#### 3.2 Verify Working Platforms
**Test platforms that should work**:
- GitHub Releases ✅ (core functionality)
- Docker Images ✅ (basic build)
- Homebrew ✅ (tap repository access)

---

## 🎯 HUMAN ACTION ITEMS

### **CRITICAL - YOU MUST DO THESE**

1. **Add Chocolatey API Key** (5 minutes)
   ```bash
   # Go to: https://github.com/Michael-A-Kuykendall/contextlite/settings/secrets/actions
   # Add secret: CHOCOLATEY_API_KEY = your_api_key
   ```

2. **Generate AUR SSH Key** (10 minutes)
   ```bash
   # Generate SSH key for AUR
   ssh-keygen -t rsa -b 4096 -C "your_email@example.com"
   # Add public key to AUR account
   # Add private key to GitHub secrets as AUR_KEY
   ```

3. **Test Local Build** (5 minutes)
   ```bash
   # Verify local build works
   go test ./internal/engine -v
   make build
   ```

### **OPTIONAL - PLATFORM EXPANSION**

4. **Snapcraft Setup** (if you want Snap packages)
   - Create Ubuntu One account
   - Register app name on Snapcraft
   - Get authentication token
   - Uncomment snapcraft section in `.goreleaser.yaml`

5. **Winget Setup** (manual submission required)
   - Microsoft requires manual PR to winget-pkgs repository
   - Not automated through GoReleaser
   - Can be done after other platforms working

---

## 🔧 AUTOMATED FIXES TO IMPLEMENT

### **Test Platform Detection Fix**
```go
// Fix for internal/engine tests
func createExecutableForPlatform(dir, name string) string {
    if runtime.GOOS == "windows" {
        return createWindowsExecutable(dir, name+".exe")
    } else {
        return createUnixExecutable(dir, name)
    }
}
```

### **Cross-Platform Mock Binary**
```go
// Replace .bat file creation with proper executable
func createMockBinary(dir string) string {
    if runtime.GOOS == "windows" {
        return createPowershellScript(dir)
    } else {
        return createShellScript(dir)
    }
}
```

---

## 📊 DEPLOYMENT STATUS MATRIX

| Platform | Status | Blocker | Fix Required | ETA |
|----------|---------|---------|-------------|-----|
| **GitHub Releases** | 🟡 Partial | Test failures | Fix tests | 30min |
| **Chocolatey** | ❌ Failed | Missing API key | Add secret | 5min |
| **Homebrew** | 🟡 Partial | Test failures | Fix tests | 30min |
| **Docker** | 🟡 Partial | Test failures | Fix tests | 30min |
| **Scoop** | 🟡 Partial | Test failures | Fix tests | 30min |
| **AUR** | ❌ Failed | Missing SSH key | Add secret | 10min |
| **Snap** | ⚫ Disabled | No snapcraft | Enable later | N/A |
| **npm** | ✅ Working | None | None | 0min |
| **PyPI** | ✅ Working | None | None | 0min |

---

## 🚀 EXECUTION ORDER

### **Immediate (Next 15 minutes)**
1. ✅ Add `CHOCOLATEY_API_KEY` to GitHub secrets
2. ✅ Add `AUR_KEY` to GitHub secrets  
3. ✅ Fix test platform detection issues

### **Short Term (Next hour)**
1. 🔧 Fix cross-platform test execution
2. 🔧 Update mock binary creation for Linux
3. 🔧 Verify test suite passes on Linux runners
4. 🚀 Tag new release to trigger full deployment

### **Validation**
1. 🧪 Test Chocolatey deployment specifically
2. 🧪 Verify other package managers work
3. 🧪 Confirm all platforms building successfully

---

## 💡 SUCCESS METRICS

**When deployment is fixed, you should see**:
- ✅ All GoReleaser tests pass
- ✅ Chocolatey package published successfully
- ✅ All 8+ package managers working
- ✅ Zero manual deployment pain points
- ✅ Single tag creates everything automatically

**Expected Result**: Tag release → All platforms deploy automatically → Zero manual work

---

## 🔥 PRIORITY RANKING

1. **🚨 CRITICAL**: Fix test failures (blocks everything)
2. **🎯 HIGH**: Add Chocolatey API key (your main pain point)
3. **📦 MEDIUM**: Add AUR SSH key (nice to have)
4. **🔧 LOW**: Enable Snapcraft (future enhancement)

**Total estimated fix time**: 1-2 hours for complete deployment ecosystem
