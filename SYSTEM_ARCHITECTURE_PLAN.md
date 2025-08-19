# 🏗️ ContextLite System Architecture & Production Plan

**Date**: August 19, 2025  
**Status**: DRAFT - Ready for Implementation  
**Model**: 14-Day Full-Featured Trial → $99 License

---

## 🎯 **EXECUTIVE SUMMARY**

This plan outlines the complete system architecture for marrying the private and public ContextLite repositories, implementing automated distribution, and ensuring production readiness with proper trial/licensing mechanisms.

### **Core Strategy: Public Repository with Private Binary Integration**
- **Public Repo**: Complete application with 14-day trial system
- **Private Repo**: Advanced binary automatically integrated via CI/CD  
- **Distribution**: Single download, full features, time-limited trial
- **Conversion**: After 14 days, requires $99 license to continue

---

## 🏗️ **REPOSITORY ARCHITECTURE**

### **1. Public Repository (`contextlite`)**
```
contextlite/
├── build/
│   ├── contextlite(.exe)           # Main application
│   └── contextlite-library(.exe)   # Private binary (auto-updated)
├── internal/
│   ├── engine/
│   │   ├── core.go                 # Fallback BM25 engine
│   │   ├── loader.go               # Smart binary detection
│   │   └── json_cli.go             # Private binary interface
│   ├── license/
│   │   ├── trial.go                # 14-day trial tracking
│   │   └── validation.go           # License validation
│   └── api/
├── cmd/
│   └── contextlite/                # Main application only
└── .github/
    └── workflows/
        └── sync-private-binary.yml # Auto-update from private repo
```

### **2. Private Repository (`contextlite-private`)**
```
contextlite-private/
├── build/
│   └── contextlite-library(.exe)   # Advanced binary
├── cmd/
│   ├── license-server/             # Payment & license system
│   └── contextlite-library/        # optimization engine binary
├── internal/
│   ├── optimization/                        # Your proprietary optimization algorithms
│   └── optimization/               # Performance optimizations
└── .github/
    └── workflows/
        └── deploy-to-public.yml    # Push binary to public repo
```

---

## 🔄 **AUTOMATED BINARY SYNCHRONIZATION**

### **GitHub Actions Workflow: Private → Public**

**File**: `contextlite-private/.github/workflows/deploy-to-public.yml`
```yaml
name: Deploy Private Binary to Public Repo

on:
  push:
    branches: [ main ]
    paths: [ 'build/contextlite-library*' ]
  release:
    types: [ published ]

jobs:
  deploy-binary:
    runs-on: ubuntu-latest
    steps:
    - name: Checkout Private Repo
      uses: actions/checkout@v4
      
    - name: Build Private Binary
      run: make build-library
      
    - name: Checkout Public Repo
      uses: actions/checkout@v4
      with:
        repository: Michael-A-Kuykendall/contextlite
        token: ${{ secrets.PUBLIC_REPO_TOKEN }}
        path: public-repo
        
    - name: Copy Binary to Public Repo
      run: |
        cp build/contextlite-library* public-repo/build/
        
    - name: Commit and Push to Public
      run: |
        cd public-repo
        git config user.name "ContextLite Bot"
        git config user.email "bot@contextlite.com"
        git add build/contextlite-library*
        git commit -m "chore: update private binary from $(git rev-parse --short HEAD)"
        git push
```

### **Binary Version Management**
```yaml
# Additional step in workflow
- name: Update Binary Version
  run: |
    echo "PRIVATE_BINARY_VERSION=$(git rev-parse --short HEAD)" > public-repo/.private-version
    echo "BUILD_DATE=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> public-repo/.private-version
```

---

## ⏱️ **14-DAY TRIAL IMPLEMENTATION**

### **Trial Tracking System**

**File**: `internal/license/trial.go`
```go
package license

import (
    "crypto/sha256"
    "encoding/hex"
    "fmt"
    "os"
    "path/filepath"
    "time"
)

type TrialManager struct {
    trialFile string
    hwID      string
}

type TrialInfo struct {
    StartDate     time.Time `json:"start_date"`
    HardwareID    string    `json:"hardware_id"`
    InstallID     string    `json:"install_id"`
    TrialDays     int       `json:"trial_days"`
    ExpiresAt     time.Time `json:"expires_at"`
}

func NewTrialManager() *TrialManager {
    homeDir, _ := os.UserHomeDir()
    trialPath := filepath.Join(homeDir, ".contextlite", "trial.json")
    
    hwID := generateHardwareID()
    
    return &TrialManager{
        trialFile: trialPath,
        hwID:      hwID,
    }
}

func (tm *TrialManager) StartOrGetTrial() (*TrialInfo, error) {
    // Check if trial exists
    if trial, err := tm.loadExistingTrial(); err == nil {
        return trial, nil
    }
    
    // Start new trial
    trial := &TrialInfo{
        StartDate:  time.Now(),
        HardwareID: tm.hwID,
        InstallID:  generateInstallID(),
        TrialDays:  14,
        ExpiresAt:  time.Now().AddDate(0, 0, 14),
    }
    
    return trial, tm.saveTrial(trial)
}

func (tm *TrialManager) IsTrialActive() bool {
    trial, err := tm.loadExistingTrial()
    if err != nil {
        return true // First run - allow trial to start
    }
    
    return time.Now().Before(trial.ExpiresAt)
}

func (tm *TrialManager) DaysRemaining() int {
    trial, err := tm.loadExistingTrial()
    if err != nil {
        return 14 // First run
    }
    
    remaining := trial.ExpiresAt.Sub(time.Now()).Hours() / 24
    if remaining < 0 {
        return 0
    }
    return int(remaining)
}
```

### **License Gate Integration**

**Update**: `internal/license/license.go`
```go
func NewFeatureGate() *LicenseFeatureGate {
    // 1. Check for valid license first
    if license := tryLoadLicense(); license != nil {
        return &LicenseFeatureGate{
            tier:    license.Tier,
            status:  StatusLicensed,
            message: fmt.Sprintf("Licensed: %s", license.Tier),
        }
    }
    
    // 2. Check trial status
    trialMgr := NewTrialManager()
    if trialMgr.IsTrialActive() {
        remaining := trialMgr.DaysRemaining()
        return &LicenseFeatureGate{
            tier:    TierPro, // Full features during trial!
            status:  StatusTrial,
            message: fmt.Sprintf("Trial: %d days remaining", remaining),
        }
    }
    
    // 3. Trial expired - require purchase
    return &LicenseFeatureGate{
        tier:    TierExpired,
        status:  StatusExpired,
        message: "Trial expired. Purchase license to continue.",
    }
}
```

---

## 📦 **DISTRIBUTION AUTOMATION**

### **Multi-Platform Release Pipeline**

**File**: `contextlite/.github/workflows/release.yml`
```yaml
name: Multi-Platform Release

on:
  push:
    tags: [ 'v*' ]

jobs:
  build-and-release:
    strategy:
      matrix:
        include:
        - os: ubuntu-latest
          goos: linux
          goarch: amd64
          suffix: ""
        - os: ubuntu-latest  
          goos: linux
          goarch: arm64
          suffix: ""
        - os: windows-latest
          goos: windows
          goarch: amd64
          suffix: ".exe"
        - os: macos-latest
          goos: darwin
          goarch: amd64
          suffix: ""
        - os: macos-latest
          goos: darwin
          goarch: arm64
          suffix: ""
          
    runs-on: ${{ matrix.os }}
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Setup Go
      uses: actions/setup-go@v4
      with:
        go-version: '1.21'
        
    - name: Ensure Private Binary Exists
      run: |
        if [ ! -f "build/contextlite-library${{ matrix.suffix }}" ]; then
          echo "WARNING: Private binary not found - using core engine only"
        fi
        
    - name: Build Release Binary
      env:
        GOOS: ${{ matrix.goos }}
        GOARCH: ${{ matrix.goarch }}
        CGO_ENABLED: 0
      run: |
        make build
        
    - name: Package Release
      run: |
        mkdir -p dist
        cp build/contextlite${{ matrix.suffix }} dist/
        if [ -f "build/contextlite-library${{ matrix.suffix }}" ]; then
          cp build/contextlite-library${{ matrix.suffix }} dist/
        fi
        cp README.md LICENSE dist/
        
    - name: Create Archive
      run: |
        cd dist
        if [ "${{ matrix.goos }}" = "windows" ]; then
          zip -r ../contextlite-${{ matrix.goos }}-${{ matrix.goarch }}.zip .
        else
          tar -czf ../contextlite-${{ matrix.goos }}-${{ matrix.goarch }}.tar.gz .
        fi
        
    - name: Upload Release Asset
      uses: actions/upload-release-asset@v1
      env:
        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
      with:
        upload_url: ${{ github.event.release.upload_url }}
        asset_path: ./contextlite-${{ matrix.goos }}-${{ matrix.goarch }}.*
        asset_name: contextlite-${{ matrix.goos }}-${{ matrix.goarch }}.*
        asset_content_type: application/octet-stream
```

### **Package Manager Automation**

**PyPI Release**: `.github/workflows/publish-pypi.yml`
```yaml
name: Publish to PyPI

on:
  release:
    types: [published]

jobs:
  publish-pypi:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v4
    
    - name: Setup Python
      uses: actions/setup-python@v4
      with:
        python-version: '3.9'
        
    - name: Update Python Wrapper
      run: |
        cd python-wrapper
        # Update version from git tag
        echo "__version__ = '${GITHUB_REF#refs/tags/v}'" > contextlite/_version.py
        
    - name: Build and Publish
      env:
        TWINE_USERNAME: __token__
        TWINE_PASSWORD: ${{ secrets.PYPI_TOKEN }}
      run: |
        cd python-wrapper
        pip install build twine
        python -m build
        twine upload dist/*
```

**npm Release**: `.github/workflows/publish-npm.yml`
```yaml
name: Publish to npm

on:
  release:
    types: [published]

jobs:
  publish-npm:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v4
    
    - name: Setup Node.js
      uses: actions/setup-node@v4
      with:
        node-version: '18'
        registry-url: 'https://registry.npmjs.org'
        
    - name: Update npm Package
      run: |
        cd npm-wrapper
        # Update version from git tag
        npm version ${GITHUB_REF#refs/tags/v} --no-git-tag-version
        
    - name: Publish to npm
      run: |
        cd npm-wrapper
        npm publish
      env:
        NODE_AUTH_TOKEN: ${{ secrets.NPM_TOKEN }}
```

---

## 🔍 **CRITICAL ISSUES AUDIT & RESOLUTION**

### **Issue 1: Engine Statistics Implementation**

**Current Problem**: Stats return hardcoded zeros
```go
// Current stub implementation
return &types.EngineStats{
    TotalQueries: 0, // Not tracked
}
```

**Solution**: Implement real statistics tracking
```go
type EngineStats struct {
    TotalQueries     int64     `json:"total_queries"`
    CacheHits        int64     `json:"cache_hits"`
    CacheMisses      int64     `json:"cache_misses"`
    AvgResponseTime  float64   `json:"avg_response_time_ms"`
    LastQueryTime    time.Time `json:"last_query_time"`
    UsingPrivateEngine bool    `json:"using_private_engine"`
}

// Add to CoreEngine struct
type CoreEngine struct {
    config  *config.Config
    storage types.StorageInterface
    stats   *EngineStats
    mutex   sync.RWMutex
}

func (e *CoreEngine) recordQuery(duration time.Duration, cacheHit bool) {
    e.mutex.Lock()
    defer e.mutex.Unlock()
    
    e.stats.TotalQueries++
    e.stats.LastQueryTime = time.Now()
    
    if cacheHit {
        e.stats.CacheHits++
    } else {
        e.stats.CacheMisses++
    }
    
    // Update rolling average
    e.stats.AvgResponseTime = (e.stats.AvgResponseTime + duration.Milliseconds()) / 2
}
```

### **Issue 2: Binary Detection Reliability**

**Current Problem**: Simplified path detection
```go
func getExecutablePath() (string, error) {
    return filepath.Abs(".")  // Too simple
}
```

**Solution**: Robust binary detection with logging
```go
func findPrivateBinary() string {
    logger := log.Default()
    
    // Get executable location first
    execPath, err := os.Executable()
    if err != nil {
        logger.Printf("Failed to get executable path: %v", err)
        execPath = "."
    }
    
    searchPaths := []string{
        filepath.Dir(execPath),                    // Same directory as main binary
        filepath.Join(filepath.Dir(execPath), "bin"),
        "./",                                      // Current working directory
        "./build/",
        "../contextlite-private/build/",          // Development setup
        "/usr/local/bin/",                        // System install
        "/opt/contextlite/bin/",                  // Package install
    }
    
    for _, basePath := range searchPaths {
        for _, binaryName := range getBinaryNames() {
            fullPath := filepath.Join(basePath, binaryName)
            
            if fileExists(fullPath) && isExecutable(fullPath) {
                logger.Printf("Found private binary at: %s", fullPath)
                return fullPath
            }
        }
    }
    
    logger.Printf("Private binary not found in any search path - using core engine")
    return ""
}
```

### **Issue 3: Cache Implementation**

**Current Problem**: Cache always returns false
```go
CacheHit: false, // Always false
```

**Solution**: Implement actual caching with TTL
```go
type QueryCache struct {
    entries map[string]*CacheEntry
    mutex   sync.RWMutex
    maxSize int
    ttl     time.Duration
}

type CacheEntry struct {
    Result    *types.ContextResult
    CreatedAt time.Time
    AccessCount int
}

func (c *QueryCache) Get(key string) (*types.ContextResult, bool) {
    c.mutex.RLock()
    defer c.mutex.RUnlock()
    
    entry, exists := c.entries[key]
    if !exists {
        return nil, false
    }
    
    // Check TTL
    if time.Since(entry.CreatedAt) > c.ttl {
        delete(c.entries, key)
        return nil, false
    }
    
    entry.AccessCount++
    return entry.Result, true
}

func (c *QueryCache) Set(key string, result *types.ContextResult) {
    c.mutex.Lock()
    defer c.mutex.Unlock()
    
    // Evict old entries if at capacity
    if len(c.entries) >= c.maxSize {
        c.evictLRU()
    }
    
    c.entries[key] = &CacheEntry{
        Result:    result,
        CreatedAt: time.Now(),
        AccessCount: 1,
    }
}
```

### **Issue 4: Error Handling**

**Current Problem**: Silent failures
```go
hostname, _ := os.Hostname()  // Error ignored
```

**Solution**: Proper error handling with fallbacks
```go
func getHardwareFingerprint() (string, error) {
    var components []string
    
    // Hostname with fallback
    if hostname, err := os.Hostname(); err == nil {
        components = append(components, hostname)
    } else {
        log.Printf("Warning: Could not get hostname: %v", err)
        components = append(components, "unknown-host")
    }
    
    // User directory with fallback
    if homeDir, err := os.UserHomeDir(); err == nil {
        components = append(components, filepath.Base(homeDir))
    } else {
        log.Printf("Warning: Could not get user directory: %v", err)
        components = append(components, "unknown-user")
    }
    
    // Add more stable identifiers...
    
    if len(components) == 0 {
        return "", fmt.Errorf("could not generate hardware fingerprint")
    }
    
    fingerprint := strings.Join(components, "-")
    hash := sha256.Sum256([]byte(fingerprint))
    return hex.EncodeToString(hash[:8]), nil
}
```

---

## 🎛️ **USER EXPERIENCE ENHANCEMENTS**

### **Trial Status Display**

**Command Line Interface**:
```bash
$ contextlite status
ContextLite Status:
✅ Engine: optimization-Optimized (contextlite-library detected)
📅 License: Trial (12 days remaining)
⚡ Performance: 0.3ms avg query time
📊 Usage: 847 queries processed

$ contextlite license purchase
Opening purchase page: https://contextlite.com/purchase
Use license key from email with: contextlite license install <key>
```

**HTTP API Enhancement**:
```go
// Add to server.go
func (s *Server) handleLicenseStatus(w http.ResponseWriter, r *http.Request) {
    featureGate := s.featureGate
    
    status := map[string]interface{}{
        "tier":            featureGate.GetTier(),
        "status":          featureGate.Status,
        "message":         featureGate.Message,
        "using_private":   s.engine.UsingPrivateBinary(),
        "trial_days":      featureGate.TrialDaysRemaining(),
        "purchase_url":    "https://contextlite.com/purchase",
    }
    
    writeJSON(w, status)
}
```

### **Graceful Degradation**

**When Trial Expires**:
```go
func (fg *LicenseFeatureGate) CheckAccess(feature string) error {
    if fg.status == StatusExpired {
        return &LicenseError{
            Message: "Trial expired. Your data is safe - purchase a license to continue.",
            PurchaseURL: "https://contextlite.com/purchase",
            TrialExpiredAt: fg.expiredAt,
        }
    }
    
    if fg.status == StatusTrial && fg.TrialDaysRemaining() <= 3 {
        log.Printf("Trial expires in %d days - consider purchasing", fg.TrialDaysRemaining())
    }
    
    return nil
}
```

---

## 📋 **IMPLEMENTATION CHECKLIST**

### **Phase 1: Repository Marriage (Week 1)**
- [ ] Set up GitHub Actions for binary synchronization
- [ ] Test private binary deployment to public repo
- [ ] Verify binary detection across platforms
- [ ] Add binary version tracking

### **Phase 2: Trial System (Week 2)** 
- [ ] Implement trial tracking system
- [ ] Add license gate with trial support
- [ ] Create trial status endpoints
- [ ] Add graceful degradation for expired trials

### **Phase 3: Production Fixes (Week 2)**
- [ ] Implement real statistics tracking
- [ ] Fix binary detection with robust path finding
- [ ] Add proper cache implementation
- [ ] Improve error handling throughout

### **Phase 4: Distribution Automation (Week 3)**
- [ ] Set up multi-platform release pipeline
- [ ] Automate PyPI package publishing
- [ ] Automate npm package publishing
- [ ] Test VS Code extension integration

### **Phase 5: User Experience (Week 4)**
- [ ] Add CLI license management commands
- [ ] Enhance API with license status endpoints
- [ ] Create user-friendly error messages
- [ ] Add purchase flow integration

---

## 🚀 **SUCCESS METRICS**

### **Technical Metrics**
- **Binary Sync Success Rate**: >99% automated deployments
- **Trial Conversion Rate**: Target 15-25% trial to paid
- **Performance**: <500ms response time 95th percentile
- **Uptime**: >99.9% for license server

### **Business Metrics**
- **Download Rate**: Track unique downloads per day
- **Trial Starts**: Monitor trial activation rate
- **Support Tickets**: <1% of users need assistance
- **License Validation**: <0.1% validation errors

---

## 🛡️ **SECURITY CONSIDERATIONS**

### **Private Binary Protection**
- Binary obfuscation using UPX or similar
- Anti-debugging techniques in private binary
- License validation with offline capability
- Secure key storage for license validation

### **Trial System Security**
- Hardware fingerprinting to prevent easy reset
- Encrypted trial tracking files
- Server-side validation for suspicious patterns
- Grace period for legitimate hardware changes

---

This plan provides a complete roadmap for production-ready ContextLite with automated private/public repository marriage, robust trial system, and comprehensive distribution automation. Each component is designed for reliability, security, and excellent user experience.
