# DEPLOYMENT ARCHITECTURE PLAN
*Status: CRITICAL - Complete overhaul required*

## 🚨 CURRENT PROBLEM ANALYSIS

### **Identified Issues**
1. **FOUR conflicting release workflows** all triggered by same tags
2. Multiple GoReleaser configs causing collision 
3. Deprecated workflows still firing
4. No hub-and-spoke architecture
5. Package manager deployments scattered and unreliable
6. ~70+ failed tags due to bad setup

### **Conflicting Workflows Found**
- `goreleaser.yml` - GoReleaser main
- `goreleaser.yaml` - GoReleaser duplicate (!!)
- `release.yml` - GoReleaser with tests
- `simple-release.yml` - GitHub releases only

## 🎯 NEW ARCHITECTURE: Hub-and-Spoke Model

### **Hub: GoReleaser (Single Source of Truth)**
```
GoReleaser → GitHub Release + Binaries
    ↓
All package managers consume from GitHub Release
```

### **Spokes: Package Managers**
- **Chocolatey** → Consumes GitHub release binaries
- **Homebrew** → Consumes GitHub release checksums
- **Snap** → Built in GoReleaser
- **AUR** → Built in GoReleaser  
- **Docker** → Built in GoReleaser
- **npm** → Wrapper downloads from GitHub
- **PyPI** → Wrapper downloads from GitHub

### **Benefits**
1. **Single workflow** eliminates conflicts
2. **Reliable binaries** from one build process
3. **Consistent checksums** across all platforms
4. **Reduced complexity** - one config to maintain
5. **Faster releases** - parallel package deployments

## 🛠️ IMPLEMENTATION PLAN

### **Phase 1: Cleanup (IMMEDIATE)**
1. **Delete conflicting workflows**:
   - [ ] Remove `goreleaser.yaml` (duplicate)
   - [ ] Remove `release.yml` (redundant)
   - [ ] Remove `simple-release.yml` (deprecated)
   - [ ] Keep only `goreleaser.yml` (primary)

2. **Disable deprecated workflows**:
   - [ ] Move to `archive/workflows/` folder
   - [ ] Document what they did

### **Phase 2: GoReleaser Configuration (CRITICAL)**
1. **Review `.goreleaser.yaml`** configuration
2. **Ensure hub-and-spoke pattern**:
   - GitHub releases as hub
   - All package managers as spokes
3. **Test with dry-run**: `goreleaser release --snapshot --clean`

### **Phase 3: Package Manager Migration**
1. **Chocolatey**: Configure to consume GitHub releases
2. **Homebrew**: Update formula to use GitHub checksums
3. **npm/PyPI**: Ensure wrappers download from GitHub
4. **Docker**: Verify GoReleaser builds properly

### **Phase 4: Testing & Validation**
1. **Create test tag**: `v2.0.1-test`
2. **Verify single workflow fires**
3. **Validate all package managers work**
4. **Clean up test artifacts**

### **Phase 5: Production Release**
1. **Tag clean release**: `v2.0.1`
2. **Monitor deployment**
3. **Verify all platforms updated**

## 📋 DETAILED WORKFLOW ANALYSIS

### **Keep: goreleaser.yml**
```yaml
name: GoReleaser - Release Everywhere
on:
  push:
    tags: ['v*']
# This should be the ONLY workflow firing on tags
```

### **Remove: All Others**
- **goreleaser.yaml** - Exact duplicate causing conflicts
- **release.yml** - Redundant GoReleaser setup  
- **simple-release.yml** - Manual GitHub releases (obsolete)

## 🔧 GORELEASER CONFIGURATION REQUIREMENTS

### **Must Include**
```yaml
builds:
  - main: ./cmd/contextlite
    targets:
      - linux_amd64
      - linux_arm64  
      - windows_amd64
      - darwin_amd64
      - darwin_arm64

archives:
  - format: tar.gz
    format_overrides:
      - goos: windows
        format: zip

release:
  github:
    owner: Michael-A-Kuykendall
    name: contextlite

chocolateys:
  - name: contextlite
    title: ContextLite
    authors: Mike Kuykendall
    summary: SMT-based context assembly engine

brews:
  - name: contextlite
    repository:
      owner: Michael-A-Kuykendall
      name: homebrew-tools

snapcrafts:
  - name: contextlite
    summary: SMT-based context assembly engine

dockers:
  - image_templates:
    - "ghcr.io/michael-a-kuykendall/contextlite:{{ .Tag }}"
    - "ghcr.io/michael-a-kuykendall/contextlite:latest"
```

## 🚀 EXECUTION CHECKLIST

### **Immediate Actions**
- [ ] **STOP**: No more tags until architecture fixed
- [ ] Move conflicting workflows to archive
- [ ] Test GoReleaser config with `--snapshot`
- [ ] Verify single workflow setup

### **Test Phase**
- [ ] Create `v2.0.1-test` tag
- [ ] Verify only ONE workflow fires
- [ ] Check all package managers update
- [ ] Clean up test artifacts

### **Production Phase**  
- [ ] Tag `v2.0.1` for real release
- [ ] Monitor deployment across all platforms
- [ ] Document new process
- [ ] Update deployment docs

## 📊 SUCCESS METRICS

### **Before Fix**
- 4 workflows firing per tag
- Multiple GoReleaser conflicts
- Failed deployments
- ~70 wasted tags

### **After Fix**
- 1 workflow per tag
- Hub-and-spoke architecture
- Reliable deployments
- Clean tag history going forward

## 🎯 OUTCOME

Single, reliable deployment workflow that:
1. **Builds once** in GoReleaser
2. **Publishes to GitHub** as hub
3. **All package managers** consume from GitHub
4. **No more conflicts** or failed deployments
5. **Professional release process** going forward

---

**STATUS**: Ready to execute Phase 1 (Cleanup) immediately
