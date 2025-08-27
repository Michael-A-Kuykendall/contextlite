# Deploy Everywhere Tool - Foundation Document

**Vision**: Create a GitHub Actions-based tool that auto-discovers project structure and deploys to all relevant package managers with platform-native patterns.

**Status**: Foundation phase - extracting proven patterns from ContextLite deployment system
**Date Started**: August 27, 2025
**Current Success Rate**: 4/12 package managers working (33% → targeting 100%)

## 🎯 Core Concept

### Auto-Discovery Engine
- **Project Structure Analysis**: Detect language, frameworks, build system
- **Platform Compatibility Matrix**: Determine which package managers are applicable
- **Native Pattern Adoption**: Use each platform's recommended deployment workflow
- **Future-Proof Morphing**: Adapt to platform changes automatically

### GitHub Actions Foundation
- **Universal CI/CD**: Leverages existing GitHub ecosystem (90M+ developers)
- **Native Integration**: Works with existing workflows and secrets
- **Scalable Architecture**: Can extend to other CI platforms later
- **Community Patterns**: Uses battle-tested workflow structures

## 📊 Current Working Deployments Analysis

*Analysis based on GitHub API inspection of recent workflow runs - Aug 27, 2025*

### ✅ PROVEN WORKING PATTERNS

#### 1. npm Package Manager
**Status**: ✅ FULLY OPERATIONAL (Fixed Aug 27, 2025)
**Current Version**: 1.1.19
**Success Rate**: 100% (verified via API run 17275852087)
**Pattern Type**: Pre-built artifacts with minimal workflow

**GitHub API Verification**: 
- Run ID: 17275852087 - publish-npm job: "conclusion": "success"
- Package verification: `npm view contextlite@1.1.19` ✅ 

```yaml
# PROVEN WORKING PATTERN - npm
publish-npm:
  runs-on: ubuntu-latest
  if: inputs.platforms == 'all' || contains(inputs.platforms, 'npm') || github.event_name != 'workflow_dispatch'
  steps:
    - uses: actions/checkout@v4
    - uses: actions/setup-node@v4
      with:
        node-version: '18'
        registry-url: 'https://registry.npmjs.org'
    
    - name: Get version
      id: version
      run: |
        if [ "${{ github.event_name }}" = "workflow_dispatch" ]; then
          echo "version=${{ github.event.inputs.version }}" >> $GITHUB_OUTPUT
        else
          echo "version=${GITHUB_REF#refs/tags/v}" >> $GITHUB_OUTPUT
        fi

    - name: Check if version exists
      id: check
      run: |
        if npm view contextlite@${{ steps.version.outputs.version }} >/dev/null 2>&1; then
          echo "exists=true" >> $GITHUB_OUTPUT
        else
          echo "exists=false" >> $GITHUB_OUTPUT
        fi

    - name: Update version and publish
      if: steps.check.outputs.exists == 'false'
      working-directory: npm-wrapper
      run: |
        npm version ${{ steps.version.outputs.version }} --no-git-tag-version
        npm publish
      env:
        NODE_AUTH_TOKEN: ${{ secrets.NPM_TOKEN }}
```

**Key Success Factors**:
- ✅ Pre-built artifacts (ships `lib/` directory)
- ✅ No lifecycle scripts (`prepare`/`postinstall` removed)
- ✅ Conditional publishing (skip if version exists)
- ✅ Minimal dependencies (no TypeScript compilation in CI)
- ✅ Standard npm workflow pattern

#### 2. PyPI Package Manager  
**Status**: ✅ WORKING (Historical success)
**Current Version**: 1.1.16
**Success Rate**: High (based on version availability)
**Pattern Type**: Python wrapper with binary download

**Verification**: Available at https://pypi.org/project/contextlite/
**API Status**: Live package confirmed via PyPI API

*[Workflow pattern analysis pending - need to extract from successful runs]*

#### 3. GitHub Packages
**Status**: ✅ LIKELY WORKING (Detected in workflow)
**Pattern Type**: npm-compatible scoped package

*[Analysis pending - workflow shows publish-github-packages job]*

#### 4. Chocolatey  
**Status**: ✅ HISTORICALLY WORKING
**Pattern Type**: Windows package manager with binary download

*[Analysis pending - need to verify current status via API]*

### 🔧 Working Pattern Commonalities

**Universal Success Factors** (extracted from npm analysis):
1. **Conditional Publishing**: Always check if version exists first
2. **Pre-built Artifacts**: Ship compiled/built files, don't build in CI
3. **Minimal Dependencies**: Avoid complex build chains in workflows
4. **Platform-Native APIs**: Use each platform's standard workflow patterns
5. **Error Isolation**: One platform failure doesn't cascade to others

**Standard Workflow Structure**:
```yaml
publish-PLATFORM:
  runs-on: ubuntu-latest
  if: [conditional logic for platform selection]
  steps:
    - uses: actions/checkout@v4
    - uses: actions/setup-[TOOL]@v4
    - name: Get version
    - name: Check if version exists  
    - name: Publish (conditional)
```

## 🔧 Auto-Discovery Architecture

### Project Detection Engine
```typescript
interface ProjectStructure {
  language: string[];           // ['javascript', 'typescript', 'go', 'python']
  packageManagers: string[];    // ['npm', 'pip', 'go-mod', 'cargo']
  buildSystem: string;          // 'webpack', 'vite', 'make', 'cargo'
  platforms: PlatformConfig[];  // Auto-detected deployment targets
}
```

### Platform Mapping System
```typescript
interface PlatformConfig {
  name: string;                 // 'npm', 'pypi', 'crates'
  detection: DetectionRule[];   // File patterns, manifests
  workflow: WorkflowTemplate;   // GitHub Actions YAML
  secrets: string[];            // Required tokens/keys
  conditional: string;          // Skip logic
}
```

### Morphing Strategy
- **Native Patterns**: Each platform uses its recommended workflow structure
- **Conditional Logic**: Smart skipping for existing versions/packages
- **Error Recovery**: Graceful degradation when platforms are unavailable
- **Future Adaptation**: Monitor platform changes and auto-update templates

## 📈 Implementation Roadmap

### Phase 1: Pattern Extraction (Current)
- [x] Document npm working pattern
- [ ] Analyze PyPI, Chocolatey, GitHub Packages patterns via API
- [ ] Extract common workflow components
- [ ] Identify platform-specific requirements

### Phase 2: Generalization Engine
- [ ] Create template system for workflow generation
- [ ] Build project structure detection logic
- [ ] Implement platform compatibility matrix
- [ ] Develop conditional deployment logic

### Phase 3: Auto-Discovery Intelligence
- [ ] File system analysis for project detection
- [ ] Manifest parsing (package.json, setup.py, Cargo.toml, etc.)
- [ ] Platform availability checking
- [ ] Smart default configuration

### Phase 4: Tool Creation
- [ ] CLI tool for workflow generation
- [ ] GitHub App for repository integration
- [ ] Web interface for configuration
- [ ] Marketplace publication

## 🎯 Success Metrics

### Current Baseline (ContextLite)
- **Working Platforms**: 4/12 (npm, PyPI, GitHub Packages, Chocolatey)
- **Success Rate**: 33%
- **Manual Configuration**: 100% (all manual setup)

### Tool Success Targets
- **Auto-Discovery Accuracy**: >90% correct platform detection
- **Deployment Success Rate**: >95% successful deploys
- **Setup Time Reduction**: <5 minutes from hours/days
- **Platform Coverage**: Support 20+ major package managers

## � Download Analytics Integration

### Automated Download Tracking System
**Purpose**: Monitor deployment success across all platforms for Deploy Everywhere tool validation

#### API-Based Download Collection
```bash
# NPM Downloads (API method)
curl -s "https://api.npmjs.org/downloads/range/2024-01-01:$(date +%Y-%m-%d)/contextlite" | \
  grep -o '"downloads":[0-9]*' | cut -d':' -f2 | awk '{sum+=$1} END {print "NPM Total: " sum}'

# Crates.io Downloads (API method)  
curl -s "https://crates.io/api/v1/crates/contextlite-client" | \
  grep -o '"downloads":[0-9]*' | cut -d':' -f2 | head -1

# Docker Hub Pulls (API method)
curl -s "https://hub.docker.com/v2/repositories/makuykendall/contextlite/" | \
  grep -o '"pull_count":[0-9]*' | cut -d':' -f2

# GitHub Release Downloads (API method with auth)
curl -s -H "Authorization: token $GITHUB_TOKEN" \
  "https://api.github.com/repos/OWNER/REPO/releases" | \
  grep '"download_count":' | awk -F':' '{sum += $2} END {print "GitHub Total: " sum}'
```

#### Web Scraping for Dashboard-Only Platforms
```bash
# PyPI Downloads (Web scraping method)
# URL: https://pypistats.org/packages/PACKAGE_NAME
# Extract: "Downloads last month: X,XXX"

# Chocolatey Downloads (Web scraping method)
# URL: https://community.chocolatey.org/packages/PACKAGE_NAME/VERSION
# Extract: "Downloads: X" and "Downloads of v VERSION: X"

# VS Code Marketplace (Web scraping method)  
# URL: https://marketplace.visualstudio.com/items?itemName=PUBLISHER.EXTENSION
# Extract: "X installs" text
```

#### Deploy Everywhere Tool Integration
```typescript
interface DownloadMetrics {
  platform: string;
  method: 'api' | 'scraping';
  endpoint: string;
  totalDownloads: number;
  lastUpdated: Date;
  growthRate: number;
}

// Auto-discovery will include download tracking setup
function setupDownloadTracking(platforms: PlatformConfig[]): DownloadMetrics[] {
  return platforms.map(platform => ({
    platform: platform.name,
    method: platform.hasAPI ? 'api' : 'scraping',
    endpoint: platform.downloadAPI || platform.pageURL,
    // ... configure tracking based on platform capabilities
  }));
}
```

## 🔧 Research Sources

### API Analysis Commands
```bash
# Get recent workflow runs
curl -s -H "Authorization: token $GITHUB_TOKEN" \
  "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/runs?per_page=10"

# Get job details for specific run
curl -s -H "Authorization: token $GITHUB_TOKEN" \
  "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/runs/RUN_ID/jobs"

# Check package existence across platforms
npm view PACKAGE@VERSION      # npm
pip show PACKAGE              # PyPI  
choco list PACKAGE            # Chocolatey
```

### Web Data Collection
```bash
# Fetch webpage content for scraping
curl -s "https://pypistats.org/packages/contextlite" | \
  grep -o 'Downloads last month: [0-9,]*' | cut -d' ' -f4 | tr -d ','

# Extract download counts from HTML
curl -s "https://community.chocolatey.org/packages/contextlite/1.0.15" | \
  grep -A 5 "Downloads:" | grep -o '[0-9]*'
```

## 📚 Learning Database

### Successful Patterns
- **npm**: Pre-built artifacts, no scripts, conditional publishing
- [Additional patterns to be documented]

### Common Failure Modes
- **Lifecycle Scripts**: prepare/postinstall causing CI failures
- **Dependency Conflicts**: devDependencies vs production installs
- **Token Management**: Authentication across multiple platforms
- **Version Conflicts**: Attempting to republish existing versions

### Platform Quirks
- **npm**: Automatic script execution during install
- [Additional quirks to be documented]

---

**Next Actions**:
1. Complete GitHub API analysis of all working deployments
2. Extract and document successful patterns for each platform
3. Begin generalization of workflow templates
4. Research auto-discovery implementation strategies

*This document will be continuously updated as patterns are extracted and the tool evolves.*
