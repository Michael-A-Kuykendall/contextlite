# ContextLite AI Coding Agent Instructions

Purpose: Enable an AI agent to be productive immediately in this repo. Follow these repo-specific conventions. Keep changes minimal, fast, and aligned with the existing architecture.

## 🎯 COMMUNICATION PROTOCOL
**MANDATORY**: Always use professional language when communicating with the user. Maintain a respectful, technical, and business-appropriate tone in all interactions.

## 📁 INTERNAL DOCUMENTATION POLICY 
**⚠️ CRITICAL**: All internal planning documents MUST be created in `internal-docs/` folder to protect IP

### **Internal Document Classification**
- **`internal-docs/planning/`** - Task lists, integration plans, project roadmaps
- **`internal-docs/security/`** - Security audits, compliance reports, vulnerability assessments
- **`internal-docs/deployment-audits/`** - Deployment failures, workflow analysis, chaos audits
- **`internal-docs/business-strategy/`** - Marketing plans, enterprise strategies, competitive analysis
- **`internal-docs/mission-stacks/`** - Mission execution plans, AI automation strategies

### **Content Guidelines**
1. **Confidential → `internal-docs/`**: Business strategies, security audits, internal processes, competitive intelligence
2. **Public → `docs/`**: User guides, API documentation, installation instructions, contribution guidelines
3. **IP Protection**: Never expose proprietary methods, internal architecture details, or sensitive business information in public docs
4. **Git Ignore**: `internal-docs/` automatically excluded from repository to prevent accidental exposure

### **Document Creation Rules**
- Planning documents, task master lists, strategy papers → Always `internal-docs/`
- User-facing documentation, tutorials, API guides → Always `docs/`
- When in doubt about classification → Default to `internal-docs/` for safety

## 🎯 CURRENT MISSION: DEPLOYMENT ECOSYSTEM HARDENING  
**Status: PRODUCTION LIVE → DEPLOYMENT AUDIT & FIXES**
**Active Documents**: 
- `DEPLOYMENT_STATUS_AUDIT.md` - Complete marketplace status breakdown
- `DEPLOYMENT_AUDIT_FINDINGS.md` - Detailed analysis of workflow failures
**Current Priority**: Fix core build system failure cascading to 5+ package managers
**Achievement**: 
- ✅ Application is LIVE and IN PRODUCTION
- ✅ 4/12 package managers working (npm, PyPI, GitHub Packages, Chocolatey)
- ✅ Smart conditional deployment system implemented
- ✅ Comprehensive deployment audit completed (Aug 20, 2025)
- ❌ Core build-and-release job failing - blocks Docker, Homebrew, Snap, AUR, Crates

## 1. Big Picture Architecture ✅ PRODUCTION LIVE
**MAJOR ACHIEVEMENT**: System is LIVE and deployed in production
- **CoreEngine**: Production-ready foundational engine with real statistics tracking
- **Enhanced Trial System**: 14-day full-featured trial with hardware binding
- **Repository Marriage**: Automated private binary sync via GitHub Actions
- **Multi-Platform Releases**: Cross-platform builds with trial integration
- **License Server**: Complete Stripe integration with email delivery

**Current Architecture**:
- **Dual-Engine System**: CoreEngine (BM25 + heuristics) + JSONCLIEngine (private SMT binary)
- **Enhanced Feature Gate**: Trial-aware licensing with 14-day full access
- **Automated Distribution**: GitHub Actions for multi-platform releases
- **Trial Management**: Hardware-bound 14-day trial with graceful expiration
- **Repository Sync**: Private binary automatically deployed to public releases

## 2. DEPLOYMENT ECOSYSTEM STATUS (August 20, 2025)

### **Deployment Audit Results ✅**
- **File**: `DEPLOYMENT_AUDIT_FINDINGS.md` - Complete workflow analysis
- **Status**: Comprehensive audit of v1.0.35 deployment completed
- **Success Rate**: 4/12 package managers working (33% success rate)
- **Root Cause Identified**: Core build-and-release job compilation failure

### **Working Package Managers** ✅
1. **npm**: Perfect conditional deployment with existence checking
2. **PyPI**: Perfect conditional deployment with package reuse
3. **GitHub Packages**: Reliable scoped package distribution
4. **Chocolatey**: Conditional logic working (correctly skipped existing package)

### **Failing Package Managers** ❌
- **build-and-release**: Go compilation error (blocks all binary-dependent packages)
- **Docker Hub**: Depends on working binaries from build-and-release
- **Homebrew**: Checksum calculation fails (needs GitHub release assets)
- **AUR (Arch)**: Publishing failure (SSH/permission issue)
- **Crates (Rust)**: Publishing failure (token/permission issue)
- **Snap**: Build failure (snapcraft configuration issue)

### **Not Implemented** ⚫
- **WinGet, Flathub, Nix, Scoop**: Completely skipped (need implementation)

### **Critical Tasks Remaining**
1. **Fix Go compilation error in build-and-release** (30 min) → immediately fixes 5+ packages
2. **Debug token/permission issues** (1 hour) → fixes AUR, Crates publishing
3. **Add conditional checks to remaining jobs** (2 hours) → prevents duplicate errors
4. **Implement 4 missing package managers** (4 hours) → completes ecosystem

## 3. Key Workflows

### **Development Workflow**
- Build: `make build` (produces `./build/contextlite`)
- Test: `make test` (all tests pass)
- Local trial: Run `./build/contextlite` (starts 14-day trial automatically)

### **Release Workflow**
- Tag release: `git tag v1.0.0 && git push --tags`
- Automatic: GitHub Actions builds all platforms
- Distribution: Multi-platform archives with trial system
- Private Binary: Auto-synced from private repository

### **Trial Experience**
- **First Run**: Automatically starts 14-day trial with full SMT features
- **Day 1-11**: Full access with daily reminders
- **Day 12-14**: Warning messages about approaching expiration
- **Day 15+**: Core engine only, purchase prompts

## 4. Architecture Patterns

### **Feature Gate Pattern**
```go
// Enhanced feature gate with trial support
featureGate := license.NewEnhancedFeatureGate()
status := featureGate.GetStatus()
remaining := featureGate.TrialDaysRemaining()
```

### **Repository Marriage Pattern**
```yaml
# Private repo pushes trigger public repo binary update
on:
  repository_dispatch:
    types: [private-binary-updated]
```

### **Trial Management Pattern**
```go
// Hardware-bound trial with graceful degradation
trialManager := NewTrialManager()
isActive := trialManager.IsTrialActive()
remaining := trialManager.DaysRemaining()
```

## 5. Production Readiness Status ✅

### **Audit Results** (from `PRODUCTION_AUDIT_REBUTTAL.md`)
- **License Server**: ✅ Fully implemented and production-ready
- **Engine Architecture**: ✅ Sophisticated dual-engine with robust fallback
- **Storage Layer**: ✅ Complete SQLite with performance optimizations  
- **Statistics**: ✅ Real tracking implemented (not hardcoded zeros)
- **Binary Detection**: ✅ Cross-platform with multiple search paths
- **Trial System**: ✅ Hardware-bound 14-day implementation
- **API Endpoints**: ✅ Complete HTTP API with proper timeouts

### **What Works Right Now**
- ✅ 14-day trial starts automatically on first run
- ✅ Private binary detection and graceful fallback
- ✅ Real-time statistics from storage layer
- ✅ Cross-platform builds via GitHub Actions
- ✅ Stripe payment integration with license delivery
- ✅ License validation with RSA cryptography

## 6. Current Deployment Task Status

### **Completed Deployments** ✅
- [x] npm: Perfect conditional deployment with API existence checking
- [x] PyPI: Perfect conditional deployment with package structure reuse
- [x] GitHub Packages: Reliable scoped package distribution
- [x] Chocolatey: Conditional logic working (correctly skips existing packages)

### **Immediate Tasks** ❌
- [ ] **FIX URGENT**: Go compilation error in build-and-release job
- [ ] **DEBUG**: AUR SSH key/permission issues  
- [ ] **DEBUG**: Crates.io token/permission issues
- [ ] **FIX**: Docker build dependency on working binaries
- [ ] **FIX**: Homebrew checksum calculation dependency
- [ ] **FIX**: Snap build configuration issues

### **Secondary Tasks** ⚫
- [ ] **IMPLEMENT**: WinGet deployment (completely missing)
- [ ] **IMPLEMENT**: Flathub deployment (completely missing)
- [ ] **IMPLEMENT**: Nix deployment (completely missing)
- [ ] **IMPLEMENT**: Scoop deployment (completely missing)

## 7. GitHub Token Usage & API Patterns

### **GitHub Token Access Pattern**
```bash
# Environment variable (already set in user's shell)
export GITHUB_TOKEN="your_token_here"

# API calls use this pattern
curl -H "Authorization: token $GITHUB_TOKEN" "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/runs"

# Common endpoints:
# - /actions/runs (list workflow runs)
# - /actions/runs/ID/jobs (get job details)  
# - /releases (get release info)
```

### **Deployment Monitoring Commands**
```bash
# Check latest workflow status
curl -s -H "Authorization: token $GITHUB_TOKEN" \
  "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/runs?per_page=5"

# Get detailed job breakdown
curl -s -H "Authorization: token $GITHUB_TOKEN" \
  "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/runs/ID/jobs"

# Check release assets  
curl -s -H "Authorization: token $GITHUB_TOKEN" \
  "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases"
```

## 8. Business Model Implementation ✅

### **14-Day Trial Strategy**
- **Full Features**: Complete SMT optimization during trial
- **No Registration**: Hardware-bound activation
- **Graceful Expiration**: Falls back to core engine
- **Clear Path**: Purchase at https://contextlite.com/purchase

### **Pricing Structure**
- **Trial**: 14 days free (all Pro features)
- **Professional**: $99 one-time (unlimited everything)
- **Enterprise**: Custom pricing (team features)

## 9. Distribution Channels Ready ✅

### **GitHub Releases**
- Multi-platform binaries
- Trial system included
- Private binary integration

### **Package Managers** (Ready for automation)
- PyPI: Python wrapper
- npm: Node.js wrapper  
- VS Code: Extension marketplace
- Rust Crates: Future implementation

## 10. Command Reference

### **License Management**
```bash
# Check license status
curl http://localhost:8080/license/status

# Check trial information
curl http://localhost:8080/api/v1/trial/info

# Start server (trial begins automatically)
./contextlite
```

### **Development Commands**
```bash
# Build with fixes
make build

# Test all components
make test

# Create release (triggers GitHub Actions)
git tag v1.0.0 && git push --tags
```

## 11. Success Metrics

### **Technical Metrics** (All Passing)
- ✅ Build Success: All platforms build correctly
- ✅ Test Coverage: All tests pass
- ✅ Trial System: 14-day tracking works
- ✅ API Response: <500ms response times
- ✅ Binary Detection: Works across platforms

### **Business Metrics** (Ready to Track)
- 🎯 Trial Conversion: Target 15-25%
- 🎯 Download Rate: Multi-platform distribution
- 🎯 Support Load: <1% users need help
- 🎯 License Validation: <0.1% errors

---

**CURRENT STATUS**: Production ready with automated distribution system complete. Repository marriage implemented. 14-day trial system fully functional. Ready for public launch after workflow testing.

## 10. Deployment Ecosystem Hardening 🎯

### **Hub-and-Spoke Architecture**
- **Hub**: build-and-release job creates GitHub release + binaries  
- **Spokes**: All other package managers consume these artifacts
- **Failure Mode**: Hub failure cascades to all binary-dependent spokes
- **Current Issue**: Hub compilation failure blocking 5+ package managers

### **Best Practices Identified**
From successful npm/PyPI implementations:
- Dynamic package structure generation
- API-based existence checking  
- Version synchronization from single source
- Graceful skipping with clear logging

### **Immediate Fix Strategy**
1. **Debug Go compilation error** (30 min) → fixes 5+ packages immediately
2. **Add missing conditional checks** (2 hours) → prevents duplicate errors
3. **Debug token/permission issues** (1 hour) → fixes publishing failures
4. **Implement missing packages** (4 hours) → completes ecosystem

## 12. Mission Architecture & AI Integration 🎯

### **Shimmy as Primary Interface (Future Intention)**
- **Architecture Decision**: Shimmy will be the primary interaction point with Rustchain
- **Integration Flow**: Mission YAML → Rustchain → Shimmy → Champion Model → Results
- **Fallback Strategy**: Direct Ollama/HTTP APIs for specific edge cases
- **Champion Model**: `llama32-champion:latest` (custom-trained on Rust/Go projects)

### **Mission Workflow System**
```
docs/mission-stacks/
├── current/     # Active missions being executed
└── done/        # Completed missions with results
```

### **Mission Lifecycle Management**
1. Critical tasks → Mission chunks → YAML generation
2. **MANDATORY**: Validate mission with `./rustchain.exe mission validate [mission.yaml]`
3. **MANDATORY**: Dry-run validation with `./rustchain.exe run --dry-run [mission.yaml]`
4. Place in `current/` → Rustchain execution → Champion AI processing
5. **MANDATORY**: Validate results and fix template variables before archival
6. Validation → Results archival → Move to `done/`
7. Expected processing time: 20-30 minutes for full critical task list

**⚠️ CRITICAL WORKFLOW RULE**: Always run validate → dry-run first to catch issues early and save time!

## 13. Complete Release Mission Workflow 🚀

### **Mission Organization Structure**
```
docs/mission-stacks/
├── current/        # Active missions being executed
├── hopper/         # Ready missions queued for execution  
└── done/           # Completed missions with results
```

### **Mission Execution Protocol**
1. **Validate**: `./rustchain.exe mission validate [mission.yaml]`
2. **Dry-run**: `./rustchain.exe run --dry-run [mission.yaml]`
3. **Execute**: `./rustchain.exe run [mission.yaml]`
4. **Validate Results**: Check output quality and completeness
5. **Fix & Retry**: If mission fails, correct once and retry; if fails twice, finish manually and move on
6. **Archive**: Move completed missions to `done/` folder with timestamp

### **Mission Failure Protocol**
- **First Failure**: Debug, fix mission, retry once
- **Second Failure**: Complete task manually, document issue, move to next mission
- **Quality Control**: All results must be validated before archival
- **Persistence**: All work must be documented and preserved

### **Release Process Integration**
- Code fixes → Documentation updates → Marketing materials → Deployment preparation
- All steps must be mission-driven with Champion AI execution
- Maintain consistency across all release artifacts
- Ensure complete traceability from code to marketing

## 14. Railway CLI Master Guide 🎯

### **CRITICAL: Interactive vs Non-Interactive Commands**
**ROOT PROBLEM**: Railway CLI defaults to interactive prompts that LOCK UP scripts

### **✅ CORRECT: Non-Interactive Usage**
```bash
# ALWAYS specify service/environment explicitly
railway service contextlite-testing
railway logs -s contextlite-testing  
railway up -s contextlite-testing
railway variables -s contextlite-testing
railway ssh -s contextlite-testing -- ls
```

### **❌ WRONG: Interactive Commands (WILL LOCK UP)**
```bash
# NEVER USE - these open interactive selectors
railway service      # Opens selector menu - LOCKS UP
railway ssh          # Waits for service selection - LOCKS UP
railway environment  # Opens environment selector - LOCKS UP
```

### **Authentication with Project Tokens**
```bash
export RAILWAY_TOKEN="d66cb512-df83-4f65-8bfb-77074517baaa"

# Project tokens work for:
railway up           # Deploy
railway status       # Check status  
railway redeploy     # Redeploy
railway variables    # Environment variables

# Project tokens DON'T work for:
railway whoami       # Needs account token
railway logs         # May be restricted
railway list         # Needs account token
```

### **Current Service Status**
- **contextlite-testing**: Has abandoned cart system with SQL bug
- **contextlite**: Main production, no abandoned cart endpoints  
- **contextlite-backup**: Backup service, no abandoned cart endpoints

### **SSH Usage (Non-Interactive)**
```bash
# Execute single commands only
railway ssh -s contextlite-testing -- ls -la
railway ssh -s contextlite-testing -- cat /app/abandoned_carts.db
railway ssh -s contextlite-testing -- find /app -name "*.db"

# Some containers have no shell - use HTTP endpoints instead
curl -s "https://contextlite-testing-production.up.railway.app/cart/status"
```

### **Debugging Abandoned Carts**
```bash
# Working endpoints:
curl -s "https://contextlite-testing-production.up.railway.app/health"
curl -X POST "https://contextlite-testing-production.up.railway.app/cart/abandon"

# Broken endpoint (SQL bug):
curl -s "https://contextlite-testing-production.up.railway.app/cart/status"
# Error: "sql: Scan error converting NULL to int64"
```

### **Complete Documentation**
See `RAILWAY_CLI_MASTER_GUIDE.md` for complete reference

## 13. Hugging Face Page Management 🎯

### **Professional Download Experience**
- **URL**: https://huggingface.co/spaces/MikeKuykendall/contextlite-download
- **Repository**: Located in `contextlite-download/` subdirectory
- **Technology**: Gradio app with GitHub API integration
- **Design**: Beautiful glassmorphism UI matching contextlite.com

### **Key Features**
- **Auto-updating**: Fetches latest releases from GitHub API every 5 minutes
- **Multi-platform**: Detects user platform and shows appropriate download
- **Professional Styling**: Dark theme with gradients and animations
- **Performance Stats**: Live metrics display (0.3ms, 2,406 files/sec, etc.)
- **Comparison Section**: ContextLite vs Vector DBs with visual indicators
- **Package Managers**: npm, PyPI, VS Code extension links

### **Management Commands**
```bash
# Navigate to Hugging Face directory
cd contextlite-download

# Edit the page
nano app.py  # or code app.py

# Test locally (optional)
python app.py

# Deploy changes
git add app.py
git commit -m "Update: [description]"
git push

# Hugging Face auto-deploys from main branch
```

### **File Structure**
```
contextlite-download/
├── app.py              # Main Gradio application
├── requirements.txt    # Python dependencies
├── README.md          # Hugging Face page description
└── .git/              # Connected to HF Spaces repo
```

### **Common Updates**
1. **Version Numbers**: Auto-fetched from GitHub API
2. **Performance Stats**: Update in app.py performance section
3. **Design Changes**: Modify CSS in HTML strings
4. **New Features**: Add to feature list sections
5. **Download Links**: Auto-generated from latest GitHub release

### **Troubleshooting**
- **Syntax Errors**: Check with `python -m py_compile app.py`
- **API Issues**: GitHub API has 60 req/hour limit (usually not hit)
- **Deployment**: Hugging Face redeploys automatically on push
- **Local Testing**: Run `python app.py` to test Gradio interface

### **Integration Points**
- **GitHub Releases**: Auto-syncs with repository releases
- **Main Website**: Consistent branding with contextlite.com
- **Package Managers**: Links to npm, PyPI, VS Code marketplace
- **Documentation**: Links to GitHub wiki and repository
