# COMPREHENSIVE INTEGRATION TESTING PLAN
## Production Launch Readiness - Phase 2

**Status**: Ready for systematic integration testing  
**Date**: August 19, 2025  
**Objective**: Test every marketplace integration thoroughly before production launch

---

## 🎯 TESTING PHILOSOPHY

**Zero Tolerance for Production Issues**
- Every integration must be tested on actual target platforms
- Every failure scenario must be identified and handled
- Every edge case must be documented
- Credibility depends on flawless execution

**Testing Methodology**
1. **Isolated Testing**: Each marketplace tested independently
2. **Platform Verification**: Test on actual target operating systems
3. **End-to-End Validation**: From release trigger to user installation
4. **Failure Recovery**: Document and test failure scenarios
5. **Documentation**: Record exact steps and troubleshooting

---

## 📋 PHASE 1: HIGH-RISK INTEGRATIONS (Start Here)

### 1. SNAP STORE INTEGRATION TEST

#### **Pre-Test Setup**
```bash
# Ensure Ubuntu WSL is properly configured
wsl --list --verbose
# Should show Ubuntu running

# Verify snapcraft installation
wsl -d Ubuntu snapcraft --version
# Should show snapcraft 8.x

# Verify login credentials
wsl -d Ubuntu snapcraft whoami
# Should show your email and permissions
```

#### **Test Execution Steps**

**Step 1: Snapcraft Build Test**
```bash
# Create test snap directory
mkdir -p /tmp/snap-test
cd /tmp/snap-test

# Create minimal snapcraft.yaml
cat > snap/snapcraft.yaml << 'EOF'
name: contextlite-test
base: core22
version: '0.9.0-test'
summary: Test build for ContextLite
description: Integration test for Snap Store publishing
grade: devel
confinement: classic

parts:
  contextlite:
    plugin: dump
    source: https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v0.9.0-beta/contextlite_0.9.0-beta_linux_amd64.tar.gz
    stage:
      - contextlite
    prime:
      - contextlite

apps:
  contextlite-test:
    command: contextlite
EOF

# Test build locally
wsl -d Ubuntu bash -c "cd /tmp/snap-test && snapcraft --destructive-mode"
```

**Step 2: Snap Installation Test**
```bash
# Install locally built snap
wsl -d Ubuntu bash -c "cd /tmp/snap-test && sudo snap install *.snap --dangerous"

# Test execution
wsl -d Ubuntu bash -c "contextlite-test --version"

# Test basic functionality
wsl -d Ubuntu bash -c "timeout 10s contextlite-test --port 18080 &"
sleep 5
curl -f http://localhost:18080/health || echo "FAIL: Health check failed"

# Cleanup
wsl -d Ubuntu bash -c "sudo snap remove contextlite-test"
```

**Step 3: GitHub Actions Simulation**
```bash
# Test the exact workflow steps
git tag v0.9.0-snap-test
git push --tags

# Monitor GitHub Actions: https://github.com/Michael-A-Kuykendall/contextlite/actions
# Verify:
# - Snap builds successfully
# - Upload to Snap Store succeeds
# - Release to stable channel works
```

**Success Criteria**
- [ ] Snap builds without errors
- [ ] Local installation works
- [ ] Binary executes and responds to health checks
- [ ] GitHub Actions completes successfully
- [ ] Snap appears in Snap Store
- [ ] Public installation works: `snap install contextlite`

**Failure Scenarios to Test**
- [ ] Missing dependencies
- [ ] Permission issues
- [ ] Network failures during upload
- [ ] Invalid snapcraft.yaml
- [ ] Authentication failures

---

### 2. AUR (ARCH USER REPOSITORY) INTEGRATION TEST

#### **Pre-Test Setup**
```bash
# Verify SSH key is properly configured
ssh -T aur@aur.archlinux.org
# Should show: "Hi username! You've successfully authenticated..."

# Check AUR account
echo "Visit: https://aur.archlinux.org/account/"
echo "Verify: SSH key is added and working"
```

#### **Test Execution Steps**

**Step 1: Manual AUR Package Creation**
```bash
# Clone AUR repository for contextlite-bin
git clone ssh://aur@aur.archlinux.org/contextlite-bin.git
cd contextlite-bin

# Create PKGBUILD
cat > PKGBUILD << 'EOF'
# Maintainer: Michael Allen Kuykendall <michaelallenkuykendall@gmail.com>
pkgname=contextlite-bin
pkgver=0.9.0
pkgrel=1
pkgdesc="AI-powered context management for developers (binary distribution)"
arch=('x86_64')
url="https://contextlite.com"
license=('MIT')
depends=()
conflicts=('contextlite')
source=("https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v${pkgver}/contextlite_${pkgver}_linux_amd64.tar.gz")
sha256sums=('SKIP')  # Will be updated with actual checksum

package() {
    install -Dm755 "${srcdir}/contextlite" "${pkgdir}/usr/bin/contextlite"
}
EOF

# Generate .SRCINFO
makepkg --printsrcinfo > .SRCINFO

# Test local build
makepkg -si --noconfirm

# Test installation
contextlite --version
timeout 10s contextlite --port 18081 &
sleep 5
curl -f http://localhost:18081/health || echo "FAIL: Health check failed"

# Commit to AUR
git add PKGBUILD .SRCINFO
git commit -m "Initial import: contextlite-bin 0.9.0"
git push
```

**Step 2: GitHub Actions AUR Test**
```bash
# Verify our automation works
# Check .github/workflows/publish-packages.yml includes AUR job
# Trigger with test release
git tag v0.9.0-aur-test
git push --tags

# Monitor: https://github.com/Michael-A-Kuykendall/contextlite/actions
```

**Step 3: Community Validation**
```bash
# Test installation from AUR
# (Requires actual Arch Linux system or container)
docker run --rm -it archlinux:latest bash -c "
  pacman -Sy --noconfirm git base-devel
  git clone https://aur.archlinux.org/contextlite-bin.git
  cd contextlite-bin
  makepkg -si --noconfirm
  contextlite --version
"
```

**Success Criteria**
- [ ] PKGBUILD builds successfully
- [ ] Package installs correctly on Arch Linux
- [ ] Binary executes with correct version
- [ ] Health endpoint responds
- [ ] AUR automation via GitHub Actions works
- [ ] Community can install via AUR helpers (yay, paru)

**Failure Scenarios to Test**
- [ ] SSH authentication failures
- [ ] PKGBUILD syntax errors
- [ ] Missing dependencies on Arch
- [ ] Checksum mismatches
- [ ] Permission issues

---

### 3. HOMEBREW INTEGRATION TEST

#### **Pre-Test Setup**
```bash
# Verify you have a Mac available for testing
echo "Required: macOS system for testing"
echo "Alternative: GitHub Actions with macos-latest runner"

# Verify homebrew-core fork exists
echo "Check: https://github.com/Michael-A-Kuykendall/homebrew-core"
```

#### **Test Execution Steps**

**Step 1: Formula Validation**
```bash
# On macOS or in GitHub Actions
# Test the homebrew formula locally first
cd homebrew
brew install --build-from-source ./contextlite.rb

# Test installation
contextlite --version
timeout 10s contextlite --port 18082 &
sleep 5
curl -f http://localhost:18082/health || echo "FAIL: Health check failed"

# Test formula audit
brew audit --strict contextlite.rb
brew style contextlite.rb
```

**Step 2: GitHub Actions Homebrew Test**
```bash
# Test the automation
git tag v0.9.0-homebrew-test
git push --tags

# Monitor the homebrew job specifically
# Verify:
# - Formula updates with new version
# - Checksums calculate correctly
# - PR created to homebrew-core
```

**Step 3: Homebrew Core Submission**
```bash
# Manual verification of PR
echo "Check: https://github.com/Homebrew/homebrew-core/pulls"
echo "Look for: contextlite formula submission"
echo "Verify: All automated tests pass"
```

**Success Criteria**
- [ ] Formula passes `brew audit --strict`
- [ ] Formula passes `brew style`
- [ ] Local installation works on macOS
- [ ] Binary executes correctly
- [ ] Health checks pass
- [ ] Automated PR creation works
- [ ] Homebrew CI tests pass

**Failure Scenarios to Test**
- [ ] Invalid formula syntax
- [ ] Checksum calculation errors
- [ ] macOS compatibility issues
- [ ] Build failures
- [ ] PR creation failures

---

### 4. DOCKER HUB INTEGRATION TEST

#### **Pre-Test Setup**
```bash
# Verify Docker Hub credentials
echo $DOCKERHUB_TOKEN | docker login --username michaelakuykendall --password-stdin

# Verify multi-platform build support
docker buildx version
docker buildx ls
```

#### **Test Execution Steps**

**Step 1: Local Docker Build Test**
```bash
# Create comprehensive Dockerfile
cat > Dockerfile.test << 'EOF'
FROM alpine:latest

# Install runtime dependencies
RUN apk add --no-cache ca-certificates

# Create non-root user
RUN adduser -D -s /bin/sh contextlite

# Copy binary
COPY contextlite /usr/local/bin/contextlite
RUN chmod +x /usr/local/bin/contextlite

# Set up directories
RUN mkdir -p /data /config && chown contextlite:contextlite /data /config

USER contextlite
WORKDIR /data

EXPOSE 8080
ENTRYPOINT ["/usr/local/bin/contextlite"]
CMD ["--port", "8080", "--data-dir", "/data"]
EOF

# Test build for multiple architectures
docker buildx build --platform linux/amd64,linux/arm64 -t contextlite:test .

# Test run
docker run -d --name contextlite-test -p 18083:8080 contextlite:test
sleep 10
curl -f http://localhost:18083/health || echo "FAIL: Health check failed"
docker logs contextlite-test
docker stop contextlite-test
docker rm contextlite-test
```

**Step 2: GitHub Actions Docker Test**
```bash
# Test automation
git tag v0.9.0-docker-test
git push --tags

# Monitor Docker Hub job
# Verify:
# - Multi-platform builds succeed
# - Images pushed to Docker Hub
# - Tags applied correctly
```

**Step 3: Public Docker Installation Test**
```bash
# Test public availability
docker run --rm michaelakuykendall/contextlite:0.9.0-docker-test --version

# Test with volume mounts
docker run -d --name contextlite-prod \
  -p 8080:8080 \
  -v $(pwd)/test-data:/data \
  michaelakuykendall/contextlite:0.9.0-docker-test

sleep 10
curl -f http://localhost:8080/health
docker logs contextlite-prod
docker stop contextlite-prod
docker rm contextlite-prod
```

**Success Criteria**
- [ ] Multi-platform builds (amd64, arm64) succeed
- [ ] Docker images run correctly
- [ ] Health endpoints respond
- [ ] Volume mounts work properly
- [ ] Non-root user security works
- [ ] Public pull and run works
- [ ] GitHub Actions automation works

**Failure Scenarios to Test**
- [ ] Build failures for different architectures
- [ ] Authentication issues with Docker Hub
- [ ] Permission problems in container
- [ ] Network connectivity issues
- [ ] Resource budgets

---

## 📋 PHASE 2: MEDIUM-RISK INTEGRATIONS

### 5. PYPI INTEGRATION TEST

#### **Test Execution Steps**

**Step 1: Python Package Build Test**
```bash
# Navigate to python wrapper
cd python-wrapper

# Install build dependencies
pip install build twine wheel

# Test package build
python -m build

# Verify package contents
tar -tzf dist/contextlite-*.tar.gz
unzip -l dist/contextlite-*.whl

# Test local installation
pip install dist/contextlite-*.whl
contextlite --version
timeout 10s contextlite --port 18084 &
sleep 5
curl -f http://localhost:18084/health || echo "FAIL: Health check failed"
pip uninstall contextlite -y
```

**Step 2: PyPI Upload Test**
```bash
# Test upload to TestPyPI first
python -m twine upload --repository testpypi dist/*

# Test installation from TestPyPI
pip install --index-url https://test.pypi.org/simple/ contextlite

# Test functionality
contextlite --version
```

**Success Criteria**
- [ ] Package builds without errors
- [ ] All files included correctly
- [ ] Installation works from PyPI
- [ ] Binary executes correctly
- [ ] Command-line interface works

---

### 6. VS CODE MARKETPLACE INTEGRATION TEST

#### **Test Execution Steps**

**Step 1: Extension Build Test**
```bash
cd vscode-extension

# Install dependencies
npm install

# Install vsce globally
npm install -g @vscode/vsce

# Build extension
npm run compile

# Package extension
vsce package

# Test installation
code --install-extension contextlite-*.vsix
```

**Step 2: Extension Functionality Test**
```bash
# Open VS Code and test:
# 1. Command palette: "ContextLite: Start Server"
# 2. Status bar shows ContextLite status
# 3. Right-click context menu has ContextLite options
# 4. Extension settings are accessible
```

**Success Criteria**
- [ ] Extension packages without errors
- [ ] Installs in VS Code successfully
- [ ] All commands work correctly
- [ ] Settings panel accessible
- [ ] ContextLite server integration works

---

## 📋 PHASE 3: LOW-RISK INTEGRATIONS

### 7-12. REMAINING INTEGRATIONS

**For each remaining integration (npm, GitHub Packages, Chocolatey, Scoop, winget, Cargo):**

#### **Standard Test Protocol**
1. **Build Test**: Package builds correctly
2. **Local Install Test**: Installs on target platform
3. **Functionality Test**: Binary executes and health checks pass
4. **Automation Test**: GitHub Actions workflow succeeds
5. **Public Availability Test**: Package available publicly
6. **Uninstall Test**: Clean removal works

---

## 🚨 FAILURE HANDLING PROTOCOL

### When Integration Tests Fail

**Step 1: Document the Failure**
```bash
# Create failure report
cat > integration-failure-$(date +%Y%m%d-%H%M%S).md << EOF
# Integration Test Failure Report

**Integration**: [Name]
**Date**: $(date)
**Phase**: [1/2/3]
**Error**: [Exact error message]

## Reproduction Steps
[Exact steps that led to failure]

## System Environment
[OS, versions, dependencies]

## Expected Behavior
[What should have happened]

## Actual Behavior
[What actually happened]

## Next Steps
[Specific actions to resolve]
EOF
```

**Step 2: Fix and Retest**
- Address the root cause
- Implement preventive measures
- Rerun the complete test for that integration
- Update documentation

**Step 3: Verify Fix Doesn't Break Others**
- Rerun any related integration tests
- Check for cascade failures

---

## 📊 INTEGRATION TEST DASHBOARD

### Test Status Tracking
```
Phase 1 (High-Risk):
[ ] Snap Store - Not Started / In Progress / Passed / Failed
[ ] AUR - Not Started / In Progress / Passed / Failed  
[ ] Homebrew - Not Started / In Progress / Passed / Failed
[ ] Docker Hub - Not Started / In Progress / Passed / Failed

Phase 2 (Medium-Risk):
[ ] PyPI - Not Started / In Progress / Passed / Failed
[ ] VS Code Marketplace - Not Started / In Progress / Passed / Failed
[ ] Chocolatey - Not Started / In Progress / Passed / Failed
[ ] Scoop - Not Started / In Progress / Passed / Failed

Phase 3 (Low-Risk):
[ ] npm - Not Started / In Progress / Passed / Failed
[ ] GitHub Packages - Not Started / In Progress / Passed / Failed
[ ] Cargo - Not Started / In Progress / Passed / Failed
[ ] winget - Not Started / In Progress / Passed / Failed
```

---

## 🎯 PRODUCTION READINESS CRITERIA

**All integrations must pass:**
- [ ] Build succeeds on all target platforms
- [ ] Installation works correctly
- [ ] Binary executes with correct version
- [ ] Health endpoints respond (< 500ms)
- [ ] Uninstallation is clean
- [ ] GitHub Actions automation works
- [ ] Public availability confirmed
- [ ] Documentation is complete

**Zero tolerance for:**
- Broken installations
- Missing dependencies
- Authentication failures
- Credential leaks
- Version mismatches
- Performance issues

---

## 🚀 FINAL VALIDATION

Before production launch, run complete end-to-end test:

```bash
# Test every marketplace installation
npm install -g contextlite
pip install contextlite
choco install contextlite
scoop install contextlite
winget install contextlite
brew install contextlite
snap install contextlite
# etc.

# Verify all installations work
for cmd in contextlite; do
  $cmd --version || echo "FAIL: $cmd not working"
  timeout 10s $cmd --port $((8080 + RANDOM % 1000)) &
  PID=$!
  sleep 5
  curl -f http://localhost:$PORT/health || echo "FAIL: $cmd health check"
  kill $PID 2>/dev/null
done
```

**Only proceed to production when ALL integrations pass ALL tests.**

---

**STATUS**: Ready to begin Phase 1 integration testing  
**NEXT**: Execute Snap Store integration test  
**TIMELINE**: Complete all phases before production launch
