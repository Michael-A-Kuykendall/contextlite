# 🔧 HUMAN ACTIONS CHECKLIST
*ContextLite Deployment Recovery Plan*

## 🚨 CRITICAL ACTIONS (Do First - 30 minutes)

### 1. Fix Build-and-Release Job (BLOCKS 5+ PACKAGES)
- [ ] **Test build command locally**:
  ```bash
  cd /c/Users/micha/repos/contextlite
  go build ./cmd/contextlite          # Test this vs
  go build ./cmd/contextlite/main.go  # This (current failing command)
  ```
- [ ] **Identify correct build path** and update `.github/workflows/publish-packages.yml`
- [ ] **Verify go.mod** has all required dependencies
- [ ] **Test multi-platform build locally**:
  ```bash
  GOOS=linux GOARCH=amd64 go build -o test-linux ./cmd/contextlite
  GOOS=windows GOARCH=amd64 go build -o test-windows.exe ./cmd/contextlite
  ```

### 2. Verify GitHub Secrets
- [ ] **Check CHOCOLATEY_API_KEY** in GitHub repository secrets
- [ ] **Check CARGO_REGISTRY_TOKEN** in GitHub repository secrets  
- [ ] **Check DOCKERHUB_USERNAME** and **DOCKERHUB_TOKEN**
- [ ] **Generate missing tokens** where needed

---

## ⚠️ HIGH PRIORITY ACTIONS (1-2 hours)

### 3. Fix Chocolatey Version Lag
- [ ] **Test Chocolatey package locally**:
  ```powershell
  cd chocolatey
  choco pack
  ```
- [ ] **Verify API key works**:
  ```powershell
  choco apikey -k YOUR_API_KEY -source https://push.chocolatey.org/
  ```
- [ ] **Check community.chocolatey.org** account permissions
- [ ] **Debug why v1.0.38 didn't publish** (check workflow logs)

### 4. Update Homebrew Formula
- [ ] **Calculate SHA256 checksums** for v1.0.38:
  ```bash
  # Download and calculate checksums
  curl -L "https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v1.0.38/contextlite-1.0.38-darwin-amd64.tar.gz" | sha256sum
  curl -L "https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v1.0.38/contextlite-1.0.38-darwin-arm64.tar.gz" | sha256sum
  ```
- [ ] **Update homebrew/contextlite.rb** with new version and checksums
- [ ] **Test formula locally** (if on macOS):
  ```bash
  brew install --build-from-source ./homebrew/contextlite.rb
  ```

### 5. Setup Missing Credentials

#### Snap Store
- [ ] **Create Snapcraft developer account** at https://snapcraft.io/
- [ ] **Generate store credentials**:
  ```bash
  snapcraft login
  snapcraft export-login snapcraft-credentials
  base64 snapcraft-credentials  # Add to GitHub secrets
  ```
- [ ] **Add SNAPCRAFT_STORE_CREDENTIALS** to GitHub secrets

#### AUR (Arch User Repository)
- [ ] **Create AUR account** at https://aur.archlinux.org/
- [ ] **Generate SSH key**:
  ```bash
  ssh-keygen -t rsa -b 4096 -f ~/.ssh/aur_key -C "your-email@example.com"
  ```
- [ ] **Add public key** to AUR account settings
- [ ] **Add private key** to GitHub secrets as **AUR_SSH_KEY**

#### Crates.io
- [ ] **Verify crates.io account** at https://crates.io/
- [ ] **Generate new API token**:
  - Go to https://crates.io/me
  - Create new token with "Publish new crates" permission
- [ ] **Add CARGO_REGISTRY_TOKEN** to GitHub secrets
- [ ] **Test token locally**:
  ```bash
  cd adapters/rust/contextlite-client
  cargo login YOUR_TOKEN
  cargo publish --dry-run
  ```

---

## 📦 PACKAGE-SPECIFIC FIXES (2-4 hours)

### 6. Fix Snap Configuration
- [ ] **Update snap/snapcraft.yaml** version to be dynamic
- [ ] **Change confinement** from `strict` to `classic` if needed
- [ ] **Test snap build locally**:
  ```bash
  sudo snap install snapcraft --classic
  snapcraft --destructive-mode
  ```

### 7. Fix Crates Version
- [ ] **Update Cargo.toml version** from 1.0.37 to 1.0.38
- [ ] **Test Rust client compilation**:
  ```bash
  cd adapters/rust/contextlite-client
  cargo build --release
  cargo test  # Make sure tests pass
  ```

### 8. Test Docker Hub
- [ ] **Verify Docker Hub account** makuykendall/contextlite
- [ ] **Check if 249 downloads** are legitimate users
- [ ] **Test Docker image locally**:
  ```bash
  docker pull makuykendall/contextlite:latest
  docker run makuykendall/contextlite:latest --help
  ```

---

## 🔮 FUTURE IMPLEMENTATION (4-8 hours)

### 9. Enable Disabled Package Managers

#### Scoop (Windows)
- [ ] **Fork ScoopInstaller/Main** repository on GitHub
- [ ] **Create dist/scoop/contextlite.json** manifest
- [ ] **Test Scoop installation locally**:
  ```powershell
  scoop install your-manifest.json
  ```

#### WinGet (Windows)
- [ ] **Configure winget-releaser** action
- [ ] **Create winget manifest** in Microsoft/winget-pkgs
- [ ] **Test WinGet installation**:
  ```powershell
  winget install Michael-A-Kuykendall.ContextLite
  ```

#### Flathub (Linux)
- [ ] **Create Flatpak manifest** com.contextlite.ContextLite.yml
- [ ] **Submit to Flathub** repository
- [ ] **Test Flatpak build**:
  ```bash
  flatpak-builder build-dir com.contextlite.ContextLite.yml --force-clean
  ```

#### Nix (NixOS)
- [ ] **Create Nix package definition** 
- [ ] **Submit PR to nixpkgs** repository
- [ ] **Test Nix installation**:
  ```bash
  nix-env -iA nixpkgs.contextlite
  ```

---

## ✅ VERIFICATION CHECKLIST

### After Each Fix
- [ ] **Trigger manual workflow** with workflow_dispatch
- [ ] **Monitor GitHub Actions** for successful completion
- [ ] **Check package manager** for new version availability
- [ ] **Test installation** from that package manager
- [ ] **Update download tracking** script

### Final Verification
- [ ] **All 12 package managers** working
- [ ] **Version consistency** (all showing v1.0.38+)
- [ ] **Download numbers** increasing across channels
- [ ] **Automated monitoring** functioning
- [ ] **Revenue tracking** ready for trial conversions

---

## 🎯 SUCCESS CRITERIA

**Technical Success**:
- ✅ 12/12 package managers deployed and working
- ✅ All packages showing current version (v1.0.38+)
- ✅ Automated deployment on git tag releases
- ✅ Download tracking working across all channels

**Business Success**:
- ✅ 5,000+ total downloads across all channels
- ✅ Multiple distribution channels active
- ✅ Trial-to-purchase funnel operational
- ✅ Revenue tracking and conversion monitoring

**Operational Success**:
- ✅ No manual intervention required for releases
- ✅ Automated failure detection and alerts
- ✅ Version consistency across all platforms
- ✅ Performance monitoring dashboard

---

## 📞 SUPPORT RESOURCES

**Documentation**: 
- GitHub Actions: https://docs.github.com/en/actions
- Chocolatey: https://docs.chocolatey.org/en-us/create/create-packages
- Snap: https://snapcraft.io/docs
- AUR: https://wiki.archlinux.org/title/AUR_submission_guidelines

**Testing Environments**:
- Docker: Local testing with Docker Desktop
- Linux: Use GitHub Actions ubuntu-latest runner
- Windows: Use GitHub Actions windows-latest runner  
- macOS: Use GitHub Actions macos-latest runner

**Recovery Strategy**:
If a package manager breaks:
1. Disable it in the workflow (add `if: false`)
2. Fix the issue locally
3. Test the fix
4. Re-enable and deploy
5. Monitor for 24 hours

---

**Total Estimated Time**: 8-12 hours over 2-3 days
**Priority Order**: build-and-release → Chocolatey → credentials → package fixes → new implementations
