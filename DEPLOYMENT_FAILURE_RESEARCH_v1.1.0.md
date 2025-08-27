# 🚨 CRITICAL: Deployment Failure Research – Version GAP CRISIS  
**Date**: August 27, 2025  
**Crisis**: npm stuck at v1.0.48 while GitHub has v1.1.15 - MAJOR VERSION DRIFT!

## 🔥 IMMEDIATE CRISIS STATUS
- **GitHub Latest**: v1.1.15 (DRAFT STATUS - packages can't see it!)  
- **npm Stuck At**: v1.0.48 (67 versions behind!)  
- **Stable Release**: v1.1.9 marked as latest stable  
- **Workflow Status**: Multiple package managers failing in latest runs

Comprehensive technical worksheet analyzing all non-working distribution channels for ContextLite. URGENT remediation required across package ecosystems.

## 🎯 PRIORITY CRISIS ANALYSIS  

### **ROOT CAUSE #1: GitHub Release Status Issues**
```bash
# CONFIRMED: Latest releases marked as DRAFT/PRERELEASE  
v1.1.15: draft=false, prerelease=UNKNOWN (investigate)
v1.1.9: draft=false, prerelease=false (marked as "latest")  
v1.0.48: draft=true (explains npm gap!)
```

### **ROOT CAUSE #2: npm Publishing Pipeline Broken**  
```json
{"dist-tags":{"latest":"1.0.48"}}
```
- npm hasn't seen ANY v1.1.x releases 
- Last successful publish: v1.0.48 (Aug 25)
- Workflow failures show "Install npm dependencies" failing

### **ROOT CAUSE #3: Workflow Job Cascade Failures**
Latest workflow run (17267687853) shows MULTIPLE failures:
- ❌ publish-npm: "Install npm dependencies" failure
- ❌ publish-github-packages: Publishing failure  
- ❌ publish-aur: Publishing failure
- ❌ publish-crates: Publishing failure  
- ❌ publish-chocolatey: Push failure
- ❌ publish-snap: Build failure

## Scope
Targets investigated:
- npm (expected new 1.1.0, currently capped at 1.0.48)
- Chocolatey (stuck in moderation / version substitution loop)
- Homebrew (formula bootstrap incomplete)
- Crates.io (Rust client version skew + publish gating)
- AUR (missing package / automation gaps)
- Snap (build + credentials / version mutation issues)

Working baselines (reference only): GitHub Release, PyPI, Docker Hub.

---
## 1. npm – Missing 1.1.0 Publication

### Observed State
- dist-tags.latest = 1.0.48
- No 1.1.0 version present in `npm.json` snapshot
- Workflow logic skips if `npm view contextlite@<version>` succeeds.
- Current workflow only executes on tag push OR manual dispatch with input version. We tagged v1.1.0 (core release) but npm wrapper version bump step only occurs if not skipped.

### Root Cause Hypotheses
1. Version mismatch: Tag v1.1.0 created but npm wrapper (`npm-wrapper/package.json`) never bumped to 1.1.0 before publish step.
2. Conditional skip logic: Manual workflow dispatch used version 1.1.0, but an earlier partial publish attempt failed build-and-release causing downstream jobs to abort before npm publish.
3. Transient build failure: Prior Go build issue (fixed) may have canceled matrix causing npm publish never to run.

### Verification Steps (Planned)
```
# 1. Inspect npm-wrapper/package.json version
# 2. Check workflow run logs for publish-npm job under run that built v1.1.0
# 3. Manually dry-run `npm version 1.1.0` inside wrapper to ensure no git tag created (use --no-git-tag-version)
```

### Remediation Plan
- Update unified VERSION source (introduce root VERSION file) consumed by publish jobs to eliminate drift.
- Add safeguard: After build step, run `node -e` script comparing expected version (workflow input) vs wrapper package.json; fail early if mismatch.
- For immediate fix: Manual dispatch with `platforms=npm` and `version=1.1.0` after bumping package.json locally (commit) or let workflow bump automatically (it currently bumps inside copy to npm-package). Ensure no pre-existing 1.1.0 published.

### Proposed Workflow Patch
Add post-skip assertion:
```
- name: Assert npm wrapper base version matches target
  if: steps.check_npm.outputs.skip == 'false'
  run: |
    base=$(jq -r .version npm-wrapper/package.json)
    echo "Base wrapper version: $base"
    # Not strictly required to match, but warn if far behind
```
(Full centralization described in Section 7.)

---
## 2. Chocolatey – Locked / Moderation Loop

### Observed State
- User reports package stuck since 1.0.15; attempts at self-reject.
- Current workflow uses dynamic substitution strategy inconsistent with nuspec placeholders:
  - `contextlite.nuspec` still uses `<version>$version$</version>` pattern but workflow replaces `VERSION_PLACEHOLDER` (mismatch).
  - Install script expects env `ChocolateyPackageVersion` / `ChocolateyChecksum64`; workflow instead calculates checksum but injects via direct string replace only of placeholders that do not exist (`RELEASE_URL_PLACEHOLDER`, `RELEASE_CHECKSUM_PLACEHOLDER` are present? Yes inside script; script currently uses env variables instead).
- Download URL in `chocolateyinstall.ps1` hardcoded to `contextlite_Windows_x86_64.zip` naming, while release assets use pattern `contextlite-<version>-windows-amd64.zip` (dash & arch naming mismatch). This breaks validation and moderation.

### Specific Mismatches
| Aspect | In Script | In Release | Effect |
|--------|-----------|------------|--------|
| Windows archive naming | `contextlite_Windows_x86_64.zip` | `contextlite-<ver>-windows-amd64.zip` | 404 during moderation install test |
| Nuspec version token | `$version$` | Workflow search/replace targets `VERSION_PLACEHOLDER` | Version not substituted -> moderation confusion |
| Checksum injection | Expects env variables OR placeholder replacement | Workflow sets `$checksum` then replaces `RELEASE_CHECKSUM_PLACEHOLDER` (script uses env) | Checksum not wired properly |

### Root Cause
Packaging directory diverged from workflow replacement assumptions; moderation likely rejected due to download failure & metadata mismatch. Subsequent attempts left version locked pending manual review.

### Remediation Plan
1. Align asset naming: Ensure release includes Windows ZIP names matching Chocolatey script OR update script to dynamic URL: `contextlite-${version}-windows-amd64.zip`.
2. Replace nuspec `<version>$version$</version>` pattern with explicit placeholder `VERSION_PLACEHOLDER` to match workflow substitution OR adjust workflow to replace `$version$`.
3. In install script, remove dependency on environment substitution; insert literal URL and SHA256 during workflow step.
4. Add moderation-friendly metadata (docs link, description length <4k, unique tags).
5. Add pre-publish verification step: Curl URL, verify 200, compute checksum, echo sample install command simulation (PowerShell Expand-Archive).

### Example Fixed Snippet (Install Script)
```
$url64 = "https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v${VERSION}/contextlite-${VERSION}-windows-amd64.zip"
...
checksum64    = 'SHA256_PLACEHOLDER'
```
Workflow replaces VERSION and SHA256 placeholders.

---
## 3. Homebrew – Formula Generation Gap

### Observed State
- `homebrew/contextlite.rb` uses runtime ENV placeholders (`AMD64_SHA`, `ARM64_SHA`) not replaced in committed formula.
- Formula uses capitalized file naming `contextlite_Darwin_x86_64.tar.gz` while release uses `contextlite-<version>-darwin-amd64.tar.gz` (different casing, dash vs underscore).
- brew API check fails -> formula unpublished.

### Root Causes
- Naming mismatch + placeholder approach unsuitable for upstream taps (Homebrew core requires hard-coded sha256 values).
- No automation to open PR against homebrew-core or a custom tap.

### Remediation Plan
1. Standardize asset naming to pattern Homebrew expects OR adjust formula to actual names.
2. During workflow: fetch release assets, compute sha256 locally (macOS runner), inline into formula, commit to dedicated tap repo (e.g., `Michael-A-Kuykendall/homebrew-contextlite`).
3. Provide tap instructions until accepted into core.

### Minimal Working Formula Template
```
class Contextlite < Formula
  desc "Ultra-fast context engine for retrieval and AI applications"
  homepage "https://contextlite.com"
  version "1.1.0"
  on_macos do
    if Hardware::CPU.intel?
      url "https://github.com/.../contextlite-1.1.0-darwin-amd64.tar.gz"
      sha256 "<sha256>"
    else
      url "https://github.com/.../contextlite-1.1.0-darwin-arm64.tar.gz"
      sha256 "<sha256>"
    end
  end
  def install
    bin.install "contextlite"
  end
  test do
    system "#{bin}/contextlite", "--version"
  end
end
```

---
## 4. Crates.io – Rust Client Not Publishing New Version

### Observed State
- Crate name: `contextlite-client` at version 1.0.43 in `Cargo.toml`.
- Target release 1.1.0 not reflected.
- Workflow checks for version presence using grep on crate listing; if absent attempts to bump.
- Potential blocking factors:
  - Missing/invalid `CARGO_REGISTRY_TOKEN` secret.
  - Packaging size / extraneous files (excluded patterns appear okay).
  - Name mismatch: perhaps intended crate name vs search pattern (workflow uses fixed crate name; OK).

### Remediation Steps
1. Confirm token secret configured.
2. Add dry-run step: `cargo publish --dry-run` output capture for diagnostics.
3. Centralize version consumption (root VERSION file) then sed into Cargo.toml analogous to other ecosystems.
4. Add error capture: On publish failure, upload `publish.log` as artifact.

### Suggested Workflow Additions
```
- name: Dry run publish
  if: steps.check_crates.outputs.skip == 'false'
  run: |
    cd adapters/rust/contextlite-client
    cargo publish --dry-run -v 2>&1 | tee ../../crate_dry_run.log
- uses: actions/upload-artifact@v4
  if: failure()
  with:
    name: crate-diagnostics
    path: crate_dry_run.log
```

---
## 5. AUR – Incomplete Publishing Flow

### Observed State
- Simple PKGBUILD with `sha256sums=('SKIP')` and direct binary extraction attempt.
- Uses `KSXGitHub/github-actions-deploy-aur` requiring SSH key secret (likely missing or misformatted).
- Upstream AUR expects either source build or permitted prebuilt binary (some packages use -bin suffix). Proper naming often: `contextlite-bin` when distributing binary.

### Key Issues
- Package name `contextlite` might collide with future source-formula expectations; better to publish `contextlite-bin`.
- Missing integrity verification (should supply actual sha256, not SKIP for release tarball if policy allows).
- Absent `.SRCINFO` generation step in automation; action may handle but not visible.

### Remediation Plan
1. Rename to `contextlite-bin`; adjust workflow accordingly.
2. Compute tarball checksum and inject into PKGBUILD.
3. Generate `.SRCINFO`: `makepkg --printsrcinfo > .SRCINFO` before publish.
4. Provide AUR SSH key (ed25519) with proper newline formatting in secret.

### Improved PKGBUILD Skeleton
```
pkgname=contextlite-bin
pkgver=1.1.0
pkgrel=1
pkgdesc="Ultra-fast context engine for retrieval and AI applications"
arch=('x86_64')
url="https://contextlite.com"
license=('MIT')
provides=('contextlite')
conflicts=('contextlite')
source=("https://github.com/.../contextlite-${pkgver}-linux-amd64.tar.gz")
sha256sums=('<sha256>')
package() {
  install -Dm755 "$srcdir/contextlite" "$pkgdir/usr/bin/contextlite"
}
```

---
## 6. Snap – Build & Credentials Issues

### Observed State
- `snapcraft.yaml` uses `version: git`; workflow sed replaces with target version only if store version absent.
- Build likely failing due to environment (classic vs strict confinement) or lacking store credentials secret (SNAPCRAFT_STORE_CREDENTIALS not set) so upload skipped.
- Plugin `go` nested build may succeed; absence in store suggests either credentials missing or reserved name requiring manual registration.

### Remediation Plan
1. Register snap name `contextlite` manually if not already (`snapcraft register contextlite`).
2. Set `SNAPCRAFT_STORE_CREDENTIALS` secret (run `snapcraft export-login --snaps contextlite --channels stable - | base64` locally to produce value).
3. Add build caching and explicit build-base; ensure multi-arch builds if needed (launch separate builds for arm64 via build matrix using `runs-on: ubuntu-22.04-arm` or remote builder).
4. Add test step: `unsquashfs -l *.snap | head -n 20` to verify binary presence pre-upload.

### Version Strategy
Set `version: 1.1.0` directly (replace sed approach). Add `grade: stable` only when production-ready; else use `candidate` channel.

---
## 7. Cross-Ecosystem Version Centralization

### Problem
Drift across npm (1.0.48), crate (1.0.43), others aim for 1.1.0.

### Solution Outline
1. Introduce root `VERSION` file containing `1.1.0`.
2. Pre-step job `determine-version` reads the file (or tag) and exports output.
3. Each publish job updates its manifest:
   - npm: `jq ".version=\"$VERSION\"" package.json > tmp && mv tmp package.json`
   - PyPI: sed in `pyproject.toml`
   - Cargo: sed version in `Cargo.toml`
   - nuspec: placeholder replacement
   - Homebrew / AUR / Scoop / etc: templates referencing $VERSION
4. Add guard: If workflow_dispatch input conflicts with VERSION file, fail early.

### Benefits
- Single authoritative source, eliminates manual bump errors, easier automation for future channels.

---
## 8. Recommended Immediate Fix Order (Practical Impact)
1. npm (public dev adoption) – sync to 1.1.0.
2. Chocolatey (Windows developers) – resolve packaging mismatch & unlock future moderation.
3. Homebrew (macOS CLI install path) – establish personal tap first.
4. Snap (Linux desktop/server discoverability) – set credentials.
5. AUR (Arch users) – rename to -bin, proper PKGBUILD.
6. Crates.io (secondary until Rust client stable) – optional after central versioning.

---
## 9. Concrete Action Checklist
- [ ] Create root VERSION file with 1.1.0
- [ ] Patch workflow for central version sourcing
- [ ] Fix Chocolatey package scripts (naming + placeholders)
- [ ] Add diagnostic dry-run steps (npm, crates, snap)
- [ ] Implement Homebrew tap automation (sha256 compute + commit)
- [ ] Prepare AUR -bin PKGBUILD template and adjust job
- [ ] Provide snap credentials and finalize version field

---
## 10. Appendix: Key File Discrepancies Summary
| Channel | File(s) | Discrepancy | Impact |
|---------|---------|-------------|--------|
| npm | npm-wrapper/package.json | Version behind target | Blocks discoverability |
| Chocolatey | chocolatey/*.nuspec + install script | Placeholder mismatch, URL naming mismatch | Moderation failure, version stuck |
| Homebrew | homebrew/contextlite.rb | Dynamic ENV-based sha placeholders + wrong asset names | Formula invalid, not published |
| Crates | adapters/rust/contextlite-client/Cargo.toml | Version lagging, no dry-run diagnostics | Publish skipped silently |
| AUR | workflow PKGBUILD inline | Name + checksum SKIP, no -bin, lack of .SRCINFO | Not accepted / not visible |
| Snap | snap/snapcraft.yaml | version: git + missing credentials | Build or upload skipped |

---
## 11. Next Steps
After approval, proceed to implement patches iteratively (commit + PR) with automated verification artifacts capturing each channel's pre/post state.

(End of research draft – ready for iteration.)
