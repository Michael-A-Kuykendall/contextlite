# ContextLite – All‑Channel Distribution & Guerrilla Launch Guide

Use this as your checklist to publish **everywhere** in one coordinated push. Each section has: **What it is**, **Prereqs**, **Packaging**, **Publish Steps**, **Review & Updates**, and **Pitfalls**. Where useful, I include minimal code/config you can paste into your repos.

---

## 0) Release Train & Signing (do this first)

**Goal:** Single command builds, signs, and ships to GitHub Releases, Homebrew, Chocolatey, Docker, and package registries.

### Prereqs

- Code-signing:
  - **Windows:** EV code-signing cert (preferred) or standard cert; configure `signtool`.
  - **macOS:** Apple Developer Program, Developer ID Application cert; set up `codesign`/`notarytool` for notarization & staple.
- GitHub account with public (Free) and private (Pro/Enterprise) repos.
- If Go: **goreleaser**; If Rust: **cargo-dist**; If mixed, still use goreleaser for multi‑arch binaries.

### Repo Structure (suggested)

```
contextlite/
  cmd/contextlite/         # main CLI (Go) or src/bin (Rust)
  installers/              # brew formula template, choco nuspec, snap, flatpak, docker
  packaging/               # icons, appdata, desktop files
  scripts/                 # CI helper scripts
  .goreleaser.yaml
```

### Example .goreleaser.yaml (excerpt, multi‑arch + brew + scoop template)

```yaml
dist: dist
before:
  hooks:
    - go mod tidy
builds:
  - id: contextlite
    main: ./cmd/contextlite
    env: [CGO_ENABLED=0]
    goos: [linux, darwin, windows]
    goarch: [amd64, arm64]
archives:
  - id: default
    builds: [contextlite]
    format_overrides:
      - goos: windows
        format: zip
    files: [LICENSE, README.md]
    wrap_in_directory: true
brews:
  - name: contextlite
    tap:
      owner: YOUR_GH_USER
      name: homebrew-tap
    commit_author: {name: "Release Bot", email: "bot@contextlite.com"}
    folder: Formula
    homepage: "https://contextlite.com"
    description: "Single-file, zero-dependency context engine"
    test: |
      system "#{bin}/contextlite", "--version"
scoops:
  - name: contextlite
    bucket:
      owner: YOUR_GH_USER
      name: scoop-bucket
    homepage: "https://contextlite.com"
    description: "Single-file, zero-dependency context engine"
    persist: []
checksum:
  name_template: "checksums.txt"
changelog:
  use: github
```

> Adjust for npm/PyPI/crates later; goreleaser will push GitHub Releases + taps.

### Signing & Notarization (macOS)

- Build → `codesign --deep --force -s "Developer ID Application: Your Name (TEAMID)" dist/contextlite_darwin_*`
- Notarize → `xcrun notarytool submit dist/*.zip --keychain-profile AC_PROFILE --wait`
- Staple → `xcrun stapler staple dist/*.zip`

### Signing (Windows)

- `signtool sign /fd SHA256 /tr http://timestamp.digicert.com /td SHA256 /a dist/contextlite_windows_amd64/contextlite.exe`

---

## 1) GitHub Releases (distribution backbone)

**What:** Canonical release host; devs trust it.

### Prereqs

- Repo public (Free). Private repo (Pro) with Releases enabled.

### Publish Steps

1. Tag: `git tag v1.0.0 && git push --tags`.
2. Run goreleaser: `goreleaser release --clean`.
3. Verify artifacts attached to Release (zip/tar.gz + checksums).
4. For **Pro**: run goreleaser in the **private** repo; attach binaries to a private Release.

### Review & Updates

- Keep latest tag pinned. Maintain changelog. Automate via GH Actions.

### Pitfalls

- Missing checksums or signatures reduces trust. Always include.

---

## 2) Visual Studio Code Marketplace (VSIX)

**What:** VS Code extension listing (Visual Studio Marketplace). Even a thin “launcher” gives massive discoverability.

### Prereqs

- Azure DevOps Publisher created (free) → gives `publisherId`.
- Install `vsce` (`npm i -g vsce`).
- Minimal extension structure:

```
.vscode-extension/
  package.json
  extension.js
  README.md
  CHANGELOG.md
```

**package.json (minimal):**

```json
{
  "name": "contextlite-launcher",
  "displayName": "ContextLite Launcher",
  "publisher": "YOUR_PUBLISHER",
  "version": "1.0.0",
  "engines": {"vscode": ">=1.85.0"},
  "categories": ["Other"],
  "activationEvents": ["onCommand:contextlite.open"],
  "contributes": {"commands": [{
    "command": "contextlite.open",
    "title": "Open ContextLite"
  }]},
  "main": "./extension.js"
}
```

**extension.js (launch binary or open docs):**

```js
const vscode = require('vscode');
const cp = require('child_process');
function activate(context) {
  const cmd = vscode.commands.registerCommand('contextlite.open', () => {
    cp.spawn('contextlite', ['ui'], {detached: true});
    vscode.window.showInformationMessage('ContextLite started.');
  });
  context.subscriptions.push(cmd);
}
function deactivate(){}
module.exports = { activate, deactivate };
```

### Publish Steps

1. `vsce package` → produces `.vsix`.
2. `vsce publish` (or upload in Marketplace portal).
3. Add icon, animated gif demo, keywords: `rag`, `vector`, `llm`, `context`.

### Review & Updates

- Auto‑update on version bump. Track installs & ratings in portal.

### Pitfalls

- Don’t bundle huge binaries; download on first run if needed.

---

## 3) JetBrains Marketplace (IntelliJ Platform Plugin)

**What:** Plugin discoverable in all JetBrains IDEs.

### Prereqs

- Gradle + `org.jetbrains.intellij` plugin.
- `plugin.xml` with metadata.

### Minimal build.gradle.kts

```kotlin
plugins {
  id("org.jetbrains.intellij") version "1.17.3"
  kotlin("jvm") version "1.9.24"
}
intellij { version.set("2024.1") }
repositories { mavenCentral() }
```

### plugin.xml (resources/META-INF/plugin.xml)

```xml
<idea-plugin>
  <id>com.yourco.contextlite</id>
  <name>ContextLite Launcher</name>
  <vendor email="support@contextlite.com">YourCo</vendor>
  <description>Start ContextLite and integrate quick actions.</description>
  <version>1.0.0</version>
  <depends>com.intellij.modules.platform</depends>
  <actions>
    <action id="ContextLite.Start" class="com.yourco.StartAction" text="Start ContextLite"/>
  </actions>
</idea-plugin>
```

### Publish Steps

1. Build plugin: `./gradlew buildPlugin` → `build/distributions/*.zip`.
2. Create JetBrains Marketplace account, new plugin, upload zip.
3. Provide screenshots, short video, tags.

### Pitfalls

- API version drift—pin to LTS IDE version.

---

## 4) PyPI (Python wrapper)

**What:** `pip install contextlite` for Python devs.

### Prereqs

- `pyproject.toml` with `setuptools`/`hatchling`.
- Wrapper exposes CLI via `console_scripts`.

### pyproject.toml (minimal)

```toml
[project]
name = "contextlite"
version = "1.0.0"
description = "Single-file context engine"
authors = [{name = "You", email = "dev@contextlite.com"}]
readme = "README.md"
requires-python = ">=3.8"

[project.scripts]
contextlite = "contextlite.__main__:main"

[build-system]
requires = ["setuptools", "wheel"]
build-backend = "setuptools.build_meta"
```

### contextlite/**main**.py

```python
import subprocess, sys

def main():
    subprocess.call(["contextlite"] + sys.argv[1:])
```

### Publish Steps

1. Build: `python -m build`.
2. Upload: `twine upload dist/*` (use API token).
3. Test: `pip install contextlite`.

### Pitfalls

- Name collisions—check availability first.

---

## 5) npm (Node wrapper)

**What:** `npx contextlite` or `npm i -g contextlite`.

### package.json (excerpt)

```json
{
  "name": "contextlite",
  "version": "1.0.0",
  "bin": {"contextlite": "bin/contextlite.js"},
  "scripts": {"postinstall": "node scripts/fetch-binary.js"}
}
```

### scripts/fetch-binary.js (download latest from GitHub Releases)

```js
const os = require('os'), https = require('https'), fs = require('fs'), path = require('path');
// detect platform, construct URL to GitHub Releases asset, download to ./bin/contextlite
```

### Publish Steps

1. `npm login`.
2. `npm publish --access public`.
3. Verify: `npx contextlite --version`.

### Pitfalls

- Postinstall scripts must handle proxies and retries.

---

## 6) crates.io (Rust)

**What:** `cargo install contextlite`.

### Two options

- **Wrapper crate** that shells out to your binary (fast to ship).
- **Native Rust client** if you expose a library API.

### Publish Steps

1. `cargo login`.
2. `cargo publish` (needs `Cargo.toml` with `[[bin]]`).
3. Tag releases consistently.

### Pitfalls

- crates.io forbids large vendor blobs—keep it thin.

---

## 7) Go Modules (if core is Go)

**What:** `go install github.com/YOUR/repo/cmd/contextlite@latest`.

### Steps

1. Ensure module path is correct in `go.mod`.
2. Tag semver `v1.0.0`.
3. Document install: `go install ...@latest`.

### Pitfalls

- Private modules require GOPRIVATE—avoid for Free path.

---

## 8) Homebrew (macOS)

**What:** `brew install contextlite` via your tap, automated by goreleaser.

### Steps

1. Create tap repo `homebrew-tap`.
2. Let goreleaser generate the formula on release.
3. Users: `brew tap YOUR/tap && brew install contextlite`.

### Pitfalls

- For homebrew-core, strict review—start with your tap.

---

## 9) Chocolatey (Windows)

**What:** `choco install contextlite`.

### Files

```
chocolatey/
  contextlite.nuspec
  tools/chocolateyinstall.ps1
  tools/chocolateyuninstall.ps1
```

**chocolateyinstall.ps1**

```powershell
$ErrorActionPreference = 'Stop'
$url = 'https://github.com/YOUR/repo/releases/download/v1.0.0/contextlite_windows_amd64.zip'
$checksum = 'SHA256_HERE'
Install-ChocolateyZipPackage -PackageName 'contextlite' -Url $url -UnzipLocation "$env:ChocolateyInstall\lib\contextlite" -Checksum $checksum -ChecksumType 'sha256'
Install-BinFile -Name 'contextlite' -Path "$env:ChocolateyInstall\lib\contextlite\contextlite.exe"
```

### Publish Steps

1. `choco apikey --key=XXXX --source=https://push.chocolatey.org/`
2. `choco pack` → `choco push`.

### Pitfalls

- Keep checksums updated per release.

---

## 10) Docker Hub / GHCR

**What:** `docker pull yourorg/contextlite`.

### Dockerfile (distroless + static)

```dockerfile
FROM gcr.io/distroless/static:nonroot
COPY contextlite /usr/local/bin/contextlite
USER nonroot
ENTRYPOINT ["/usr/local/bin/contextlite"]
```

### Steps

1. Multi‑arch build: `docker buildx build --platform linux/amd64,linux/arm64 -t yourorg/contextlite:1.0.0 --push .`
2. Latest tag: `:latest`.

### Pitfalls

- If you need extra libs, use `alpine` base and pin versions.

---

## 11) Mac App Store (optional; CLI tools are a poor MAS fit)

**What:** GUI wrapper app that embeds/launches the CLI.

### Steps (high level)

1. Create minimal notarized sandboxed app (Swift/Catalyst) that launches ContextLite or provides UI.
2. App Store Connect listing (icons, screenshots, privacy).
3. Pass sandbox guidelines.

### Pitfalls

- MAS often rejects background/CLI tools. Consider outside‑store notarized downloads instead.

---

## 12) Microsoft Store (Windows)

**What:** List a Win32 app via MSIX packaging.

### Steps

1. Package with MSIX (or create GUI wrapper installer `.msi`).
2. Partner Center account; create product; upload package; age ratings; metadata.
3. Submit; respond to certification feedback.

### Pitfalls

- SmartScreen reputation—use EV cert and accumulate installs.

---

## 13) Linux Repos

**Fast paths first:** Snap, Flatpak, AUR, Launchpad PPA, Fedora COPR.

### Snapcraft

- `snap/snapcraft.yaml` minimal:

```yaml
name: contextlite
base: core22
version: 1.0.0
summary: Single-file context engine
description: ContextLite CLI
grade: stable
confinement: classic
apps:
  contextlite:
    command: bin/contextlite
parts:
  contextlite:
    plugin: dump
    source: ./dist/linux_amd64
```

- Build & push with `snapcraft`.

### Flatpak (Flathub)

- Provide `.desktop` and metainfo if GUI; for CLI, publish via wrappers or skip.

### AUR (Arch)

- Create `PKGBUILD` fetching tarball from GitHub, install to `/usr/bin/contextlite`.

### Launchpad PPA (Ubuntu/Debian)

- Use `debuild` to create `.deb`; upload to PPA; users add PPA and `apt install contextlite`.

### Fedora COPR (RPM)

- Spec file to build RPM; host in COPR for `dnf install contextlite`.

### Pitfalls

- Each ecosystem has review delays; start with Snap + AUR + PPA for fastest wins.

---

## 14) Hugging Face (Spaces & Models)

**What:** Demo space + model stub for discoverability.

### Spaces

1. Create Space (Gradio/Streamlit) demonstrating ContextLite speed vs vector DB.
2. Include a small dataset; run CLI inside Space.
3. Add tags: `tool`, `retrieval`, `rag-alternative`.

### Models

- Publish a lightweight “ContextLite Sample Index” model card linking to your site and repo.

---

## 15) GitHub Marketplace (Action + App)

**Action** (fast path)

1. Repo `action-contextlite-setup` with `action.yml` that downloads/installs binary.
2. Tag a release `v1`.
3. Publish to Marketplace as an **Action**.

**GitHub App** (optional)

1. Register GitHub App (Developer Settings); scopes: repo read.
2. Provide OAuth flow; optional marketplace listing with pricing (if you want paid plans here).

---

## 16) OpenAI “Extensions” / GPT Store Presence (optional)

**Goal:** A GPT that teaches ContextLite and links to downloads; optional action calling your public API.

### Steps

1. Create a public GPT profile; add knowledge (your docs), website, and support link.
2. (Optional) Define an Action schema that calls a read‑only endpoint (e.g., benchmarks).
3. Publish; add store tags.

### Pitfalls

- Policies drift; treat this as awareness, not primary distribution.

---

## 17) Appcast / Auto‑Update (optional but useful)

- Host a simple JSON feed of latest version + checksums.
- CLI can check and prompt to update; disable for air‑gapped users by default.

---

## 18) Affiliate / Reseller Mechanics

- Create Stripe affiliate links with 20% rev share.
- Generate unique coupon codes; issue via auto‑email post‑application.
- Provide a one‑pager and 30‑sec benchmark clip affiliates can reuse.

---

## 19) Coordinated Launch Checklist (Day ‑7 to Day +7)

**Day ‑7**: Finalize signing, release v1.0.0 to GitHub; brew/choco formulas green. **Day ‑6**: Publish npm, PyPI, crates, Go tag; verify installs. **Day ‑5**: Docker multi‑arch push; Snap/AUR/PPA submissions. **Day ‑4**: VS Code extension submit; JetBrains plugin upload. **Day ‑3**: Create Hugging Face Space demo; record benchmark gif. **Day ‑2**: Write 5 comparison posts (Medium, Dev.to, Hashnode, LinkedIn Articles, GitHub Pages). **Day ‑1**: Update website CTAs with badges (GitHub, Brew, Choco, Docker). **Day 0**: Press “Publish” on all marketplaces; post Reddit/Twitter/LinkedIn threads with benchmarks. **Day +1..+7**: Answer issues, push 1.0.1 hotfix if needed; request reviews; activate affiliates.

---

## 20) Minimal Snippets Library

### Brew Tap README snippet

```
brew tap YOUR/tap
brew install contextlite
```

### Choco Install snippet

```
choco install contextlite
```

### Docker Run snippet

```
docker run --rm -v "$PWD:/data" yourorg/contextlite:latest contextlite index /data
```

### npm / npx

```
npx contextlite --help
```

### pip

```
pip install contextlite
```

### Go install

```
go install github.com/YOUR/repo/cmd/contextlite@latest
```

---

## 21) Common Compliance & Trust To‑Dos

- Publish **SBOM** (CycloneDX) per release.
- Include **checksums** and **sigstore/cosign** signatures.
- Ship **LICENSE** and third‑party notices.
- Add **Privacy & Telemetry** detail; default to off.

---

## 22) Fast Support Loop

- Create `support@contextlite.com` alias.
- Pin GitHub Discussions Q&A.
- 1‑page Troubleshooting: AV false positives, macOS quarantine, proxy issues.

---

## 23) Metrics to Watch

- GitHub stars, release downloads, brew and choco install stats.
- VS Code/JetBrains installs & retention.
- Conversion: Free → Pro (14‑day trial exits).

---

### Final Notes

- Treat **GitHub Releases** as your gold source; other channels fetch from it.
- Automate everything with CI—manual steps will break under load.
- Keep messaging consistent: "Single‑file. Zero deps. Faster than vector DBs."

