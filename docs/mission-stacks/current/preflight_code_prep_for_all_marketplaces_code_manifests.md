# Preflight Code Prep for All Marketplaces (Code & Manifests)

**Goal:** Have every manifest, wrapper, installer, and CI script staged in your repos **before** you push the first public release. This makes “publish everywhere” a one‑button operation.

> Repo assumption: main public repo = `contextlite` (Free). Private Pro/Enterprise repo mirrors structure but omits public registries.

---

## 0) Common Repo Layout & Versioning

```
contextlite/
  cmd/contextlite/           # main CLI entry (Go) or src/bin (Rust)
  internal/...               # core libs
  docs/                      # user docs
  installers/                # per‑marketplace assets (brew, choco, snap, etc.)
  packaging/                 # icons, appdata, desktop files
  scripts/                   # helper scripts
  .goreleaser.yaml           # multi‑target build/publish
  .github/workflows/release.yml
  LICENSE
  README.md
```

**Semver tagging:** `v1.0.0` (tags drive all downstream pipelines).

**Artifact naming convention:** `contextlite_${GOOS}_${GOARCH}.(zip|tar.gz)` + `checksums.txt`.

**Signing:**

- Windows (signtool): `CERT_THUMBPRINT` in GitHub Secrets.
- macOS (codesign/notarytool): Apple App‑Specific password and keychain profile in Secrets.
- Provenance (cosign): `COSIGN_KEY` secret.

---

## 1) GitHub Actions – One Button Multi‑Publish

**.github/workflows/release.yml**

```yaml
name: release
on:
  push:
    tags: [ 'v*' ]
jobs:
  build-release:
    runs-on: ubuntu-latest
    permissions:
      contents: write
      id-token: write
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-go@v5
        with: { go-version: '1.22.x' }
      - name: Setup cosign
        uses: sigstore/cosign-installer@v3.5.0
      - name: Install goreleaser
        uses: goreleaser/goreleaser-action@v6
        with: { version: latest, args: release --clean }
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
          # macOS signing/notarization (if building on macOS runners separately)
          AC_PASSWORD: ${{ secrets.APPLE_APP_SPECIFIC_PASSWORD }}
          COSIGN_PASSWORD: ${{ secrets.COSIGN_PASSWORD }}
          COSIGN_KEY: ${{ secrets.COSIGN_KEY }}
```

**.goreleaser.yaml (excerpt)**

```yaml
dist: dist
before:
  hooks: [ 'go mod tidy' ]
builds:
  - id: contextlite
    main: ./cmd/contextlite
    env: [ CGO_ENABLED=0 ]
    goos: [ linux, darwin, windows ]
    goarch: [ amd64, arm64 ]
archives:
  - id: default
    builds: [ contextlite ]
    name_template: '{{ .ProjectName }}_{{ .Os }}_{{ .Arch }}'
    files: [ LICENSE, README.md ]
    format_overrides:
      - goos: windows
        format: zip
signs:
  - cmd: cosign
    signature: ${artifact}.sig
    args: [ 'sign-blob', '--yes', '--key=env://COSIGN_KEY', '--output-signature=${signature}', '${artifact}' ]
brews:
  - name: contextlite
    tap:
      owner: YOUR_GH
      name: homebrew-tap
    folder: Formula
    homepage: https://contextlite.com
    description: Single-file, zero-dependency context engine
scoops:
  - name: contextlite
    bucket:
      owner: YOUR_GH
      name: scoop-bucket
    homepage: https://contextlite.com
    description: Single-file, zero-dependency context engine
checksum: { name_template: 'checksums.txt' }
changelog: { use: github }
```

---

## 2) VS Code Extension (Visual Studio Marketplace)

**Files (repo **``**):**

```
package.json
extension.js
README.md
CHANGELOG.md
icon.png
```

**package.json**

```json
{
  "name": "contextlite-launcher",
  "displayName": "ContextLite Launcher",
  "publisher": "YOUR_PUBLISHER",
  "version": "1.0.0",
  "engines": { "vscode": ">=1.85.0" },
  "categories": ["Other"],
  "activationEvents": ["onCommand:contextlite.open"],
  "contributes": { "commands": [{ "command": "contextlite.open", "title": "Open ContextLite" }] },
  "main": "./extension.js",
  "repository": { "type": "git", "url": "https://github.com/YOUR_GH/contextlite" }
}
```

**extension.js**

```js
const vscode = require('vscode');
const cp = require('child_process');
function activate(ctx){
  ctx.subscriptions.push(vscode.commands.registerCommand('contextlite.open', () => {
    cp.spawn('contextlite', ['ui'], { detached: true });
    vscode.window.showInformationMessage('ContextLite started.');
  }));
}
function deactivate(){}
module.exports = { activate, deactivate };
```

**CI add-on:** add `vsce` packaging step in a separate workflow or manual.

---

## 3) JetBrains Plugin (IntelliJ Platform)

**Module **``**:**

```
build.gradle.kts
src/main/java/com/yourco/StartAction.java
src/main/resources/META-INF/plugin.xml
```

**build.gradle.kts**

```kotlin
plugins { id("org.jetbrains.intellij") version "1.17.3" }
intellij { version.set("2024.1") }
repositories { mavenCentral() }
```

**plugin.xml**

```xml
<idea-plugin>
  <id>com.yourco.contextlite</id>
  <name>ContextLite Launcher</name>
  <version>1.0.0</version>
  <vendor email="support@contextlite.com">ContextLite</vendor>
  <description>Start ContextLite from JetBrains IDEs.</description>
  <actions>
    <action id="ContextLite.Start" class="com.yourco.StartAction" text="Start ContextLite"/>
  </actions>
</idea-plugin>
```

**StartAction.java**

```java
package com.yourco;
import com.intellij.openapi.actionSystem.*;
import com.intellij.openapi.ui.Messages;
public class StartAction extends AnAction {
  @Override public void actionPerformed(AnActionEvent e){
    try { new ProcessBuilder("contextlite","ui").start(); }
    catch (Exception ex){ Messages.showErrorDialog("Failed to start ContextLite", "ContextLite"); }
  }
}
```

---

## 4) PyPI Wrapper

**Module **``**:**

```
pyproject.toml
contextlite/__init__.py
contextlite/__main__.py
scripts/fetch_binary.py
```

**pyproject.toml**

```toml
[project]
name = "contextlite"
version = "1.0.0"
description = "Single-file context engine wrapper"
readme = "README.md"
requires-python = ">=3.8"
[project.scripts]
contextlite = "contextlite.__main__:main"
[build-system]
requires = ["setuptools","wheel"]
build-backend = "setuptools.build_meta"
```

**contextlite/****main****.py**

```python
import os, sys, subprocess
from .fetch_binary import ensure_binary

def main():
    bin_path = ensure_binary()
    os.execv(bin_path, [bin_path] + sys.argv[1:])
```

**scripts/fetch\_binary.py**

```python
import os, platform, urllib.request, tarfile, zipfile, stat

RELEASE = os.getenv('CTX_RELEASE', 'latest')
BASE = 'https://github.com/YOUR_GH/contextlite/releases/download'

def ensure_binary():
    p = platform.system().lower(); a = platform.machine().lower()
    if a in ('x86_64','amd64'): a='amd64'
    if a in ('arm64','aarch64'): a='arm64'
    ext = 'zip' if p=='windows' else 'tar.gz'
    name = f"contextlite_{p}_{a}.{ext}"
    url = f"{BASE}/v1.0.0/{name}" if RELEASE!='latest' else f"{BASE}/v1.0.0/{name}"
    target = os.path.join(os.path.expanduser('~/.contextlite'), name)
    os.makedirs(os.path.dirname(target), exist_ok=True)
    if not os.path.exists(target): urllib.request.urlretrieve(url, target)
    outdir = os.path.dirname(target)
    if ext=='zip':
        with zipfile.ZipFile(target) as z: z.extractall(outdir)
    else:
        with tarfile.open(target) as t: t.extractall(outdir)
    bin_path = os.path.join(outdir, 'contextlite' + ('.exe' if p=='windows' else ''))
    os.chmod(bin_path, os.stat(bin_path).st_mode | stat.S_IEXEC)
    return bin_path
```

---

## 5) npm Wrapper

**Module **``**:**

```
package.json
bin/contextlite.js
scripts/fetch-binary.js
```

**package.json**

```json
{
  "name": "contextlite",
  "version": "1.0.0",
  "bin": { "contextlite": "bin/contextlite.js" },
  "scripts": { "postinstall": "node scripts/fetch-binary.js" }
}
```

**bin/contextlite.js**

```js
#!/usr/bin/env node
const { spawn } = require('child_process');
const { ensureBinary } = require('../scripts/fetch-binary');
(async () => {
  const bin = await ensureBinary();
  const p = spawn(bin, process.argv.slice(2), { stdio: 'inherit' });
  p.on('exit', code => process.exit(code));
})();
```

**scripts/fetch-binary.js**

```js
const os = require('os'), fs = require('fs'), path = require('path'), https = require('https'), zlib = require('zlib');
function arch(){ const a=os.arch(); return a==='x64'?'amd64':(a==='arm64'?'arm64':a) }
function plat(){ const p=os.platform(); return p==='win32'?'windows':(p==='darwin'?'darwin':'linux') }
const EXT = plat()==='windows'?'zip':'tar.gz'
const NAME = `contextlite_${plat()}_${arch()}.${EXT}`
const URL = `https://github.com/YOUR_GH/contextlite/releases/download/v1.0.0/${NAME}`
const DIR = path.join(os.homedir(), '.contextlite')
const FILE = path.join(DIR, NAME)
exports.ensureBinary = () => new Promise((resolve,reject)=>{
  fs.mkdirSync(DIR, { recursive:true })
  const f = fs.createWriteStream(FILE)
  https.get(URL, res=>{ res.pipe(f); f.on('finish', ()=>{ f.close(()=>{
    // TODO: extract zip/tar.gz then chmod
    const bin = path.join(DIR,'contextlite'+(plat()==='windows'?'.exe':''))
    resolve(bin)
  })})}).on('error', reject)
})
```

---

## 6) crates.io Wrapper

**Module **``**:**

```
Cargo.toml
src/main.rs
```

**Cargo.toml**

```toml
[package]
name = "contextlite"
version = "1.0.0"
edition = "2021"
[dependencies]
```

**src/main.rs**

```rust
use std::process::Command;
fn main(){
  let status = Command::new("contextlite").args(std::env::args().skip(1)).status().unwrap();
  std::process::exit(status.code().unwrap_or(1));
}
```

---

## 7) Go Module (if core is Go)

**go.mod (at repo root)**

```
module github.com/YOUR_GH/contextlite

go 1.22
```

**Install command documented:**

```
go install github.com/YOUR_GH/contextlite/cmd/contextlite@latest
```

---

## 8) Homebrew Tap & Scoop (Windows alt)

**Homebrew tap repo **``

```ruby
class Contextlite < Formula
  desc "Single-file, zero-dependency context engine"
  homepage "https://contextlite.com"
  version "1.0.0"
  on_macos do
    url "https://github.com/YOUR_GH/contextlite/releases/download/v1.0.0/contextlite_darwin_amd64.tar.gz"
    sha256 "REPLACE"
    def install; bin.install "contextlite"; end
  end
  on_linux do
    url "https://github.com/YOUR_GH/contextlite/releases/download/v1.0.0/contextlite_linux_amd64.tar.gz"
    sha256 "REPLACE"
    def install; bin.install "contextlite"; end
  end
end
```

**Scoop bucket **``

```json
{ "version": "1.0.0", "url": "https://github.com/YOUR_GH/contextlite/releases/download/v1.0.0/contextlite_windows_amd64.zip", "hash": "REPLACE", "bin": "contextlite.exe" }
```

---

## 9) Chocolatey Package

**Folder **``**:**

```
contextlite.nuspec
tools/chocolateyinstall.ps1
tools/chocolateyuninstall.ps1
```

**contextlite.nuspec**

```xml
<?xml version="1.0"?>
<package>
  <metadata>
    <id>contextlite</id>
    <version>1.0.0</version>
    <title>ContextLite</title>
    <authors>ContextLite</authors>
    <projectUrl>https://contextlite.com</projectUrl>
    <description>Single-file context engine</description>
  </metadata>
</package>
```

**tools/chocolateyinstall.ps1**

```powershell
$ErrorActionPreference = 'Stop'
$url = 'https://github.com/YOUR_GH/contextlite/releases/download/v1.0.0/contextlite_windows_amd64.zip'
$checksum = 'REPLACE'
Install-ChocolateyZipPackage -PackageName 'contextlite' -Url $url -UnzipLocation "$env:ChocolateyInstall\lib\contextlite" -Checksum $checksum -ChecksumType 'sha256'
Install-BinFile -Name 'contextlite' -Path "$env:ChocolateyInstall\lib\contextlite\contextlite.exe"
```

---

## 10) Docker (Hub or GHCR)

**Dockerfile (distroless)**

```dockerfile
FROM gcr.io/distroless/static:nonroot
COPY contextlite /usr/local/bin/contextlite
USER nonroot
ENTRYPOINT ["/usr/local/bin/contextlite"]
```

**Buildx script**

```bash
docker buildx build --platform linux/amd64,linux/arm64 \
  -t yourorg/contextlite:1.0.0 -t yourorg/contextlite:latest --push .
```

---

## 11) Snapcraft (Ubuntu)

**File **``

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

---

## 12) AUR (Arch)

**Folder **``**:**

```
PKGBUILD
```

**PKGBUILD**

```bash
pkgname=contextlite
pkgver=1.0.0
pkgrel=1
arch=('x86_64' 'aarch64')
depends=()
url='https://contextlite.com'
license=('custom')
source=("https://github.com/YOUR_GH/contextlite/releases/download/v${pkgver}/contextlite_linux_amd64.tar.gz")
sha256sums=('REPLACE')
package(){
  install -Dm755 "$srcdir/contextlite" "$pkgdir/usr/bin/contextlite"
}
```

---

## 13) Debian/Ubuntu PPA (Launchpad)

**Debianize folder **``**:**

```
control
changelog
rules
copyright
```

**debian/control**

```
Source: contextlite
Section: utils
Priority: optional
Maintainer: You <support@contextlite.com>
Standards-Version: 4.6.2

Package: contextlite
Architecture: any
Depends: ${shlibs:Depends}, ${misc:Depends}
Description: Single-file context engine
```

---

## 14) Fedora COPR (RPM)

**Spec **``

```
Name:           contextlite
Version:        1.0.0
Release:        1%{?dist}
Summary:        Single-file context engine
License:        Proprietary
URL:            https://contextlite.com
Source0:        https://github.com/YOUR_GH/contextlite/releases/download/v%{version}/contextlite_linux_amd64.tar.gz
%description
ContextLite CLI
%install
install -D -m 0755 contextlite %{buildroot}%{_bindir}/contextlite
%files
%{_bindir}/contextlite
```

---

## 15) Microsoft Store (MSIX)

**MSIX packaging assets (in **``**):**

```
AppxManifest.xml
images/* (Store icons)
```

**AppxManifest.xml (snippet)**

```xml
<Identity Name="ContextLite" Publisher="CN=YOURCOMPANY" Version="1.0.0.0" />
<Properties>
  <DisplayName>ContextLite</DisplayName>
  <PublisherDisplayName>Your Company</PublisherDisplayName>
</Properties>
```

---

## 16) Mac App (for notarized dmg or MAS wrapper)

**Xcode wrapper app** launching the CLI with a minimal UI; include:

- `Info.plist` with entitlement/sandbox (MAS) or hardened runtime (notarized dmg).
- `postinstall` script to place `contextlite` in `/usr/local/bin` (outside MAS).

---

## 17) Hugging Face Space (Gradio demo)

**Repo **``**:**

```
app.py
requirements.txt
README.md
```

**app.py (excerpt)**

```python
import gradio as gr, subprocess

def run(q):
  p = subprocess.run(["contextlite","query",q], capture_output=True, text=True)
  return p.stdout

gr.Interface(fn=run, inputs="text", outputs="text", title="ContextLite Demo").launch()
```

---

## 18) GitHub Action (Marketplace) – Setup Action

**Repo **``**:**

```
action.yml
index.js
```

**action.yml**

```yaml
name: Setup ContextLite
runs:
  using: node20
  main: index.js
inputs:
  version:
    description: Version to install
    required: false
    default: latest
```

**index.js** (download binary to runner)

```js
// Fetch release asset and add to PATH
```

---

## 19) OpenAI GPT Store Presence (awareness)

- Prepare: short README, website link, usage examples.
- Optional: lightweight HTTP endpoint for benchmarks; OpenAPI spec for Actions.

---

## 20) Affiliate Wiring (Stripe)

- Webhook → GitHub API invite for Pro repo.
- Coupon & referral code generator script in `/scripts/affiliates/`.

---

## 21) Trust Artifacts (attach to every release)

- `SBOM` (CycloneDX JSON) → `/dist/sbom.json`
- `checksums.txt` + `*.sig`
- `THIRD_PARTY_NOTICES.txt`
- `PRIVACY.md` & `TELEMETRY.md` (telemetry default off)

---

## 22) Local Test Matrix (pre‑release)

```
macOS: brew + tarball + notarized dmg
Windows 11: choco + zip + MSIX
Linux: docker + snap + AUR + deb/rpm
VS Code & JetBrains: install + launch binary
Python: pip wrapper; Node: npx wrapper; Rust: cargo run
```

**Once these files exist and the CI is green, tagging **``** will push artifacts to GitHub Releases and give every marketplace something to consume with minimal manual work.**

