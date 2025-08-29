# ContextLite Open Source Deployment Strategy

**Status**: Research Phase → Implementation Ready  
**Date**: August 29, 2025  
**Based on**: Analysis of proven open source deployment tools + current system audit

## 🎯 Executive Summary

After researching leading open source deployment solutions, I've identified the best practices to create a unified, reliable deployment system for ContextLite. Instead of reinventing the wheel, we'll adopt proven patterns from:

1. **GoReleaser** - Multi-platform binary releases with package manager distribution
2. **Release-It** - Version management, changelog generation, and release automation  
3. **Semantic Release** - Automated releases with conventional commits
4. **GitHub Actions Marketplace** - Pre-built deployment actions

## 🔍 Research Findings: What's Already Available

### 1. GoReleaser (⭐ 15.1k stars) - PERFECT FIT
**Purpose**: Automated release engineering for Go projects  
**What it does**:
- Cross-platform binary builds (Linux, Windows, macOS - all architectures)
- Package manager distribution (Homebrew, Chocolatey, Snap, AUR, Scoop)
- Docker multi-arch image builds
- GitHub/GitLab releases with assets
- Changelog generation
- Archive creation (.tar.gz, .zip, .deb, .rpm)

**Why it's perfect for us**:
- ✅ Go project (matches ContextLite)
- ✅ Supports ALL our target platforms
- ✅ Single config file (.goreleaser.yaml)
- ✅ Proven by 15k+ stars, used by major projects
- ✅ Handles exactly our use case

### 2. Release-It (⭐ 8.6k stars) - COMPLEMENTARY
**Purpose**: Version management and npm/GitHub releases  
**What it does**:
- Automated version bumping (semver)
- Git tagging and push
- Changelog generation
- GitHub/GitLab releases
- npm publishing
- Hook system for custom commands
- CI/CD integration

**Why it's useful**:
- ✅ Handles version lifecycle management
- ✅ Used by major projects (jQuery, Redux, Axios)
- ✅ Excellent for npm package coordination

### 3. Semantic Release (⭐ via marketplace) - AUTOMATION
**Purpose**: Fully automated releases based on commit messages  
**What it does**:
- Analyzes commit messages for release type
- Automatically determines version bumps
- Generates changelogs
- Creates GitHub releases
- Publishes to npm
- Plugin ecosystem

**Why it's interesting**:
- ✅ Zero manual version management
- ✅ Conventional commit standards
- ✅ Fully automated CI/CD

## 🏗️ Recommended Hybrid Strategy

### Phase 1: Adopt GoReleaser as Core Engine (1 week)

**Replace our complex 11-workflow system with single GoReleaser config:**

```yaml
# .goreleaser.yaml
version: 2

project_name: contextlite

before:
  hooks:
    - go mod tidy
    - go test ./...

builds:
  - env:
      - CGO_ENABLED=0
    goos:
      - linux
      - windows  
      - darwin
    goarch:
      - amd64
      - arm64
    main: ./cmd/contextlite

archives:
  - format: tar.gz
    name_template: >-
      {{ .ProjectName }}_
      {{- title .Os }}_
      {{- if eq .Arch "amd64" }}x86_64
      {{- else if eq .Arch "386" }}i386
      {{- else }}{{ .Arch }}{{ end }}
    format_overrides:
      - goos: windows
        format: zip

checksum:
  name_template: 'checksums.txt'

snapshot:
  name_template: "{{ incpatch .Version }}-next"

changelog:
  sort: asc
  filters:
    exclude:
      - '^docs:'
      - '^test:'

# Package Manager Distribution
brews:
  - name: contextlite
    homepage: https://contextlite.com
    description: "Mathematical optimization for context retrieval"
    repository:
      owner: Michael-A-Kuykendall
      name: homebrew-contextlite

chocolateys:
  - name: contextlite
    title: ContextLite
    authors: Michael Kuykendall
    project_url: https://contextlite.com
    url_template: "https://github.com/Michael-A-Kuykendall/contextlite/releases/download/{{ .Tag }}/{{ .ArtifactName }}"
    copyright: 2025 Michael Kuykendall
    package_source_url: https://github.com/Michael-A-Kuykendall/contextlite
    description: |
      Mathematical optimization for context retrieval.
      Replaces vector databases with 0.3ms search times.

snapcrafts:
  - name: contextlite
    summary: Mathematical optimization for context retrieval
    description: |
      ContextLite replaces vector databases with mathematical optimization.
      Get 0.3ms search times vs 50ms+ with traditional vector databases.
    grade: stable
    confinement: strict

nfpms:
  - file_name_template: '{{ .ConventionalFileName }}'
    id: packages
    homepage: https://contextlite.com
    description: |-
      Mathematical optimization for context retrieval.
      Replaces vector databases with 0.3ms search times.
    maintainer: Michael Kuykendall <michael@contextlite.com>
    license: Commercial
    vendor: ContextLite
    bindir: /usr/bin
    section: utils
    contents:
      - src: ./LICENSE
        dst: /usr/share/doc/contextlite/copyright
        file_info:
          mode: 0644
    formats:
      - apk
      - deb
      - rpm
      - termux.deb
      - archlinux

aurs:
  - name: contextlite-bin
    homepage: https://contextlite.com
    description: "Mathematical optimization for context retrieval"
    maintainers:
      - 'Michael Kuykendall <michael at contextlite dot com>'
    license: Commercial
    private_key: '{{ .Env.AUR_SSH_KEY }}'
    git_url: 'ssh://aur@aur.archlinux.org/contextlite-bin.git'
    depends:
      - glibc
    package: |-
      install -Dm755 "./contextlite" "${pkgdir}/usr/bin/contextlite"

dockers:
  - image_templates:
      - "contextlite/contextlite:{{ .Version }}-amd64"
      - "contextlite/contextlite:latest-amd64"
    dockerfile: Dockerfile
    use: buildx
    build_flag_templates:
      - "--platform=linux/amd64"
      - "--label=org.opencontainers.image.created={{.Date}}"
      - "--label=org.opencontainers.image.title={{.ProjectName}}"
      - "--label=org.opencontainers.image.revision={{.FullCommit}}"
      - "--label=org.opencontainers.image.version={{.Version}}"
  - image_templates:
      - "contextlite/contextlite:{{ .Version }}-arm64"
      - "contextlite/contextlite:latest-arm64"
    dockerfile: Dockerfile
    use: buildx
    build_flag_templates:
      - "--platform=linux/arm64"
      - "--label=org.opencontainers.image.created={{.Date}}"
      - "--label=org.opencontainers.image.title={{.ProjectName}}"
      - "--label=org.opencontainers.image.revision={{.FullCommit}}"
      - "--label=org.opencontainers.image.version={{.Version}}"

docker_manifests:
  - name_template: contextlite/contextlite:{{ .Version }}
    image_templates:
      - contextlite/contextlite:{{ .Version }}-amd64
      - contextlite/contextlite:{{ .Version }}-arm64
  - name_template: contextlite/contextlite:latest
    image_templates:
      - contextlite/contextlite:latest-amd64
      - contextlite/contextlite:latest-arm64
```

### Phase 2: Add Release-It for Version Management (3 days)

**package.json for npm wrapper + version coordination:**
```json
{
  "name": "contextlite",
  "version": "1.1.17",
  "scripts": {
    "release": "release-it",
    "release:ci": "release-it --ci --no-git.requireCleanWorkingDir"
  },
  "release-it": {
    "git": {
      "commitMessage": "chore: release v${version}",
      "tagName": "v${version}"
    },
    "github": {
      "release": true,
      "releaseName": "ContextLite v${version}",
      "tokenRef": "GITHUB_TOKEN"
    },
    "hooks": {
      "after:bump": "goreleaser release --clean",
      "after:release": "echo Successfully released ${name} v${version}"
    }
  }
}
```

### Phase 3: Unified Workflow (2 days)

**Single GitHub Action that coordinates everything:**
```yaml
# .github/workflows/unified-release.yml
name: Unified Release

on:
  push:
    branches: [main]
  workflow_dispatch:
    inputs:
      version:
        description: 'Version (auto, patch, minor, major)'
        default: 'auto'

jobs:
  release:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
          token: ${{ secrets.GITHUB_TOKEN }}

      - uses: actions/setup-go@v4
        with:
          go-version: '1.23'

      - uses: actions/setup-node@v4
        with:
          node-version: '18'

      # Phase 1: Determine version and create release
      - name: Release with Release-It
        run: npm run release:ci
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
          NPM_TOKEN: ${{ secrets.NPM_TOKEN }}

      # Phase 2: GoReleaser handles all package managers
      - name: Run GoReleaser
        uses: goreleaser/goreleaser-action@v6
        with:
          version: latest
          args: release --clean
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
          CHOCOLATEY_API_KEY: ${{ secrets.CHOCOLATEY_API_KEY }}
          AUR_SSH_KEY: ${{ secrets.AUR_SSH_KEY }}
          SNAPCRAFT_STORE_CREDENTIALS: ${{ secrets.SNAPCRAFT_STORE_CREDENTIALS }}
          DOCKER_USERNAME: ${{ secrets.DOCKERHUB_USERNAME }}
          DOCKER_PASSWORD: ${{ secrets.DOCKERHUB_TOKEN }}

      # Phase 3: Custom wrappers (npm, PyPI, etc.)
      - name: Deploy npm wrapper
        run: |
          cd npm-wrapper
          npm version ${{ env.RELEASE_VERSION }} --no-git-tag-version
          npm publish
        env:
          NPM_TOKEN: ${{ secrets.NPM_TOKEN }}

      - name: Deploy PyPI wrapper  
        run: |
          cd python-wrapper
          python setup.py sdist bdist_wheel
          twine upload dist/*
        env:
          TWINE_USERNAME: __token__
          TWINE_PASSWORD: ${{ secrets.PYPI_TOKEN }}
```

## 🚀 Implementation Plan

### Week 1: Core Migration
- [ ] **Day 1-2**: Install and configure GoReleaser
- [ ] **Day 3-4**: Test GoReleaser with our binary builds
- [ ] **Day 5-7**: Configure package managers (Homebrew, Chocolatey, Docker, AUR, Snap)

### Week 2: Integration
- [ ] **Day 1-2**: Add Release-It for version management
- [ ] **Day 3-4**: Create unified workflow
- [ ] **Day 5-7**: Test complete release pipeline

### Week 3: Wrapper Migration  
- [ ] **Day 1-3**: Move npm/PyPI wrappers to new system
- [ ] **Day 4-5**: Add missing platforms (WinGet, Scoop, Flathub)
- [ ] **Day 6-7**: Comprehensive testing

### Week 4: Cleanup & Documentation
- [ ] **Day 1-2**: Remove old workflows
- [ ] **Day 3-4**: Update documentation
- [ ] **Day 5-7**: Team training and final testing

## 🎯 Expected Benefits

### Reliability Improvements
- **From**: 11 competing workflows, 33% success rate
- **To**: Single GoReleaser config, 95%+ success rate

### Maintenance Reduction
- **From**: 1044 lines across 11 workflows
- **To**: ~200 lines in GoReleaser config + 50 lines workflow

### Platform Coverage
- **From**: 4/12 platforms working
- **To**: 12/12 platforms with standardized approach

### Development Speed
- **From**: Manual version management, complex debugging
- **To**: `git tag v1.x.x && git push --tags` → everything happens

## 🔧 Immediate Next Steps

1. **Install GoReleaser**: `go install github.com/goreleaser/goreleaser@latest`
2. **Initialize config**: `goreleaser init`
3. **Test local build**: `goreleaser build --single-target`
4. **Test release simulation**: `goreleaser release --snapshot --clean`
5. **Migrate gradually**: Start with binary builds, add package managers one by one

## 🎉 Success Definition

**Phase 1 Success**: GoReleaser builds and distributes to 8+ platforms automatically  
**Phase 2 Success**: Single `git tag` command triggers full deployment to all platforms  
**Phase 3 Success**: Zero manual intervention, 95%+ success rate, <30 minute deployment time

---

**Bottom Line**: Stop reinventing the wheel. GoReleaser + Release-It is exactly what we need and is used by thousands of successful projects. Let's adopt proven solutions instead of maintaining our complex custom system.
