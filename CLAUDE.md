# ContextLite Project - Claude Development Guide

## Working GitHub API Commands

### ✅ CONFIRMED WORKING - Deploy to Chocolatey
```bash
# Trigger selective Chocolatey deployment (TESTED & WORKING)
cd "C:\Users\micha\repos\contextlite"
curl -X POST -H "Authorization: Bearer $GITHUB_TOKEN" -H "Accept: application/vnd.github.v3+json" \
  "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/workflows/deploy-selective.yml/dispatches" \
  -d '{"ref":"main","inputs":{"platforms":"chocolatey","version":"1.1.3","force_deploy":"true"}}'
```

### ✅ CONFIRMED WORKING - GitHub Release API Access
```bash
# Check GitHub releases (TESTED & WORKING)
cd "C:\Users\micha\repos\contextlite" 
curl -H "Authorization: Bearer $GITHUB_TOKEN" "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases/tags/v1.1.1"
```

## Project Structure Notes

- Main repo: `C:\Users\micha\repos\contextlite`
- Chocolatey packages: Fixed with placeholder approach for URL/checksum replacement
- VS Code extension: Manual marketplace uploads with .vsix files
- Hugging Face: Auto-deploys via git push to contextlite-download folder
- GitHub token: Available as `$GITHUB_TOKEN` environment variable

## Critical Fixes Applied

### Chocolatey Deployment Issue (RESOLVED)
- **Root Cause**: Install script used env variables, workflow expected placeholders
- **Fix**: Updated chocolatey/tools/chocolateyinstall.ps1 to use RELEASE_URL_PLACEHOLDER and RELEASE_CHECKSUM_PLACEHOLDER
- **Result**: Workflow now properly replaces URLs and checksums

### Selective Deployment Workflow (RESOLVED)  
- **Root Cause**: Windows ZIP had wrong structure (nested directories instead of flat)
- **Fix**: Updated .github/workflows/deploy-selective.yml to create flat ZIP with contextlite.exe at root
- **Result**: Chocolatey verification should pass

## Deployment Status
- **Chocolatey**: 🎉 SUCCESS v1.1.4 - DEPLOYED! After weeks of debugging, finally working!
- **VS Code**: Manual upload process, currently at v1.1.2 
- **Hugging Face**: Working with analytics tracking
- **Homebrew**: Needs workflow conflict resolution
- **NPM/Docker**: Status to be verified

## Recent Fixes Applied (Latest)

### 🎉 FINAL BREAKTHROUGH - CHOCOLATEY DEPLOYMENT SUCCESS (Aug 26, 2025)
- **Result**: ContextLite v1.1.4 successfully deployed to Chocolatey!
- **Timeline**: Resolved 2+ week deployment blockage 
- **Status**: GitHub Actions workflow now fully automated and working
- **Next**: Monitor Chocolatey approval process for v1.1.4

### 📝 Placeholder Mismatch Fix (FINAL PIECE - Aug 26, 2025)  
- **Root Cause**: nuspec file used `$version$` but workflow expected `VERSION_PLACEHOLDER`
- **Error**: `choco pack` command failing during package creation
- **Fix**: Updated contextlite.nuspec to use `VERSION_PLACEHOLDER` consistently
- **Result**: Chocolatey package creation now succeeds

### 🚨 CRITICAL BINARY PRESERVATION FIX (BREAKTHROUGH - Aug 26, 2025)
- **Root Cause**: Workflow was DELETING binaries immediately after building them!
- **Error**: `cp: cannot stat 'contextlite-linux-amd64': No such file or directory`
- **Fix**: Removed incorrect `rm -f contextlite-linux-amd64 contextlite-darwin-amd64 contextlite-darwin-arm64` cleanup step
- **Impact**: This was the PRIMARY cause blocking Chocolatey deployment for weeks
- **Result**: All platform binaries now preserved for proper archive creation

### Archive Creation Fix (RESOLVED - Aug 26, 2025)
- **Root Cause**: `rm -rf` command failing on non-existent files in workflow
- **Fix**: Added proper error handling with `2>/dev/null || true`  
- **Result**: Archive creation step now passes, enables Chocolatey deployment to proceed