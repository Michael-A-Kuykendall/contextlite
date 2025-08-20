# URGENT: GitHub Actions Workflow Fix Required

**Date**: August 20, 2025  
**Priority**: CRITICAL - Blocking Homebrew/Chocolatey publishing

## Problem Summary
Two workflows conflict on tags trigger:
- simple-release.yml (DISABLED ✅)
- publish-packages.yml (needs dependency removal ❌)

## Required Fix
Remove 'needs: build-and-release' from:
- Line ~273: publish-chocolatey job  
- Line ~497: publish-homebrew job

## Why This Works
Homebrew/Chocolatey download from existing releases, don't need fresh builds.

## Test
Create v1.0.33 tag to verify jobs execute (not skip).

## IDE Cache Issue
If edits don't persist, close VS Code and use external editor.
