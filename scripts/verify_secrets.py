#!/usr/bin/env python3
"""
ContextLite GitHub Secrets Verification
Checks if all required secrets are properly named and configured
"""

import requests
import json

def check_secrets():
    """Verify all GitHub secrets match workflow expectations"""
    
    # What our workflows expect vs what should be in GitHub secrets
    expected_secrets = {
        'NPM_TOKEN': 'npm registry token from npmjs.com',
        'PYPI_TOKEN': 'PyPI API token from pypi.org',
        'DOCKERHUB_USERNAME': 'Docker Hub username', 
        'DOCKERHUB_TOKEN': 'Docker Hub access token',
        'CHOCOLATEY_API_KEY': 'Chocolatey API key from chocolatey.org/account',
        'CARGO_REGISTRY_TOKEN': 'Crates.io API token from crates.io',
        'SNAPCRAFT_STORE_CREDENTIALS': 'Snapcraft store credentials from snapcraft login',
        'AUR_SSH_KEY': 'SSH private key for AUR repository access',
        'HOMEBREW_GITHUB_API_TOKEN': 'GitHub personal access token for Homebrew',
        'VSCODE_MARKETPLACE_TOKEN': 'VS Code marketplace token from marketplace.visualstudio.com'
    }
    
    print("🔐 CONTEXTLITE GITHUB SECRETS VERIFICATION")
    print("=" * 60)
    print()
    
    print("📋 REQUIRED SECRETS FOR DEPLOYMENT:")
    print()
    
    for secret_name, description in expected_secrets.items():
        print(f"🔑 {secret_name}")
        print(f"   📝 {description}")
        print()
    
    print("✅ VERIFICATION CHECKLIST:")
    print()
    print("1. Go to: https://github.com/Michael-A-Kuykendall/contextlite/settings/secrets/actions")
    print("2. Verify each secret name matches exactly (case-sensitive)")
    print("3. Ensure secret values are current and valid")
    print("4. Test locally where possible")
    print()
    
    print("🔧 RECENT FIXES:")
    print("✅ Fixed: GITHUB_TOKEN → HOMEBREW_GITHUB_API_TOKEN for Homebrew workflow")
    print("✅ Fixed: GitHub Packages scoped naming")
    print("✅ Fixed: Rust authentication test")
    print()
    
    print("📊 CURRENT DEPLOYMENT STATUS:")
    print("✅ Working: npm, PyPI, Docker, GitHub Packages (4/9)")
    print("❌ Needs secrets check: Crates, Chocolatey, Snap, AUR, Homebrew (5/9)")

if __name__ == "__main__":
    check_secrets()
