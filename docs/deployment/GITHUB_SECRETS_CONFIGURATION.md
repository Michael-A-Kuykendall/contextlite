# 🔐 GITHUB SECRETS CONFIGURATION
**Purpose**: Secure storage for all distribution platform API keys  
**Repository**: Michael-A-Kuykendall/contextlite

## 📋 REQUIRED SECRETS LIST

### Core Distribution Secrets
| Secret Name | Purpose | Platform | Status |
|-------------|---------|----------|---------|
| `GITHUB_TOKEN` | GitHub releases, packages | GitHub | ✅ Built-in |
| `NPM_TOKEN` | npm package publishing | npm | ⏳ Pending |
| `PYPI_TOKEN` | PyPI package publishing | PyPI | ⏳ Not needed (OIDC) |
| `DOCKER_TOKEN` | Docker Hub publishing | Docker Hub | ⏳ Pending |
| `VSCE_TOKEN` | VS Code extension publishing | Azure DevOps | ⏳ Pending |
| `CHOCOLATEY_API_KEY` | Chocolatey package publishing | Chocolatey | ⏳ Pending |

### Optional/Future Secrets  
| Secret Name | Purpose | Platform | Status |
|-------------|---------|----------|---------|
| `JETBRAINS_TOKEN` | JetBrains plugin publishing | JetBrains | ⏳ Pending |
| `SNAPCRAFT_STORE_CREDENTIALS` | Snap Store publishing | Canonical | ⏳ Pending |
| `COSIGN_PRIVATE_KEY` | Binary signing | cosign | ⏳ Future |
| `GPG_PRIVATE_KEY` | Package signing | GPG | ⏳ Future |

## 🔧 SECRET CONFIGURATION STEPS

### 1. Access GitHub Secrets
1. Go to: https://github.com/Michael-A-Kuykendall/contextlite/settings/secrets/actions
2. Click "New repository secret"
3. Add each secret individually

### 2. PyPI (OIDC Trusted Publisher - No Secret Needed)
PyPI uses OpenID Connect trusted publishing, which doesn't require storing tokens:
```yaml
# Already configured in release.yml workflow
- name: Publish to PyPI
  uses: pypa/gh-action-pypi-publish@release/v1
  with:
    packages-dir: python-wrapper/dist/
```

### 3. npm Token
```bash
# After creating npm account:
npm login
npm token create --type=automation --scope=public
# Copy token and add as NPM_TOKEN secret
```

### 4. Docker Token  
```bash
# After creating Docker Hub account:
# Go to: https://hub.docker.com/settings/security
# Create new access token with read/write permissions
# Add as DOCKER_TOKEN secret
```

### 5. VS Code Extension Token
```bash
# After creating Azure DevOps organization:
# Install vsce: npm install -g vsce
vsce create-publisher contextlite
# Create PAT with Marketplace (publish) permissions
# Add as VSCE_TOKEN secret
```

### 6. Chocolatey API Key
```bash
# After creating Chocolatey account:
# Go to: https://community.chocolatey.org/account
# Copy API key from account settings
# Add as CHOCOLATEY_API_KEY secret
```

## 🧪 TESTING SECRET ACCESS

### Test Workflow (Optional)
Create `.github/workflows/test-secrets.yml` to verify secret access:
```yaml
name: Test Secrets Access
on: workflow_dispatch

jobs:
  test-secrets:
    runs-on: ubuntu-latest
    steps:
      - name: Test NPM Token
        run: echo "NPM token length: ${#NPM_TOKEN}"
        env:
          NPM_TOKEN: ${{ secrets.NPM_TOKEN }}
      
      - name: Test Docker Token  
        run: echo "Docker token length: ${#DOCKER_TOKEN}"
        env:
          DOCKER_TOKEN: ${{ secrets.DOCKER_TOKEN }}
      
      # Add similar tests for other secrets
```

## 🚨 SECURITY BEST PRACTICES

### Secret Management
1. **Principle of Least Privilege**: Only grant minimum required permissions
2. **Regular Rotation**: Rotate tokens every 90 days or after incidents
3. **Monitoring**: Monitor token usage and access patterns
4. **Backup Access**: Ensure multiple team members can regenerate tokens

### Token Scopes
- **npm**: Automation token with publish scope only
- **Docker**: Read/write permissions for specific repositories
- **VSCE**: Marketplace publish permissions only
- **Chocolatey**: Package push permissions only

### Incident Response
1. **Compromise Detection**: Monitor for unauthorized token usage
2. **Immediate Revocation**: Revoke compromised tokens immediately
3. **Token Regeneration**: Generate new tokens with same permissions
4. **Audit Trail**: Review all actions performed with compromised tokens

---

## ✅ VERIFICATION COMMANDS

After setting up secrets, verify they work:

```bash
# Test goreleaser with secrets (dry run)
goreleaser release --snapshot --clean --skip-publish

# Test individual platforms
npm whoami  # Test npm authentication
docker login ghcr.io  # Test Docker authentication
vsce ls-publishers  # Test VS Code authentication
```

---

**Next Steps**: Execute BUSINESS_ACCOUNT_SETUP_GUIDE.md to create all accounts and generate API keys.
