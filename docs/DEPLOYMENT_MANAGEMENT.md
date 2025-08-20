# Deployment & Platform Management

## Overview

ContextLite is deployed across multiple platforms and needs coordinated management. This document covers all deployment channels and their administration.

## 🚀 Deployment Channels

### 1. **Hugging Face Spaces** (Primary Download Experience)
- **URL**: https://huggingface.co/spaces/MikeKuykendall/contextlite-download  
- **Repository**: `contextlite-download/` subdirectory
- **Auto-Deploy**: Connected to HF Spaces for instant deployment
- **Management Guide**: See [`../HUGGING_FACE_MANAGEMENT.md`](../HUGGING_FACE_MANAGEMENT.md)

**Quick Management**:
```bash
cd contextlite-download
# Edit app.py for changes
git add app.py && git commit -m "Update: description" && git push
# Auto-deploys to Hugging Face within 2 minutes
```

### 2. **GitHub Releases** (Multi-Platform Binaries)
- **Auto-Build**: GitHub Actions on tag push
- **Platforms**: Windows, macOS (x64/ARM64), Linux (x64/ARM64)
- **Trigger**: `git tag v1.x.x && git push --tags`

### 3. **Package Managers** (Wrappers)
- **npm**: `npm-wrapper/` → https://www.npmjs.com/package/contextlite
- **PyPI**: `python-wrapper/` → https://pypi.org/project/contextlite/
- **VS Code**: `vscode-extension/` → VS Code Marketplace

### 4. **Documentation**
- **GitHub Wiki**: Complete technical reference
- **Main Site**: https://contextlite.com

## 🔧 Management Workflows

### Release Process
1. **Tag Release**: `git tag v1.x.x && git push --tags`
2. **GitHub Actions**: Auto-builds all platforms
3. **Hugging Face**: Auto-updates download page
4. **Package Managers**: Manual publish (see wrapper directories)

### Hugging Face Updates
```bash
cd contextlite-download
code app.py  # Make changes
python -m py_compile app.py  # Check syntax
git add app.py && git commit -m "Update: description" && git push
```

### Emergency Fixes
- **Hugging Face**: Direct edit in `contextlite-download/app.py`
- **GitHub**: Hotfix branch → PR → merge
- **Packages**: Version bump in respective wrapper directories

## 📊 Platform Analytics & Marketing

### Download Statistics Sources
- **GitHub**: Release download counts
- **npm**: npmjs.com package stats
- **PyPI**: pypi.org download analytics  
- **VS Code**: Marketplace install counts
- **Hugging Face**: Space view/usage metrics

### Cross-Platform Marketing Strategy
When releasing updates, leverage all channels for maximum impact.

**→ See [`MARKETING_BLAST_STRATEGY.md`](MARKETING_BLAST_STRATEGY.md) for detailed marketing exploitation plan**

Key opportunity: Each package manager has thousands of daily visitors searching for AI tools. Update all descriptions simultaneously to create marketing blast effect.

## 📋 Maintenance Checklist

### Weekly
- [ ] Check all download links work
- [ ] Monitor Hugging Face page performance
- [ ] Review package manager stats

### Per Release
- [ ] Update Hugging Face page if needed
- [ ] Verify GitHub releases deployed correctly
- [ ] Update package manager descriptions
- [ ] Cross-link all platforms

### Monthly
- [ ] Review analytics across all platforms
- [ ] Update performance stats if improved
- [ ] Refresh marketing copy
- [ ] Check competitor landscape

## 🎯 Marketing Blast Strategy

When you release updates, you can "blast" across all platforms:

### 1. **Package Manager Updates**
Each package page is SEO gold:
- **npm**: ~500k weekly views for popular packages
- **PyPI**: ~1M+ weekly Python package searches
- **VS Code**: ~10M+ extension searches monthly

### 2. **Content Strategy** 
Update all package descriptions with:
```markdown
# ContextLite: RAG Systems Were a Mistake

Replace slow, approximate vector databases with mathematically optimal context selection.
- ⚡ **0.3ms** response time (vs 30-50ms for vector DBs)
- 🎯 **Provably optimal** results via optimization solving  
- 💰 **$0** ongoing costs (vs $300-500/month for cloud vector DBs)
- 🔒 **100% local** - your data never leaves your machine

[**Download now →**](https://huggingface.co/spaces/MikeKuykendall/contextlite-download)
```

### 3. **SEO Amplification**
- Each package manager page links to your site
- Keywords get distributed across multiple high-authority domains
- Creates natural backlink profile
- Drives traffic from developer-focused audiences

## 🔗 Cross-Platform Integration

### Consistent Messaging
All platforms should echo the same core message:
1. **Hook**: "RAG Systems Were a Mistake" 
2. **Problem**: Vector databases are slow & expensive
3. **Solution**: Mathematical optimization in 0.3ms
4. **Proof**: Performance benchmarks
5. **CTA**: Download from Hugging Face

### Traffic Funnel
```
npm/PyPI/VS Code → Hugging Face → GitHub → Website → Purchase
```

### Link Strategy
- **Package Managers**: Link to Hugging Face download
- **Hugging Face**: Link to GitHub and main site
- **GitHub**: Link to purchase page
- **Main Site**: Complete sales funnel
