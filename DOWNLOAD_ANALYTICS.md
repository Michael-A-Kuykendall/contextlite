# ContextLite Download Analytics

## 🎯 Current Status (Real Data!)

**Total Downloads: 2,208+** across all channels
- **NPM**: 1,876 downloads (last month) ⭐ **Top Performer**
- **Docker Hub**: 290 total pulls 
- **Crates.io**: 42 total downloads
- **PyPI**: ✅ **Published** (stats unavailable) 🆕
- **GitHub Releases**: 0 downloads## 🚀 Quick Commands

### Dashboard (Recommended)
```bash
make stats              # Beautiful dashboard view
make quick-stats        # One-liner summary
make track-downloads    # Update all statistics
make downloads-commit   # Update stats and commit
```

### Manual Scripts  
```bash
./scripts/dashboard.sh       # Pretty dashboard
./scripts/quick_stats.sh     # Fast one-liner check
./scripts/download_tracker.sh # Full data collection
```

### One-liner without dependencies:
```bash
curl -s "https://api.npmjs.org/downloads/range/last-month/contextlite" | grep -o '"downloads":[0-9]*' | grep -o '[0-9]*' | awk '{sum+=$1} END {print "NPM: "sum" downloads"}'
```

## 📊 Distribution Channels

### ✅ Active & Tracking
- **NPM**: https://www.npmjs.com/package/contextlite (API: Real-time)
- **Docker Hub**: https://hub.docker.com/r/makuykendall/contextlite (API: Live pulls)
- **Crates.io**: https://crates.io/crates/contextlite-client (API: Total downloads)
- **PyPI**: https://pypi.org/project/contextlite/ (Published v1.0.43) 🆕
- **GitHub Releases**: https://github.com/Michael-A-Kuykendall/contextlite/releases (API: Asset downloads)

### ⏳ Deployment Pending
- **Homebrew**: Formula ready, awaiting core inclusion
- **Snap Store**: Configuration ready, publishing in progress
- **AUR (Arch)**: PKGBUILD ready, SSH access issues  
- **VS Code Marketplace**: Extension ready, not yet published
- **Chocolatey**: Package ready, deployment disabled (slow approval)

### 📈 API Endpoints for Manual Checking

```bash
# NPM (30-day downloads)
curl -s "https://api.npmjs.org/downloads/range/last-month/contextlite"

# PyPI (recent downloads) 
curl -s "https://pypistats.org/api/packages/contextlite/recent"

# Docker Hub (total pulls)
curl -s "https://hub.docker.com/v2/repositories/makuykendall/contextlite/"

# Crates.io (total downloads)
curl -s "https://crates.io/api/v1/crates/contextlite-client"

# GitHub Releases (requires GITHUB_TOKEN)
curl -s -H "Authorization: token $GITHUB_TOKEN" \
  "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases"
```

## 📋 Output Format

### JSON Output (`download_stats.json`)
```json
{
  "timestamp": "2025-08-22T10:30:00Z",
  "total_downloads": 2208,
  "channels": {
    "npm": {
      "downloads": 1876,
      "url": "https://www.npmjs.com/package/contextlite", 
      "status": "success"
    },
    "docker": {
      "downloads": 290,
      "url": "https://hub.docker.com/r/makuykendall/contextlite",
      "status": "success"
    }
  }
}
```

### Dashboard View
```
╔══════════════════════════════════════════════════════════════╗
║                   📊 CONTEXTLITE DOWNLOADS                  ║
║                      Distribution Analytics                  ║
╚══════════════════════════════════════════════════════════════╝

🏆 TOP PERFORMING CHANNELS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
NPM Package
   📈 1,876 downloads

Docker Hub  
   📈 290 downloads
```

## 🔄 Automation

### Daily Tracking with Cron
```bash
# Edit crontab
crontab -e

# Add daily tracking at 6 AM
0 6 * * * cd /path/to/contextlite && make downloads-commit
```

### CI/CD Integration
```yaml
# GitHub Actions workflow to track downloads
- name: Update Download Statistics
  run: |
    make track-downloads
    git add download_stats.json
    git commit -m "Update download statistics" || exit 0
    git push
```

## 🎯 Key Insights

### Performance Metrics
- **NPM dominates** with 85% of downloads (1,876/2,208)
- **Docker Hub** shows strong container adoption (290 pulls)
- **Rust community** early adoption (42 downloads on Crates.io)
- **GitHub Releases** not yet popular (direct binary downloads)

### Distribution Strategy Success
- Package managers are more popular than direct downloads
- JavaScript/Node.js community leading adoption
- Container deployment showing good traction
- Rust integration working but smaller scale

### Next Steps
1. **Focus NPM marketing** - it's clearly the most effective channel
2. **Boost Docker adoption** - containers are gaining traction
3. **Complete pending deployments** - PyPI could be significant
4. **Track conversion metrics** - monitor trial-to-purchase rates

## 🛠️ Troubleshooting

### Common Issues
1. **Rate Limits**: GitHub API limited to 60 req/hour without token
2. **Missing Packages**: Some platforms don't have packages published yet  
3. **Network Timeouts**: Use `curl -v` for debugging connectivity
4. **JSON Parsing**: Bash scripts work without Python dependencies

### Debug Commands
```bash
# Test individual APIs
curl -v "https://api.npmjs.org/downloads/range/last-month/contextlite"

# Check GitHub token (if using)
curl -s -H "Authorization: token $GITHUB_TOKEN" \
  "https://api.github.com/user"

# Validate JSON output
cat download_stats.json | jq . > /dev/null && echo "Valid JSON" || echo "Invalid JSON"
```

### Environment Requirements
- **Bash**: Works on Linux, macOS, Windows (WSL/Git Bash)
- **curl**: For API requests  
- **grep/awk/sed**: Standard Unix tools
- **GITHUB_TOKEN**: Optional, for GitHub Releases data only
