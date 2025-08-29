# 🔐 Private Binary Installation Guide

## Current Status: Missing Private SMT Binary

**Problem**: Context assembly API failing because `contextlite-library` binary not found
**Impact**: SMT optimization disabled, falling back to core engine only
**Solution**: Install private binary for full professional features

## 🔍 Current Binary Search Paths

The system searches for `contextlite-library` (or `contextlite-library.exe` on Windows) in:

1. `./` (current directory)
2. `../contextlite-private/build/` (development setup)
3. `/usr/local/bin/` (system install)
4. `./bin/` (relative to executable)
5. `../bin/` (parent bin directory)

## 🎯 Installation Options

### Option 1: Development Setup (Recommended)
```bash
# Clone the private repository alongside public repo
cd /c/Users/micha/repos/
git clone <private-repo-url> contextlite-private
cd contextlite-private
make build-library

# Binary will be at: ../contextlite-private/build/contextlite-library.exe
# ContextLite will auto-detect it from the main repo
```

### Option 2: Local Installation
```bash
# Download or build the private binary
# Place it in one of these locations:

# Current directory (easiest for testing)
cp contextlite-library.exe /c/Users/micha/repos/contextlite/

# System installation
sudo cp contextlite-library /usr/local/bin/

# Relative to executable
mkdir -p /c/Users/micha/repos/contextlite/bin/
cp contextlite-library.exe /c/Users/micha/repos/contextlite/bin/
```

### Option 3: Direct Download from Private Releases
```bash
# If private repo has releases, download latest binary
wget <private-repo-releases-url>/contextlite-library.exe
chmod +x contextlite-library.exe
mv contextlite-library.exe ./
```

## 🧪 Testing Binary Installation

```bash
# Test if binary is detected
cd /c/Users/micha/repos/contextlite
./contextlite --test-smt

# Check engine status via API
curl -s http://localhost:8084/api/v1/engine/info
```

**Expected Output with Private Binary**:
```json
{
  "type": "private-optimized",
  "features": ["smt-optimization", "7d-features", "patent-pending"],
  "description": "Full SMT-optimized engine with proprietary algorithms",
  "communication": "json-cli"
}
```

**Current Output (Core Engine Only)**:
```json
{
  "type": "core-engine", 
  "features": ["bm25-scoring", "heuristic-selection", "production-ready"],
  "description": "Core engine with proven BM25 and heuristic algorithms",
  "communication": "direct"
}
```

## 🔧 Troubleshooting

### Binary Not Found
- Verify file exists: `ls -la contextlite-library*`
- Check permissions: `chmod +x contextlite-library.exe`
- Test execution: `./contextlite-library.exe --version`

### Wrong Architecture
- Ensure binary matches your system (Windows x64, Linux x64, etc.)
- Download correct architecture from private repo releases

### Permission Denied
```bash
# Fix permissions
chmod +x contextlite-library
# Or on Windows
icacls contextlite-library.exe /grant Everyone:F
```

## 📞 Getting Private Access

If you need access to the private repository:

1. **Contact**: Repository owner for private repo access
2. **License**: Ensure you have valid professional license
3. **Purpose**: Development use requires special access token

## 🎯 Post-Installation Verification

After installing private binary:

1. **Restart ContextLite**: `contextlite stop && contextlite start`
2. **Check Engine Type**: API should show "private-optimized"
3. **Test SMT Features**: Context assembly should work with full optimization
4. **Monitor Logs**: Look for "Private JSON CLI engine loaded" messages

---

**Status**: Ready for private binary installation
**Next**: Choose installation method and acquire private binary
