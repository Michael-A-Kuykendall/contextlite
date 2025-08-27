# ContextLite Scripts Directory

This directory contains various automation and analysis scripts for the ContextLite project. Scripts are organized by purpose and include both legacy deployment tools and new PUNCH-powered analysis capabilities.

## 📊 **PUNCH-Powered Analysis Scripts** (NEW)

These scripts leverage the PUNCH discovery tool to provide deep insights into your codebase.

### `analyze-architecture.ps1` / `analyze-architecture.sh`
**Purpose**: Comprehensive architecture analysis of the ContextLite codebase

**What it does**:
- Discovers all Go components (functions, structs, interfaces, variables)
- Generates architecture documentation in JSON format
- Analyzes HTTP handlers and API patterns
- Creates component inventory and statistics
- Maps function relationships and dependencies

**Usage**:
```powershell
# PowerShell (Windows)
cd C:\Users\micha\repos\contextlite
powershell.exe -File scripts\analyze-architecture.ps1

# Bash (Linux/WSL)
./scripts/analyze-architecture.sh
```

**Outputs**:
- `punch_results/components.json` - All discovered components with metadata
- `punch_results/http_handlers.txt` - HTTP handler analysis
- `punch_results/stats.json` - Codebase statistics and metrics
- `punch_results/functions.txt` - Function inventory

### `punch-quality-check.ps1` / `punch-quality-check.sh`
**Purpose**: Code quality analysis and technical debt assessment

**What it does**:
- Analyzes function complexity across the codebase
- Identifies performance hotspots and optimization opportunities
- Scans for security patterns (auth, crypto, license validation)
- Reviews test coverage and test file organization
- Generates quality metrics and recommendations

**Usage**:
```powershell
powershell.exe -File scripts\punch-quality-check.ps1
```

**Outputs**:
- `punch_results/quality/functions.txt` - Function complexity analysis
- `punch_results/quality/structs.txt` - Struct dependency analysis
- `punch_results/quality/performance.txt` - Performance hotspot detection
- `punch_results/quality/security.txt` - Security pattern analysis
- `punch_results/quality/tests.txt` - Test coverage analysis

### `punch-deployment-analysis.sh`
**Purpose**: Deployment configuration and workflow complexity analysis

**What it does**:
- Analyzes deployment configurations and package managers
- Reviews GitHub Actions workflows
- Examines Docker and containerization setup
- Assesses build system complexity
- Evaluates release automation processes

**Usage**:
```bash
./scripts/punch-deployment-analysis.sh
```

**Outputs**:
- `punch_results/deployment/config_components.json` - Deployment components
- `punch_results/deployment/package_managers.txt` - Package manager analysis
- `punch_results/deployment/workflows.txt` - GitHub Actions analysis
- `punch_results/deployment/docker.txt` - Docker configuration review
- `punch_results/deployment/build_system.txt` - Build system analysis
- `punch_results/deployment/releases.txt` - Release automation review

---

## 📈 **Download Analytics Scripts**

These scripts track ContextLite's distribution across multiple platforms.

### `dashboard.sh`
**Purpose**: Interactive download analytics dashboard

**What it does**:
- Displays comprehensive download statistics from all platforms
- Shows package manager deployment status
- Provides color-coded status indicators
- Tracks npm, Docker, Crates.io, GitHub releases
- Monitors PyPI, Homebrew, Snap Store, AUR, VS Code, Chocolatey

**Usage**:
```bash
./scripts/dashboard.sh
```

**Features**:
- Real-time download counts with formatting
- Platform health status indicators
- Quick action commands
- Automatic stat file generation if missing

### `download_tracker.sh` / `download_tracker.py`
**Purpose**: Multi-platform download statistics collection

**What they do**:
- Fetches download statistics from npm, Docker Hub, Crates.io, PyPI
- Checks package deployment status across platforms
- Generates `download_stats.json` with comprehensive metrics
- Tracks historical download trends

**Usage**:
```bash
./scripts/download_tracker.sh
# OR
python scripts/download_tracker.py
```

### `quick_stats.sh`
**Purpose**: Fast download statistics summary

**What it does**:
- Provides instant download count overview
- Shows key metrics without full dashboard
- Useful for CI/CD and quick checks

**Usage**:
```bash
./scripts/quick_stats.sh
```

---

## 🚀 **Deployment Scripts**

These scripts handle various deployment scenarios and server management.

### `deploy.sh`
**Purpose**: Main deployment automation script

**What it does**:
- Handles production deployment workflows
- Manages server provisioning and configuration
- Coordinates multi-platform releases

### `production-deploy.sh`
**Purpose**: Production-specific deployment script

**What it does**:
- Production environment deployment
- Safety checks and rollback capabilities
- Production server configuration

### `provision-server.sh`
**Purpose**: Server infrastructure setup

**What it does**:
- Sets up new servers for ContextLite deployment
- Configures server dependencies and environment
- Installs required services and configurations

### `deploy-web-terminal.sh`
**Purpose**: Web terminal deployment for demos

**What it does**:
- Deploys web-based terminal interface
- Sets up demonstration environment
- Configures public-facing demo instances

---

## 🔧 **Utility Scripts**

### `verify_secrets.py`
**Purpose**: Security validation for deployment credentials

**What it does**:
- Validates GitHub secrets and API tokens
- Checks deployment credential integrity
- Ensures security compliance before releases

### `monitor_deployment.py` / `monitor_v1039_deployment.sh`
**Purpose**: Deployment monitoring and tracking

**What they do**:
- Monitor active deployments across platforms
- Track deployment success/failure rates
- Generate deployment status reports
- Alert on deployment issues

### `update_coverage_registry.go`
**Purpose**: Test coverage registry maintenance

**What it does**:
- Updates system registry with test coverage data
- Maintains component status tracking
- Generates coverage reports and metrics

---

## 📁 **File Structure & Usage Patterns**

```
scripts/
├── README.md                           # This file
├── PUNCH Analysis Scripts
│   ├── analyze-architecture.ps1        # Architecture analysis (PowerShell)
│   ├── analyze-architecture.sh         # Architecture analysis (Bash)
│   ├── punch-quality-check.ps1         # Quality analysis (PowerShell)
│   ├── punch-quality-check.sh          # Quality analysis (Bash)
│   └── punch-deployment-analysis.sh    # Deployment analysis
├── Download Analytics
│   ├── dashboard.sh                     # Interactive dashboard
│   ├── download_tracker.sh             # Statistics collection (Bash)
│   ├── download_tracker.py             # Statistics collection (Python)
│   └── quick_stats.sh                  # Quick statistics
├── Deployment
│   ├── deploy.sh                        # Main deployment
│   ├── production-deploy.sh             # Production deployment
│   ├── provision-server.sh              # Server setup
│   └── deploy-web-terminal.sh           # Web terminal deployment
└── Utilities
    ├── verify_secrets.py                # Security validation
    ├── monitor_deployment.py            # Deployment monitoring
    ├── monitor_v1039_deployment.sh      # Version-specific monitoring
    └── update_coverage_registry.go      # Coverage registry updates
```

## 🎯 **Common Use Cases**

### **Development Workflow**
```bash
# Analyze codebase before major changes
./scripts/analyze-architecture.sh

# Check code quality before release
./scripts/punch-quality-check.sh

# Review deployment complexity
./scripts/punch-deployment-analysis.sh
```

### **Release Management**
```bash
# Check download performance
./scripts/dashboard.sh

# Verify deployment status
./scripts/monitor_deployment.py

# Update statistics
./scripts/download_tracker.sh
```

### **DevOps Operations**
```bash
# Deploy to production
./scripts/production-deploy.sh

# Set up new server
./scripts/provision-server.sh

# Validate security
python scripts/verify_secrets.py
```

## 🔍 **PUNCH Integration Details**

The PUNCH-powered scripts use the PUNCH discovery tool (symlinked as `.punch-tool/`) to provide advanced code analysis. PUNCH discovers:

- **Components**: Functions, structs, interfaces, variables, constants
- **Relationships**: Function calls, imports, dependencies
- **Patterns**: Architecture patterns, code smells, optimization opportunities
- **Metrics**: Complexity, maintainability, performance characteristics

All PUNCH results are stored in `punch_results/` (automatically gitignored).

## 📋 **Prerequisites**

- **PUNCH Scripts**: Require PUNCH tool symlinked as `.punch-tool/`
- **Python Scripts**: Require Python 3.x with requests library
- **Go Scripts**: Require Go toolchain
- **PowerShell Scripts**: Windows PowerShell 5.0+ or PowerShell Core

## 🛡️ **Security Notes**

- All scripts respect `.gitignore` patterns
- Sensitive data is handled via environment variables
- Download statistics are anonymized
- PUNCH analysis data is kept local (not uploaded anywhere)

## 🚀 **Getting Started**

1. **For architecture analysis**: Run `analyze-architecture.ps1` to understand your codebase
2. **For download tracking**: Run `dashboard.sh` to see distribution performance  
3. **For quality assessment**: Run `punch-quality-check.ps1` for technical debt analysis
4. **For deployment monitoring**: Run `monitor_deployment.py` to track releases

Each script includes help output and error handling to guide you through usage.