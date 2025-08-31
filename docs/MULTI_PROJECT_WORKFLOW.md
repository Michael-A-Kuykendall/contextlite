# Multi-Project Workflow Guide

## 🏗️ Managing Multiple Repositories with ContextLite 2.0

ContextLite 2.0 introduces **true multi-project support** with automatic isolation, independent configurations, and seamless workflow integration.

## 🚀 Getting Started

### Onboarding Multiple Projects

```bash
# Auto-discover all repositories
contextlite --onboard

# Or use interactive setup for advanced control
contextlite-onboard
```

The onboarding process will:
1. **Scan** your development directory for Git repositories
2. **Detect** existing ContextLite databases (preserved automatically)
3. **Assign** unique ports to avoid conflicts (8080, 8081, 8082...)
4. **Generate** optimized configurations for each project
5. **Setup** integration hooks for development tools

## 📁 Project Structure After Onboarding

```
~/repos/
├── project-alpha/
│   ├── .contextlite/
│   │   ├── config.yaml           # Project-specific configuration
│   │   └── metadata.json         # Discovery and integration data
│   ├── contextlite.db            # Project database (preserved if existing)
│   └── CLAUDE.md                 # Updated with ContextLite instructions
├── project-beta/
│   ├── .contextlite/
│   │   ├── config.yaml           # Different port (8081)
│   │   └── metadata.json
│   └── contextlite.db
└── project-gamma/
    ├── .contextlite/
    │   ├── config.yaml           # Different port (8082)
    │   └── metadata.json
    └── contextlite.db
```

## 🎯 Managing Individual Projects

### Start Project-Specific ContextLite

```bash
# Method 1: Navigate to project and start
cd ~/repos/project-alpha
contextlite --config .contextlite/config.yaml

# Method 2: Use CLI with project name
contextlite-cli connect project-alpha

# Method 3: Start all projects
contextlite-cli start-all
```

### Project Status and Management

```bash
# View all configured projects
contextlite-cli discover

# Check running instances  
contextlite-cli status

# Stop specific project
contextlite-cli stop project-alpha

# Stop all instances
contextlite-cli stop-all

# Restart project with new config
contextlite-cli restart project-alpha
```

## 🔧 Per-Project Configuration

Each project maintains independent configuration in `.contextlite/config.yaml`:

```yaml
# Project Alpha - Port 8080
server:
  host: "127.0.0.1"
  port: 8080
  
project:
  name: "project-alpha"
  auto_discovery: true
  
storage:
  database_path: "./contextlite.db"
  
log_ingestion:
  git: true
  claude_code: true
  vs_code: true
  interval: "on_exit"
  
mcp:
  enabled: true
  port: 9080
```

```yaml
# Project Beta - Port 8081 (no conflicts)
server:
  host: "127.0.0.1"
  port: 8081
  
project:
  name: "project-beta"
  auto_discovery: true
  
storage:
  database_path: "./contextlite.db"
  
# Different log preferences
log_ingestion:
  git: true
  claude_code: false
  vs_code: true
  copilot: true
  interval: "hourly"
  
mcp:
  enabled: true
  port: 9081
```

## 🔌 Integration with Development Tools

### VS Code Extension

The ContextLite VS Code extension automatically detects onboarded projects:

1. **Auto-Detection**: Scans workspace for `.contextlite` directories
2. **Status Bar Integration**: Shows project-specific ContextLite status
3. **One-Click Management**: Start/stop per project without terminal
4. **Context Switching**: Automatically connects to correct instance per workspace

### Claude Code Integration

Each project exposes its own MCP server:

```bash
# Project Alpha MCP server: localhost:9080
# Project Beta MCP server: localhost:9081
# Project Gamma MCP server: localhost:9082
```

Claude Code can query project-specific context:

```bash
# Query project-alpha context
curl http://localhost:9080/contextlite/registry/components

# Query project-beta context  
curl http://localhost:9081/contextlite/registry/components
```

### Git Integration

Each project maintains independent Git integration:

```yaml
# Different Git preferences per project
log_ingestion:
  git: true
  branches: ["main", "develop"]      # Project-specific branch tracking
  include_patterns: ["*.go", "*.rs"] # Language-specific filtering
  exclude_patterns: ["vendor/"]      # Project-specific excludes
```

## 🔄 Development Workflow Examples

### Scenario 1: Microservices Architecture

```bash
# Setup multiple related services
~/services/
├── user-service/          # Port 8080, MCP 9080
├── auth-service/          # Port 8081, MCP 9081  
├── payment-service/       # Port 8082, MCP 9082
└── notification-service/  # Port 8083, MCP 9083

# Start all services for development
contextlite-cli start-all

# Query cross-service context
curl http://localhost:8080/api/v1/assemble -d '{"query": "authentication flow"}'
curl http://localhost:8081/api/v1/assemble -d '{"query": "user validation"}'
```

### Scenario 2: Client/Server Projects

```bash
# Different technology stacks
~/projects/
├── mobile-app/           # React Native - Port 8080
├── web-frontend/         # Next.js - Port 8081
├── api-backend/          # Go - Port 8082
└── ml-service/           # Python - Port 8083

# Different log integration per stack
# Mobile: Git + VS Code
# Web: Git + VS Code + Copilot  
# API: Git + Claude Code
# ML: Git + VS Code + JetBrains
```

### Scenario 3: Open Source Contributions

```bash
# Multiple open source projects
~/opensource/
├── contributing-to-golang/    # Go project
├── react-component-lib/       # TypeScript
├── rust-cli-tool/            # Rust
└── python-ml-library/        # Python

# Each maintains separate context and development history
# Independent ContextLite instances prevent context bleeding
```

## 📊 Monitoring Multi-Project Setup

### Overall System Status

```bash
# Check all running instances
contextlite-cli status

# Output:
# Project          Port    Status      Uptime     Memory
# project-alpha    8080    Running     2h 30m     45MB
# project-beta     8081    Running     1h 15m     38MB
# project-gamma    8082    Stopped     -          -
```

### Per-Project Analytics

```bash
# Project-specific metrics
curl http://localhost:8080/api/v1/storage/info  # Project Alpha stats
curl http://localhost:8081/api/v1/storage/info  # Project Beta stats

# Combined analytics
contextlite-cli analytics --all-projects
```

## 🛠️ Advanced Configuration

### Resource Limits

```yaml
# Per-project resource management
resource_limits:
  max_memory_mb: 256        # Limit per project
  max_concurrent_requests: 5
  max_database_size_mb: 500
  
# Global limits across all projects  
global_limits:
  max_projects: 10
  total_memory_limit_mb: 2048
```

### Custom Port Ranges

```yaml
# Override default port assignment
port_management:
  base_port: 9000           # Start from port 9000
  mcp_base_port: 10000      # MCP servers start from 10000
  range_size: 100           # Allow 100 projects (9000-9099)
```

### Integration Preferences

```yaml
# Per-project integration settings
integrations:
  vs_code:
    enabled: true
    workspace_file: ".vscode/settings.json"
    
  claude_code:
    enabled: true
    mcp_server: true
    
  git_hooks:
    enabled: true
    on_commit: "import_recent"
    on_checkout: "refresh_context"
```

## 🔄 Migration and Maintenance

### Adding New Projects

```bash
# Add new project to existing setup
cd ~/repos/new-project
contextlite --onboard --add-to-existing

# Or re-run full discovery
contextlite --onboard --rescan
```

### Updating All Projects

```bash
# Update ContextLite binary
choco upgrade contextlite  # Windows
brew upgrade contextlite   # macOS

# Update all project configurations
contextlite-cli update-configs --all
```

### Backup and Restore

```bash
# Backup all project databases
contextlite-cli backup --output ~/contextlite-backup-$(date +%Y%m%d).tar.gz

# Restore from backup
contextlite-cli restore ~/contextlite-backup-20250831.tar.gz
```

## 🚨 Troubleshooting

### Port Conflicts

```bash
# Check port usage
contextlite-cli ports

# Reassign ports if conflicts
contextlite-cli reassign-ports --start-port 9000
```

### Database Issues

```bash
# Validate all project databases
contextlite-cli validate --all-databases

# Repair corrupted database
contextlite-cli repair project-alpha --backup-first
```

### Integration Problems

```bash
# Reset VS Code integration
contextlite-cli reset-vscode --project project-alpha

# Regenerate MCP servers
contextlite-cli setup-mcp --all-projects
```

## 🎯 Best Practices

### Project Organization
- **Keep projects isolated**: Don't share databases between unrelated projects
- **Use consistent naming**: Project names should match directory names
- **Regular maintenance**: Run `contextlite-cli health-check` weekly

### Resource Management
- **Monitor memory usage**: Large projects may need higher limits
- **Stagger startup**: Don't start all projects simultaneously on resource-constrained systems
- **Use selective startup**: Only run ContextLite for actively developed projects

### Integration Strategy
- **Enable selective logging**: Only import logs from tools you actively use
- **Configure MCP selectively**: Disable MCP for projects where Claude Code isn't used
- **Optimize configurations**: Adjust settings based on project size and usage patterns

---

**🎉 ContextLite 2.0's multi-project support enables true enterprise-grade development workflows with zero configuration overhead!**