# ContextLite v1.x → v2.0 Migration Guide

## 🎯 Quick Migration (Recommended)

For most users, migration is automatic:

```bash
# 1. Upgrade ContextLite
choco upgrade contextlite     # Windows
brew upgrade contextlite      # macOS
npm update -g contextlite     # Cross-platform

# 2. Run auto-migration
contextlite --onboard

# ✅ Done! Your v1.x data is preserved and enhanced with v2.0 features
```

## 🔍 What Changes in v2.0

### ✅ Preserved (No Action Required)
- **Existing Databases**: All your indexed content is automatically detected and preserved
- **Configuration Values**: Core settings like optimization preferences are migrated
- **API Compatibility**: v1.x API endpoints continue to work
- **Performance**: Same sub-millisecond response times maintained

### 🆕 New Features (Automatic)
- **Auto-Discovery**: Intelligent repository detection
- **Multi-Project Support**: Independent instances per repository
- **Enhanced Security**: Production-grade security controls
- **Development Integration**: Git, VS Code, Claude Code log ingestion
- **MCP Protocol**: Real-time Claude Code integration

## 📊 Before and After Comparison

### v1.x Workflow
```bash
# Manual setup for each project
cd project1
contextlite --config custom-config.yaml --port 8080

cd ../project2  
contextlite --config custom-config.yaml --port 8081  # Port conflicts!

# Manual VS Code integration
# Manual CLAUDE.md updates
# No development log integration
```

### v2.0 Workflow
```bash
# One-time setup discovers everything
contextlite --onboard

# Each project automatically configured:
# project1: Port 8080, optimized config, VS Code ready
# project2: Port 8081, optimized config, VS Code ready
# project3: Port 8082, optimized config, VS Code ready

# Automatic log integration from Git, VS Code, Claude Code
# Automatic CLAUDE.md updates with project-specific instructions
```

## 🔧 Manual Migration (Advanced Users)

If you need fine-grained control over migration:

### Step 1: Backup Existing Setup

```bash
# Backup your databases
cp */contextlite.db ~/contextlite-backup/

# Backup configurations
cp */contextlite-config.yaml ~/contextlite-backup/
```

### Step 2: Run Interactive Onboarding

```bash
contextlite-onboard

# Choose specific options:
# - Select which repositories to include
# - Choose integration preferences
# - Set custom port ranges
# - Configure log ingestion preferences
```

### Step 3: Verify Migration

```bash
# Check all projects were detected
contextlite-cli discover

# Verify databases preserved
ls -la */contextlite.db

# Test each project
contextlite-cli test-all
```

## 🛠️ Configuration Format Changes

### v1.x Configuration Format
```yaml
# Single project, basic config
server:
  port: 8080
  host: "127.0.0.1"
  
storage:
  database_path: "./contextlite.db"
  
optimization:
  timeout_ms: 250
  precision: 0.05
```

### v2.0 Configuration Format
```yaml
# Enhanced multi-project config
server:
  port: 8080                    # Auto-assigned unique port
  host: "127.0.0.1"
  
project:
  name: "project-alpha"         # NEW: Project identification
  auto_discovery: true          # NEW: Auto-discovery enabled
  
storage:
  database_path: "./contextlite.db"
  
optimization:
  timeout_ms: 250
  precision: 0.05
  
log_ingestion:                  # NEW: Development log integration
  git: true
  claude_code: true
  vs_code: true
  interval: "on_exit"
  
mcp:                           # NEW: Claude Code integration
  enabled: true
  port: 9080                   # Auto-assigned MCP port
```

## 🔌 Integration Updates Required

### VS Code Extension
- **Update to v2.0**: Extension auto-detects onboarded projects
- **No Manual Config**: Extension finds `.contextlite` directories automatically
- **Per-Project Control**: Start/stop individual projects from status bar

### API Clients
```javascript
// v1.x: Single endpoint
const client = new ContextLiteClient('http://localhost:8080');

// v2.0: Multi-project aware
const projectAlpha = new ContextLiteClient('http://localhost:8080'); // Auto-assigned
const projectBeta = new ContextLiteClient('http://localhost:8081');  // Auto-assigned

// OR use auto-discovery
const client = new ContextLiteClient();
await client.autoDiscover('project-alpha');  // Finds correct port automatically
```

### Claude Code Users
```bash
# v1.x: Manual MCP server setup
# Complex manual configuration required

# v2.0: Automatic MCP integration
# Each onboarded project exposes MCP server automatically
# Claude Code automatically discovers project context
```

## ⚡ Performance Improvements

### Database Optimization
- **Automatic VACUUM**: v2.0 runs database optimization during migration
- **Index Rebuilding**: FTS5 indexes rebuilt for enhanced performance
- **Schema Updates**: New tables for log ingestion and project metadata

### Memory Management
- **Per-Project Limits**: Memory usage isolated between projects
- **Resource Pooling**: Shared resources for common operations
- **Garbage Collection**: Enhanced cleanup for long-running instances

## 🚨 Breaking Changes

### Port Management
- **Auto-Assignment**: Ports automatically assigned instead of fixed 8080
- **Update Clients**: Hard-coded port references need updating
- **Discovery API**: Use auto-discovery instead of assuming port 8080

### File Structure
- **`.contextlite/` Directory**: New project metadata directory
- **Configuration Location**: Moved from root to `.contextlite/config.yaml`
- **Metadata Files**: New `.contextlite/metadata.json` for integration data

### CLI Interface
- **New Flags**: `--onboard` replaces manual configuration commands
- **New Binary**: `contextlite-onboard.exe` for interactive setup
- **Command Changes**: Some v1.x CLI flags deprecated in favor of config files

## 🔄 Rollback Procedure

If you need to rollback to v1.x:

### Step 1: Backup v2.0 Data
```bash
# Backup new v2.0 configurations
tar -czf v2-backup.tar.gz */.contextlite/
```

### Step 2: Restore v1.x Binary
```bash
# Downgrade to last v1.x version
choco install contextlite --version 1.1.23 --allow-downgrade
```

### Step 3: Restore v1.x Configurations
```bash
# Copy back your v1.x configs
cp ~/contextlite-backup/*.yaml ./
```

### Step 4: Manual Project Restart
```bash
# Start projects manually with v1.x approach
contextlite --config contextlite-config.yaml --port 8080
```

## 📞 Migration Support

### Common Issues

**Issue**: Port conflicts after migration
```bash
# Solution: Check and reassign ports
contextlite-cli ports
contextlite-cli reassign-ports --start-port 9000
```

**Issue**: VS Code extension not detecting projects
```bash
# Solution: Restart VS Code and check for .contextlite directories
code --list-extensions | grep contextlite
```

**Issue**: Lost database after migration
```bash
# Solution: Check backup and restore
ls -la ~/contextlite-backup/
contextlite-cli restore ~/contextlite-backup/project.db
```

### Getting Help

- **Documentation**: Complete guides in `docs/` directory
- **GitHub Issues**: Report migration problems
- **Community Discord**: Real-time help from other users
- **Email Support**: support@contextlite.com for critical issues

## 🎯 Verification Checklist

After migration, verify these work correctly:

- [ ] All projects show in `contextlite-cli discover`
- [ ] Each project starts without port conflicts
- [ ] Existing data is accessible via API
- [ ] VS Code extension detects all projects
- [ ] Claude Code MCP integration works
- [ ] Log ingestion imports development activity
- [ ] Performance matches or exceeds v1.x baseline

## 🚀 Taking Advantage of v2.0 Features

### Enable New Integrations
```bash
# Setup comprehensive log ingestion
contextlite-cli configure --project project-alpha --logs git,claude-code,vs-code,copilot

# Enable Claude Code MCP for all projects
contextlite-cli setup-mcp --all-projects
```

### Optimize Multi-Project Workflow
```bash
# Create project groups for related repositories
contextlite-cli group create "microservices" user-service auth-service payment-service

# Start/stop groups together
contextlite-cli start-group microservices
contextlite-cli stop-group microservices
```

### Advanced Features
```bash
# Cross-project context queries (enterprise feature)
curl http://localhost:8080/api/v1/cross-project/assemble \
  -d '{"query": "authentication patterns", "projects": ["user-service", "auth-service"]}'
```

---

**🎉 Welcome to ContextLite 2.0! Your development workflow just got significantly more powerful while remaining completely transparent to your existing setup.**