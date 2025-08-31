# ContextLite 2.0 Auto-Discovery Quick Start

## 🚀 Zero-Configuration Setup

ContextLite 2.0 introduces **intelligent auto-discovery** that finds all your repositories and sets up multi-project RAG systems automatically.

### ⚡ 30-Second Setup

```bash
# Install ContextLite
choco install contextlite        # Windows
brew install contextlite         # macOS  
npm install -g contextlite       # Cross-platform

# Auto-discover and configure all projects
contextlite --onboard

# That's it! ContextLite is now running on all your repositories
```

### 🎯 What Auto-Discovery Does

1. **Finds All Git Repositories** in your development directory
2. **Preserves Existing Databases** - no data loss during setup
3. **Assigns Unique Ports** automatically (8080, 8081, 8082...)
4. **Creates Configurations** for each project with optimal settings
5. **Sets Up Integration** with VS Code, Claude Code, Copilot logs
6. **Updates CLAUDE.md** files with project-specific instructions

### 🖥️ Interactive vs Quick Setup

#### Quick Setup (Recommended)
```bash
contextlite --onboard
# Choose default settings → Everything configured in 30 seconds
```

#### Interactive Setup (Advanced)
```bash
contextlite-onboard
# Choose specific projects, ports, and integrations
```

### 🔧 Per-Project Usage

After onboarding, each project has its own ContextLite instance:

```bash
cd /your/project
contextlite --config contextlite-config.yaml

# OR use the CLI
contextlite-cli connect your-project-name
```

### 🔌 VS Code Integration

The ContextLite VS Code extension automatically detects onboarded projects:

1. **Auto-Detection**: Extension finds `.contextlite` directories
2. **One-Click Start**: Status bar button to start/stop per project  
3. **Project Isolation**: Each project has independent context
4. **Zero Configuration**: Works immediately after onboarding

### 📊 Multi-Project Management

View all your ContextLite instances:

```bash
contextlite-cli discover     # List all configured projects
contextlite-cli status       # Show running instances
contextlite-cli stop-all     # Stop all instances
```

### 🔄 Log Integration

ContextLite automatically imports development logs on exit:

- **Git History**: Commit messages and change context
- **Claude Code Logs**: AI conversation history  
- **VS Code Activity**: File access patterns
- **GitHub Copilot**: Code suggestions context

### 🛠️ Advanced Configuration

Each project gets a `contextlite-config.yaml` with:

```yaml
server:
  port: 8080              # Unique port per project
storage:  
  database_path: "./contextlite.db"
project:
  auto_discovery: true    # NEW: Auto-discovery enabled
log_ingestion:
  git: true              # NEW: Automatic log import
  interval: "on_exit"
mcp:
  enabled: true          # NEW: Claude Code integration
```

### 🚨 Migration from v1.x

Existing ContextLite users:

1. **Databases Preserved**: Your existing data is automatically detected
2. **Port Updates**: May need to update clients to new ports
3. **Configuration**: New YAML format with enhanced features
4. **VS Code**: Update extension to v2.0 for auto-discovery

### 📚 Next Steps

- **[Multi-Project Workflow Guide](MULTI_PROJECT_WORKFLOW.md)**
- **[Claude Code Integration](../internal/mcp/README.md)**
- **[Enterprise Clustering](CLUSTERING_GUIDE.md)**
- **[API Reference](API_REFERENCE.md)**

---

**🎉 ContextLite 2.0: From manual setup to intelligent auto-discovery in one major release!**