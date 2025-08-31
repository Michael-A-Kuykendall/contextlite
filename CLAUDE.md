## 🦀 **RUSTCHAIN MISSION SYSTEM - COMPLETE PRIMER**

### **Core Concepts**
- **Rustchain**: AI agent framework for mission execution with DAG-based task orchestration
- **Mission**: YAML file defining a series of steps to be executed by the Champion AI
- **Steps**: Individual tasks with specific types (command, llm, create_file, tool, http)
- **Dependencies**: Steps can depend on other steps using `depends_on` field

### **Mission File Structure (MANDATORY FORMAT)**

```yaml
version: "1.0"                    # Required version field
name: "mission_name"              # Required top-level name
description: "Mission description" # Required description

steps:                           # Required steps array
  - id: "step_id"               # Required unique step ID
    name: "Step Name"           # Required step name
    step_type: "command"        # Required: command|llm|create_file|tool|http
    parameters:                 # Required parameters object
      command: "echo"           # Command-specific parameters
      args: ["Hello World"]
    timeout_seconds: 30         # Optional timeout
    depends_on: ["other_step"]  # Optional dependencies

config:                         # Optional configuration
  max_parallel_steps: 1         # Parallel execution limit
  timeout_seconds: 120          # Mission timeout
```

### **Step Types and Parameters**

#### **1. Command Steps** (`step_type: "command"`)
```yaml
- id: "run_command"
  name: "Execute Shell Command"
  step_type: "command"
  parameters:
    command: "echo"             # Command to run
    args: ["Hello", "World"]    # Arguments array
  timeout_seconds: 30
```

#### **2. LLM Steps** (`step_type: "llm"`)
```yaml
- id: "ask_ai"
  name: "Query AI Model"
  step_type: "llm"
  parameters:
    prompt: "Analyze this code"  # AI prompt
    model: "llama32-champion:latest"  # Model name
    provider: "ollama"          # Provider (ollama, openai)
    temperature: 0.3            # Creativity (0-1)
    max_tokens: 500             # Response length limit
```

#### **3. File Creation Steps** (`step_type: "create_file"`)
```yaml
- id: "create_report"
  name: "Create Report File"
  step_type: "create_file"
  parameters:
    path: "output/report.md"    # File path
    content: "Report content"   # File content
```

### **Mission Execution Commands**
```bash
# Validate mission format
./rustchain.exe mission validate mission.yaml

# Dry-run (simulation mode)  
./rustchain.exe run --dry-run mission.yaml

# Execute mission
./rustchain.exe run mission.yaml
```

### **Champion AI Integration**
- **Model**: `llama32-champion:latest` (custom-trained on Rust/Go projects)
- **Provider**: `ollama` (local inference)
- **Context**: Champion AI has specialized knowledge of ContextLite architecture

### **Mission Execution Protocol**
1. **Validate**: `./rustchain.exe mission validate mission.yaml`
2. **Dry-run**: `./rustchain.exe run --dry-run mission.yaml`
3. **Execute**: `./rustchain.exe run mission.yaml`
4. **Archive**: Move to `docs/mission-stacks/done/` when complete

## 🎯 **MISSION ARCHITECTURE DECISION** (Aug 28, 2025)
**Future Intention**: Shimmy as primary interface with Rustchain for automated mission execution
- **Integration**: Mission YAML → Rustchain → Shimmy → Champion AI (`llama32-champion:latest`)
- **Workflow**: `docs/mission-stacks/current/` → execution → `docs/mission-stacks/done/`
- **Timeline**: 20-30 minutes for complete critical task processing via Champion AI
- **Champion Model**: Custom-trained on Rust/Go projects, project-aware responses

## Working GitHub API Commands

### ✅ CONFIRMED WORKING - Deploy to Chocolatey
```bash
# Trigger selective Chocolatey deployment (TESTED & WORKING)
cd "C:\Users\micha\repos\contextlite"
curl -X POST -H "Authorization: Bearer $GITHUB_TOKEN" -H "Accept: application/vnd.github.v3+json" \
  "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/workflows/deploy-selective.yml/dispatches" \
  -d '{"ref":"main","inputs":{"platforms":"chocolatey","version":"1.1.3","force_deploy":"true"}}'
```

### ✅ CONFIRMED WORKING - GitHub Release API Access
```bash
# Check GitHub releases (TESTED & WORKING)
cd "C:\Users\micha\repos\contextlite" 
curl -H "Authorization: Bearer $GITHUB_TOKEN" "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases/tags/v1.1.1"
```

## Project Structure Notes

- Main repo: `C:\Users\micha\repos\contextlite`
- Chocolatey packages: Fixed with placeholder approach for URL/checksum replacement
- VS Code extension: Manual marketplace uploads with .vsix files
- Hugging Face: Auto-deploys via git push to contextlite-download folder
- GitHub token: Available as `$GITHUB_TOKEN` environment variable

## Critical Fixes Applied

### Chocolatey Deployment Issue (RESOLVED)
- **Root Cause**: Install script used env variables, workflow expected placeholders
- **Fix**: Updated chocolatey/tools/chocolateyinstall.ps1 to use RELEASE_URL_PLACEHOLDER and RELEASE_CHECKSUM_PLACEHOLDER
- **Result**: Workflow now properly replaces URLs and checksums

### Selective Deployment Workflow (RESOLVED)  
- **Root Cause**: Windows ZIP had wrong structure (nested directories instead of flat)
- **Fix**: Updated .github/workflows/deploy-selective.yml to create flat ZIP with contextlite.exe at root
- **Result**: Chocolatey verification should pass

## Deployment Status
- **Chocolatey**: 🎉 SUCCESS v1.1.4 - DEPLOYED! After weeks of debugging, finally working!
- **VS Code**: Manual upload process, currently at v1.1.2 
- **Hugging Face**: Working with analytics tracking
- **Homebrew**: Needs workflow conflict resolution
- **NPM/Docker**: Status to be verified

## Recent Fixes Applied (Latest)

### 🎉 FINAL BREAKTHROUGH - CHOCOLATEY DEPLOYMENT SUCCESS (Aug 26, 2025)
- **Result**: ContextLite v1.1.4 successfully deployed to Chocolatey!
- **Timeline**: Resolved 2+ week deployment blockage 
- **Status**: GitHub Actions workflow now fully automated and working
- **Next**: Monitor Chocolatey approval process for v1.1.4

### 📝 Placeholder Mismatch Fix (FINAL PIECE - Aug 26, 2025)  
- **Root Cause**: nuspec file used `$version$` but workflow expected `VERSION_PLACEHOLDER`
- **Error**: `choco pack` command failing during package creation
- **Fix**: Updated contextlite.nuspec to use `VERSION_PLACEHOLDER` consistently
- **Result**: Chocolatey package creation now succeeds

### 🚨 CRITICAL BINARY PRESERVATION FIX (BREAKTHROUGH - Aug 26, 2025)
- **Root Cause**: Workflow was DELETING binaries immediately after building them!
- **Error**: `cp: cannot stat 'contextlite-linux-amd64': No such file or directory`
- **Fix**: Removed incorrect `rm -f contextlite-linux-amd64 contextlite-darwin-amd64 contextlite-darwin-arm64` cleanup step
- **Impact**: This was the PRIMARY cause blocking Chocolatey deployment for weeks
- **Result**: All platform binaries now preserved for proper archive creation

### Archive Creation Fix (RESOLVED - Aug 26, 2025)
- **Root Cause**: `rm -rf` command failing on non-existent files in workflow
- **Fix**: Added proper error handling with `2>/dev/null || true`  
- **Result**: Archive creation step now passes, enables Chocolatey deployment to proceed

# ContextLite Configuration

## Project Setup
- **Project**: contextlite
- **Port**: 8084
- **Database**: C:\Users\micha\repos\contextlite\contextlite.db
- **Config**: C:\Users\micha\repos\contextlite\contextlite-config.yaml

## Quick Commands
```bash
# Start ContextLite for this project
contextlite --config C:\Users\micha\repos\contextlite\contextlite-config.yaml --port 8084

# Connect via CLI
contextlite-cli connect contextlite

# Query this project's context
contextlite-cli query contextlite "your search terms"
```

## Integration Status
- Port assignment: ✅ Standardized
- Database: ✅ Preserved existing data
- Configuration: ✅ Automated
- Discovery: ✅ Enabled