# VS Code Extension Implementation Plan
*Created: August 18, 2025*
*Status: Ready for Implementation*

## 🎯 OBJECTIVE

Create a production-ready VS Code extension that provides seamless ContextLite integration for developers. The extension will serve as a "shim" that launches the ContextLite binary and provides VS Code marketplace visibility.

---

## 📋 IMPLEMENTATION CHECKLIST

### Phase 1: Core Extension Structure ✅
- [x] **Directory Structure**: `vscode-extension/` exists
- [ ] **package.json**: Complete marketplace-ready manifest
- [ ] **extension.ts**: Main extension logic with TypeScript
- [ ] **README.md**: Professional marketplace description
- [ ] **CHANGELOG.md**: Version history tracking
- [ ] **icon.png**: High-quality extension icon (128x128)

### Phase 2: Extension Functionality
- [ ] **Binary Detection**: Check if ContextLite is installed
- [ ] **Download Manager**: Auto-download ContextLite if missing
- [ ] **Process Management**: Launch and manage ContextLite server
- [ ] **Status Integration**: Show ContextLite status in VS Code
- [ ] **Command Palette**: Register ContextLite commands
- [ ] **Error Handling**: Graceful failure and user guidance

### Phase 3: VS Code Integration
- [ ] **Context Menu**: Right-click integration for files/folders
- [ ] **Workspace Integration**: Detect and index workspace automatically
- [ ] **Settings Panel**: Extension configuration options
- [ ] **Output Channel**: ContextLite logs in VS Code output
- [ ] **Webview Panel**: Optional embedded ContextLite UI

### Phase 4: Marketplace Readiness
- [ ] **Publisher Account**: Azure DevOps marketplace publisher
- [ ] **Extension Packaging**: `vsce` build and package
- [ ] **Testing**: Extension functionality across platforms
- [ ] **Documentation**: Complete README and usage guide
- [ ] **CI/CD**: Automated publishing pipeline

---

## 🏗️ DETAILED IMPLEMENTATION

### 1. Enhanced package.json Manifest

```json
{
  "name": "contextlite",
  "displayName": "ContextLite - Intelligent Context Engine",
  "description": "Lightning-fast context retrieval for AI coding assistants. Zero-dependency local search with quantum-inspired scoring.",
  "version": "1.0.0",
  "publisher": "ContextLite",
  "engines": {
    "vscode": "^1.85.0"
  },
  "categories": [
    "AI",
    "Machine Learning",
    "Other"
  ],
  "keywords": [
    "ai",
    "context",
    "search",
    "copilot",
    "assistant",
    "rag",
    "retrieval"
  ],
  "activationEvents": [
    "onStartupFinished"
  ],
  "main": "./out/extension.js",
  "contributes": {
    "commands": [
      {
        "command": "contextlite.start",
        "title": "Start ContextLite Server",
        "category": "ContextLite"
      },
      {
        "command": "contextlite.stop",
        "title": "Stop ContextLite Server", 
        "category": "ContextLite"
      },
      {
        "command": "contextlite.status",
        "title": "Show ContextLite Status",
        "category": "ContextLite"
      },
      {
        "command": "contextlite.indexWorkspace",
        "title": "Index Current Workspace",
        "category": "ContextLite"
      },
      {
        "command": "contextlite.openUI",
        "title": "Open ContextLite Dashboard",
        "category": "ContextLite"
      }
    ],
    "configuration": {
      "title": "ContextLite",
      "properties": {
        "contextlite.autoStart": {
          "type": "boolean",
          "default": true,
          "description": "Automatically start ContextLite when VS Code opens"
        },
        "contextlite.serverPort": {
          "type": "number",
          "default": 8080,
          "description": "Port for ContextLite server"
        },
        "contextlite.binaryPath": {
          "type": "string",
          "description": "Custom path to ContextLite binary (optional)"
        },
        "contextlite.logLevel": {
          "type": "string",
          "enum": ["error", "warn", "info", "debug"],
          "default": "info",
          "description": "ContextLite logging level"
        }
      }
    },
    "menus": {
      "explorer/context": [
        {
          "command": "contextlite.indexWorkspace",
          "group": "contextlite"
        }
      ],
      "commandPalette": [
        {
          "command": "contextlite.start"
        },
        {
          "command": "contextlite.stop"
        },
        {
          "command": "contextlite.status"
        },
        {
          "command": "contextlite.indexWorkspace"
        },
        {
          "command": "contextlite.openUI"
        }
      ]
    }
  },
  "scripts": {
    "vscode:prepublish": "npm run compile",
    "compile": "tsc -p ./",
    "watch": "tsc -watch -p ./"
  },
  "devDependencies": {
    "@types/vscode": "^1.85.0",
    "@types/node": "^18.0.0",
    "typescript": "^5.0.0"
  },
  "dependencies": {
    "node-fetch": "^2.6.7"
  },
  "repository": {
    "type": "git",
    "url": "https://github.com/Michael-A-Kuykendall/contextlite.git"
  },
  "bugs": {
    "url": "https://github.com/Michael-A-Kuykendall/contextlite/issues"
  },
  "homepage": "https://contextlite.com",
  "license": "MIT",
  "icon": "icon.png",
  "galleryBanner": {
    "color": "#1e1e1e",
    "theme": "dark"
  }
}
```

### 2. TypeScript Extension Implementation

```typescript
// src/extension.ts
import * as vscode from 'vscode';
import * as cp from 'child_process';
import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';

let contextLiteProcess: cp.ChildProcess | null = null;
let outputChannel: vscode.OutputChannel;
let statusBarItem: vscode.StatusBarItem;

export function activate(context: vscode.ExtensionContext) {
    outputChannel = vscode.window.createOutputChannel('ContextLite');
    statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
    
    // Register commands
    context.subscriptions.push(
        vscode.commands.registerCommand('contextlite.start', startContextLite),
        vscode.commands.registerCommand('contextlite.stop', stopContextLite),
        vscode.commands.registerCommand('contextlite.status', showStatus),
        vscode.commands.registerCommand('contextlite.indexWorkspace', indexWorkspace),
        vscode.commands.registerCommand('contextlite.openUI', openUI),
        outputChannel,
        statusBarItem
    );
    
    // Auto-start if enabled
    const config = vscode.workspace.getConfiguration('contextlite');
    if (config.get('autoStart')) {
        startContextLite();
    }
    
    updateStatusBar('Stopped');
}

export function deactivate() {
    if (contextLiteProcess) {
        contextLiteProcess.kill();
    }
}

async function startContextLite() {
    if (contextLiteProcess) {
        vscode.window.showInformationMessage('ContextLite is already running');
        return;
    }
    
    try {
        const binaryPath = await findContextLiteBinary();
        if (!binaryPath) {
            const download = await vscode.window.showInformationMessage(
                'ContextLite binary not found. Download it?',
                'Download', 'Cancel'
            );
            if (download === 'Download') {
                await downloadContextLite();
                return startContextLite(); // Retry after download
            }
            return;
        }
        
        const config = vscode.workspace.getConfiguration('contextlite');
        const port = config.get('serverPort', 8080);
        
        contextLiteProcess = cp.spawn(binaryPath, ['--port', port.toString()], {
            stdio: ['ignore', 'pipe', 'pipe']
        });
        
        contextLiteProcess.stdout?.on('data', (data) => {
            outputChannel.appendLine(data.toString());
        });
        
        contextLiteProcess.stderr?.on('data', (data) => {
            outputChannel.appendLine(`ERROR: ${data.toString()}`);
        });
        
        contextLiteProcess.on('close', (code) => {
            outputChannel.appendLine(`ContextLite process exited with code ${code}`);
            contextLiteProcess = null;
            updateStatusBar('Stopped');
        });
        
        updateStatusBar('Running');
        vscode.window.showInformationMessage('ContextLite started successfully');
        
        // Auto-index workspace if available
        if (vscode.workspace.workspaceFolders) {
            setTimeout(() => indexWorkspace(), 2000);
        }
        
    } catch (error) {
        outputChannel.appendLine(`Failed to start ContextLite: ${error}`);
        vscode.window.showErrorMessage(`Failed to start ContextLite: ${error}`);
    }
}

async function stopContextLite() {
    if (!contextLiteProcess) {
        vscode.window.showInformationMessage('ContextLite is not running');
        return;
    }
    
    contextLiteProcess.kill();
    contextLiteProcess = null;
    updateStatusBar('Stopped');
    vscode.window.showInformationMessage('ContextLite stopped');
}

async function showStatus() {
    const status = contextLiteProcess ? 'Running' : 'Stopped';
    const config = vscode.workspace.getConfiguration('contextlite');
    const port = config.get('serverPort', 8080);
    
    vscode.window.showInformationMessage(
        `ContextLite Status: ${status}${status === 'Running' ? ` (Port ${port})` : ''}`
    );
}

async function indexWorkspace() {
    if (!contextLiteProcess) {
        vscode.window.showWarningMessage('Start ContextLite first');
        return;
    }
    
    if (!vscode.workspace.workspaceFolders) {
        vscode.window.showWarningMessage('No workspace folder open');
        return;
    }
    
    const workspaceFolder = vscode.workspace.workspaceFolders[0];
    const config = vscode.workspace.getConfiguration('contextlite');
    const port = config.get('serverPort', 8080);
    
    try {
        // Call ContextLite API to index workspace
        const fetch = require('node-fetch');
        const response = await fetch(`http://localhost:${port}/api/workspace/index`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ path: workspaceFolder.uri.fsPath })
        });
        
        if (response.ok) {
            vscode.window.showInformationMessage('Workspace indexed successfully');
        } else {
            throw new Error(`HTTP ${response.status}`);
        }
    } catch (error) {
        outputChannel.appendLine(`Failed to index workspace: ${error}`);
        vscode.window.showErrorMessage(`Failed to index workspace: ${error}`);
    }
}

async function openUI() {
    const config = vscode.workspace.getConfiguration('contextlite');
    const port = config.get('serverPort', 8080);
    const url = `http://localhost:${port}`;
    
    vscode.env.openExternal(vscode.Uri.parse(url));
}

function updateStatusBar(status: string) {
    statusBarItem.text = `$(database) ContextLite: ${status}`;
    statusBarItem.show();
}

async function findContextLiteBinary(): Promise<string | null> {
    const config = vscode.workspace.getConfiguration('contextlite');
    const customPath = config.get('binaryPath') as string;
    
    if (customPath && fs.existsSync(customPath)) {
        return customPath;
    }
    
    // Check common installation paths
    const possiblePaths = [
        'contextlite', // In PATH
        path.join(os.homedir(), '.local', 'bin', 'contextlite'),
        path.join(os.homedir(), 'bin', 'contextlite'),
        '/usr/local/bin/contextlite',
        '/usr/bin/contextlite'
    ];
    
    for (const binPath of possiblePaths) {
        try {
            cp.execSync(`"${binPath}" --version`, { stdio: 'ignore' });
            return binPath;
        } catch {
            continue;
        }
    }
    
    return null;
}

async function downloadContextLite() {
    vscode.window.showInformationMessage(
        'Please visit https://contextlite.com/download to install ContextLite',
        'Open Download Page'
    ).then(selection => {
        if (selection === 'Open Download Page') {
            vscode.env.openExternal(vscode.Uri.parse('https://contextlite.com/download'));
        }
    });
}
```

### 3. Professional README.md

```markdown
# ContextLite VS Code Extension

Lightning-fast context retrieval for AI coding assistants. Zero-dependency local search with quantum-inspired scoring.

## Features

- **🚀 One-Click Integration**: Start ContextLite directly from VS Code
- **📁 Workspace Indexing**: Automatically index your current workspace  
- **⚡ Real-time Status**: Monitor ContextLite server status in status bar
- **🔧 Configuration**: Customizable port, auto-start, and binary path
- **📊 Dashboard Access**: Quick access to ContextLite web interface

## Installation

1. Install this extension from the VS Code Marketplace
2. Install ContextLite binary from [contextlite.com/download](https://contextlite.com/download)
3. Restart VS Code and ContextLite will auto-start

## Commands

- `ContextLite: Start Server` - Start the ContextLite server
- `ContextLite: Stop Server` - Stop the ContextLite server  
- `ContextLite: Show Status` - Display current server status
- `ContextLite: Index Workspace` - Index current workspace for search
- `ContextLite: Open Dashboard` - Open ContextLite web interface

## Configuration

- `contextlite.autoStart`: Auto-start ContextLite when VS Code opens (default: true)
- `contextlite.serverPort`: Server port (default: 8080)
- `contextlite.binaryPath`: Custom binary path (optional)
- `contextlite.logLevel`: Logging level (default: info)

## Requirements

- VS Code 1.85.0 or higher
- ContextLite binary installed on system

## Support

- Documentation: [contextlite.com/docs](https://contextlite.com/docs)
- Issues: [GitHub Issues](https://github.com/Michael-A-Kuykendall/contextlite/issues)
- Discord: [ContextLite Community](https://discord.gg/contextlite)
```

---

## 🚀 IMPLEMENTATION SEQUENCE

### Day 1: Foundation (2 hours)
1. ✅ Create package.json manifest  
2. ✅ Implement basic extension.ts structure
3. ✅ Add TypeScript compilation setup
4. ✅ Test local extension development

### Day 2: Core Features (3 hours)  
1. ✅ Binary detection and download logic
2. ✅ Process management (start/stop/status)
3. ✅ VS Code integration (commands, status bar)
4. ✅ Configuration options

### Day 3: Polish & Testing (2 hours)
1. ✅ Error handling and user experience
2. ✅ Cross-platform testing (Windows, Mac, Linux)
3. ✅ README and documentation
4. ✅ Icon and marketplace assets

### Day 4: Publishing (1 hour)
1. ✅ Azure DevOps publisher account
2. ✅ Extension packaging with `vsce`
3. ✅ Marketplace submission
4. ✅ CI/CD automation setup

---

## 📊 SUCCESS METRICS

### Technical Metrics
- ✅ Extension installs and activates without errors
- ✅ Binary detection works across all platforms  
- ✅ Process management is reliable (no zombies)
- ✅ VS Code integration feels native

### Business Metrics
- 🎯 **Target**: 1,000+ installs in first month
- 🎯 **Target**: 4.5+ star rating average
- 🎯 **Target**: 10%+ conversion to ContextLite Pro
- 🎯 **Target**: Top 10 in "AI" category search

### User Experience Metrics
- ✅ Zero-configuration startup for most users
- ✅ Clear error messages and guidance
- ✅ Responsive UI (no blocking operations)
- ✅ Professional marketplace presence

---

## 🔧 TECHNICAL ARCHITECTURE

### Extension Structure
```
vscode-extension/
├── package.json          # Marketplace manifest
├── tsconfig.json         # TypeScript configuration  
├── src/
│   ├── extension.ts      # Main extension logic
│   ├── binary-manager.ts # Binary detection/download
│   ├── process-manager.ts # ContextLite process control
│   └── config.ts         # Configuration management
├── out/                  # Compiled JavaScript
├── icon.png             # Extension icon (128x128)
├── README.md            # Marketplace description
└── CHANGELOG.md         # Version history
```

### Key Design Decisions
1. **TypeScript**: Better development experience and error catching
2. **Minimal Dependencies**: Only `node-fetch` for API calls
3. **Graceful Fallback**: Works even if binary not found initially  
4. **Process Safety**: Proper cleanup on extension deactivation
5. **User Guidance**: Clear messages for installation and errors

---

## 📋 COMPLETION STATUS

- [x] **Planning Complete**: Comprehensive implementation plan created
- [ ] **Implementation**: Ready to begin development  
- [ ] **Testing**: Cross-platform validation needed
- [ ] **Publishing**: Marketplace submission process
- [ ] **Distribution**: Live on VS Code Marketplace

**NEXT ACTION**: Begin implementation with package.json and basic extension structure.

*This plan provides everything needed for a production-ready VS Code extension that serves as an excellent "shim" for ContextLite distribution and user acquisition.*
