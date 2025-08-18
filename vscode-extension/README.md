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

## What is ContextLite?

ContextLite is an intelligent context engine that helps AI coding assistants understand your codebase. Instead of sending random files, ContextLite uses quantum-inspired scoring to find exactly the right context for your queries.

### Key Benefits

- **Zero Dependencies**: Pure Go binary, no Python or Node.js required
- **Lightning Fast**: Sub-millisecond search across large codebases
- **Private**: All processing happens locally on your machine
- **Smart Scoring**: Quantum-inspired algorithms find relevant context
- **Universal**: Works with any AI assistant (GitHub Copilot, Claude, ChatGPT)

## Support

- Documentation: [contextlite.com/docs](https://contextlite.com/docs)
- Issues: [GitHub Issues](https://github.com/Michael-A-Kuykendall/contextlite/issues)
- Discord: [ContextLite Community](https://discord.gg/contextlite)

## License

MIT