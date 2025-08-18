"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
exports.deactivate = deactivate;
// VS Code Extension for ContextLite
const vscode = __importStar(require("vscode"));
const cp = __importStar(require("child_process"));
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const os = __importStar(require("os"));
let contextLiteProcess = null;
let outputChannel;
let statusBarItem;
function activate(context) {
    outputChannel = vscode.window.createOutputChannel('ContextLite');
    statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
    // Register commands
    context.subscriptions.push(vscode.commands.registerCommand('contextlite.start', startContextLite), vscode.commands.registerCommand('contextlite.stop', stopContextLite), vscode.commands.registerCommand('contextlite.status', showStatus), vscode.commands.registerCommand('contextlite.indexWorkspace', indexWorkspace), vscode.commands.registerCommand('contextlite.openUI', openUI), outputChannel, statusBarItem);
    // Auto-start if enabled
    const config = vscode.workspace.getConfiguration('contextlite');
    if (config.get('autoStart')) {
        startContextLite();
    }
    updateStatusBar('Stopped');
}
function deactivate() {
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
            const download = await vscode.window.showInformationMessage('ContextLite binary not found. Download it?', 'Download', 'Cancel');
            if (download === 'Download') {
                await downloadContextLite();
                return;
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
    }
    catch (error) {
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
    vscode.window.showInformationMessage(`ContextLite Status: ${status}${status === 'Running' ? ` (Port ${port})` : ''}`);
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
        }
        else {
            throw new Error(`HTTP ${response.status}`);
        }
    }
    catch (error) {
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
function updateStatusBar(status) {
    statusBarItem.text = `$(database) ContextLite: ${status}`;
    statusBarItem.show();
}
async function findContextLiteBinary() {
    const config = vscode.workspace.getConfiguration('contextlite');
    const customPath = config.get('binaryPath');
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
        }
        catch {
            continue;
        }
    }
    return null;
}
async function downloadContextLite() {
    vscode.window.showInformationMessage('Please visit https://contextlite.com/download to install ContextLite', 'Open Download Page').then(selection => {
        if (selection === 'Open Download Page') {
            vscode.env.openExternal(vscode.Uri.parse('https://contextlite.com/download'));
        }
    });
}
//# sourceMappingURL=extension.js.map