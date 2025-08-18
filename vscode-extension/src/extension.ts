// VS Code Extension for ContextLite
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