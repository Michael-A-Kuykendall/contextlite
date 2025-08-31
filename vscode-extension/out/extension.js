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
    context.subscriptions.push(vscode.commands.registerCommand('contextlite.start', startContextLite), vscode.commands.registerCommand('contextlite.stop', stopContextLite), vscode.commands.registerCommand('contextlite.status', showStatus), vscode.commands.registerCommand('contextlite.indexWorkspace', indexWorkspace), vscode.commands.registerCommand('contextlite.openUI', openUI), vscode.commands.registerCommand('contextlite.enableForProject', enableForProject), vscode.commands.registerCommand('contextlite.ingestChatHistory', ingestChatHistory), outputChannel, statusBarItem);
    // Check if project already has ContextLite configured
    const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
    if (workspaceFolder) {
        const contextLiteDir = path.join(workspaceFolder.uri.fsPath, '.contextlite');
        if (fs.existsSync(contextLiteDir)) {
            // Project already configured - auto-start if enabled
            const config = vscode.workspace.getConfiguration('contextlite');
            if (config.get('autoStart', true)) {
                setTimeout(() => startContextLite(), 1000); // Small delay for workspace to settle
            }
            updateStatusBar('Configured');
        }
        else {
            // Project not configured - show as available
            updateStatusBar('Available');
        }
    }
    else {
        updateStatusBar('No Workspace');
    }
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
        // 🎯 INTELLIGENT PORT MANAGEMENT - Get or assign project-specific port
        const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
        if (!workspaceFolder) {
            vscode.window.showErrorMessage('No workspace folder open');
            return;
        }
        const projectPath = workspaceFolder.uri.fsPath;
        const projectInstance = await getOrAssignProjectPort(projectPath);
        // Start with project-specific configuration
        const args = ['--config', projectInstance.configPath];
        contextLiteProcess = cp.spawn(binaryPath, args, {
            stdio: ['ignore', 'pipe', 'pipe'],
            cwd: projectPath
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
        updateStatusBar(`Running (Port ${projectInstance.port})`);
        vscode.window.showInformationMessage(`ContextLite started for ${projectInstance.projectName} on port ${projectInstance.port}`);
        // Auto-index workspace if available
        setTimeout(() => indexWorkspace(), 2000);
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
async function getOrAssignProjectPort(projectPath) {
    const homeDir = os.homedir();
    const registryPath = path.join(homeDir, '.contextlite', 'port_registry.json');
    // Load existing registry
    let registry = {};
    try {
        if (fs.existsSync(registryPath)) {
            const data = fs.readFileSync(registryPath, 'utf8');
            registry = JSON.parse(data);
        }
    }
    catch (error) {
        outputChannel.appendLine(`Failed to load port registry: ${error}`);
    }
    const normalizedPath = path.resolve(projectPath).toLowerCase();
    const projectName = path.basename(projectPath);
    // Check if project already has a port
    const existing = registry[normalizedPath];
    if (existing && await isPortHealthy(existing.port)) {
        outputChannel.appendLine(`Using existing ContextLite instance on port ${existing.port}`);
        return existing;
    }
    // Assign new port
    const port = await findAvailablePort();
    const configDir = path.join(projectPath, '.contextlite');
    const instance = {
        projectName,
        projectPath: normalizedPath,
        port,
        configPath: path.join(configDir, 'config.yaml'),
        dbPath: path.join(configDir, 'contextlite.db')
    };
    // Create project config
    await createProjectConfig(instance);
    // Save to registry
    registry[normalizedPath] = instance;
    try {
        const dir = path.dirname(registryPath);
        if (!fs.existsSync(dir)) {
            fs.mkdirSync(dir, { recursive: true });
        }
        fs.writeFileSync(registryPath, JSON.stringify(registry, null, 2));
        outputChannel.appendLine(`Assigned port ${port} to project ${projectName}`);
    }
    catch (error) {
        outputChannel.appendLine(`Failed to save port registry: ${error}`);
    }
    return instance;
}
async function findAvailablePort() {
    const portRange = [8080, 8081, 8082, 8083, 8084, 8085, 8086, 8087, 8088, 8089, 8090];
    for (const port of portRange) {
        if (await isPortAvailable(port)) {
            return port;
        }
    }
    throw new Error('No available ports in range 8080-8090');
}
async function isPortAvailable(port) {
    return new Promise((resolve) => {
        const server = require('net').createServer();
        server.listen(port, () => {
            server.close(() => resolve(true));
        });
        server.on('error', () => resolve(false));
    });
}
async function isPortHealthy(port) {
    try {
        const fetch = require('node-fetch');
        const response = await fetch(`http://localhost:${port}/health`, {
            timeout: 2000
        });
        return response.ok;
    }
    catch {
        return false;
    }
}
async function createProjectConfig(instance) {
    const configDir = path.dirname(instance.configPath);
    if (!fs.existsSync(configDir)) {
        fs.mkdirSync(configDir, { recursive: true });
    }
    const config = `# Auto-generated ContextLite configuration for ${instance.projectName}
# Port: ${instance.port}

server:
  port: ${instance.port}
  host: "127.0.0.1"
  cors_enabled: true

storage:
  database_path: "${instance.dbPath.replace(/\\/g, '/')}"
  cache_size_mb: 256

cluster:
  enabled: true
  node_id: "contextlite-${instance.projectName}-${instance.port}"
  
  affinity:
    workspace_routing: true
    sticky_sessions: true
    rules:
      "${instance.projectName}":
        resource_tier: "high"
        max_memory_mb: 512
        priority: 8

# Performance optimization for VS Code
performance:
  cache_embeddings: true
  enable_smart_indexing: true
  update_frequency: "on_save"

# SMT solver settings
smt:
  solver_timeout_ms: 1000
  max_candidates: 100
  objective_style: "code_context"

# Privacy settings
privacy:
  project_isolation: true
  exclude_patterns:
    - "*.env*"
    - "*.key" 
    - "*.pem"
    - "secrets/*"
    - "node_modules/*"
    - ".git/*"

logging:
  level: "info"
  file: "${path.join(configDir, 'contextlite.log').replace(/\\/g, '/')}"
`;
    fs.writeFileSync(instance.configPath, config);
}
// Enable ContextLite for current project
async function enableForProject() {
    const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
    if (!workspaceFolder) {
        vscode.window.showErrorMessage('No workspace folder open');
        return;
    }
    const projectPath = workspaceFolder.uri.fsPath;
    const projectName = path.basename(projectPath);
    try {
        // Create project instance
        const projectInstance = await getOrAssignProjectPort(projectPath);
        vscode.window.showInformationMessage(`ContextLite enabled for ${projectName} on port ${projectInstance.port}`, 'Start Now', 'Configure').then(selection => {
            if (selection === 'Start Now') {
                startContextLite();
            }
            else if (selection === 'Configure') {
                vscode.workspace.openTextDocument(projectInstance.configPath);
            }
        });
        updateStatusBar('Configured');
    }
    catch (error) {
        vscode.window.showErrorMessage(`Failed to enable ContextLite: ${error}`);
    }
}
// Ingest chat history into ContextLite database
async function ingestChatHistory() {
    const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
    if (!workspaceFolder) {
        vscode.window.showErrorMessage('No workspace folder open');
        return;
    }
    const projectPath = workspaceFolder.uri.fsPath;
    const contextLiteDir = path.join(projectPath, '.contextlite');
    if (!fs.existsSync(contextLiteDir)) {
        const enable = await vscode.window.showInformationMessage('ContextLite not enabled for this project. Enable it first?', 'Enable', 'Cancel');
        if (enable === 'Enable') {
            await enableForProject();
        }
        return;
    }
    // Find chat history files
    const homeDir = os.homedir();
    const possibleChatDirs = [
        path.join(homeDir, '.anthropic', 'chats'),
        path.join(homeDir, 'AppData', 'Roaming', 'Claude', 'chats'),
        path.join(homeDir, '.claude', 'chats'),
        path.join(homeDir, 'Documents', 'Claude'),
        path.join(projectPath, 'claude-chats'),
        path.join(projectPath, 'chats'),
    ];
    vscode.window.showInformationMessage('Searching for chat history files...', { modal: false });
    const chatFiles = [];
    const projectName = path.basename(projectPath);
    for (const chatDir of possibleChatDirs) {
        if (fs.existsSync(chatDir)) {
            try {
                const files = fs.readdirSync(chatDir, { recursive: true });
                for (const file of files) {
                    const filePath = path.join(chatDir, file.toString());
                    if (file.toString().endsWith('.json') && fs.statSync(filePath).isFile()) {
                        // Check if file mentions this project
                        try {
                            const content = fs.readFileSync(filePath, 'utf8');
                            if (content.includes(projectName) || content.includes('contextlite')) {
                                chatFiles.push(filePath);
                            }
                        }
                        catch (e) {
                            // Skip files we can't read
                        }
                    }
                }
            }
            catch (e) {
                // Skip directories we can't read
            }
        }
    }
    if (chatFiles.length === 0) {
        vscode.window.showWarningMessage('No chat history files found for this project');
        return;
    }
    // Show found files and ask for confirmation
    const selection = await vscode.window.showInformationMessage(`Found ${chatFiles.length} chat files. Ingest them into ContextLite?`, 'Ingest All', 'Show Files', 'Cancel');
    if (selection === 'Show Files') {
        outputChannel.appendLine(`Found chat files for ${projectName}:`);
        chatFiles.forEach(file => outputChannel.appendLine(`  • ${file}`));
        outputChannel.show();
        return;
    }
    if (selection !== 'Ingest All') {
        return;
    }
    // Start ingestion process
    outputChannel.appendLine(`Starting ingestion of ${chatFiles.length} chat files...`);
    outputChannel.show();
    // Get ContextLite instance info
    const instance = await getOrAssignProjectPort(projectPath);
    // Check if ContextLite is running
    if (!await isPortHealthy(instance.port)) {
        const start = await vscode.window.showInformationMessage('ContextLite is not running. Start it for ingestion?', 'Start', 'Cancel');
        if (start === 'Start') {
            await startContextLite();
            // Wait for startup
            await new Promise(resolve => setTimeout(resolve, 3000));
        }
        else {
            return;
        }
    }
    // Ingest each chat file
    let ingested = 0;
    let failed = 0;
    for (const chatFile of chatFiles) {
        try {
            const content = fs.readFileSync(chatFile, 'utf8');
            const chatData = JSON.parse(content);
            // Convert chat to documents for ContextLite
            const documents = extractDocumentsFromChat(chatData, chatFile);
            // Add to ContextLite via API
            for (const doc of documents) {
                try {
                    const fetch = require('node-fetch');
                    const response = await fetch(`http://localhost:${instance.port}/api/v1/documents`, {
                        method: 'POST',
                        headers: {
                            'Content-Type': 'application/json',
                            'X-Workspace-ID': instance.projectName
                        },
                        body: JSON.stringify(doc),
                        timeout: 10000
                    });
                    if (response.ok) {
                        outputChannel.appendLine(`✅ Ingested: ${doc.path}`);
                    }
                    else {
                        outputChannel.appendLine(`❌ Failed to ingest: ${doc.path} (${response.status})`);
                        failed++;
                    }
                }
                catch (e) {
                    outputChannel.appendLine(`❌ Error ingesting: ${doc.path} - ${e}`);
                    failed++;
                }
            }
            ingested++;
        }
        catch (e) {
            outputChannel.appendLine(`❌ Failed to process: ${chatFile} - ${e}`);
            failed++;
        }
    }
    const message = `Ingestion complete: ${ingested} files processed, ${failed} failed`;
    outputChannel.appendLine(message);
    vscode.window.showInformationMessage(message);
}
// Extract documents from chat JSON for ContextLite storage
function extractDocumentsFromChat(chatData, chatFile) {
    const documents = [];
    const baseName = path.basename(chatFile, '.json');
    try {
        // Handle different chat file formats
        const messages = chatData.messages || chatData.conversation || [chatData];
        for (let i = 0; i < messages.length; i++) {
            const message = messages[i];
            const role = message.role || message.author || 'unknown';
            const content = message.content || message.text || message.message || '';
            if (content && content.length > 50) { // Only include substantial messages
                documents.push({
                    path: `chat/${baseName}/message_${i}_${role}`,
                    content: content,
                    language: 'markdown',
                    metadata: {
                        type: 'chat_message',
                        role: role,
                        timestamp: message.timestamp || message.created_at || new Date().toISOString(),
                        chat_file: chatFile,
                        message_index: i
                    }
                });
            }
        }
        // Add summary document
        documents.push({
            path: `chat/${baseName}/summary`,
            content: `Chat session: ${baseName}\nTotal messages: ${messages.length}\nFrom file: ${chatFile}`,
            language: 'markdown',
            metadata: {
                type: 'chat_summary',
                total_messages: messages.length,
                chat_file: chatFile
            }
        });
    }
    catch (e) {
        // Fallback: treat entire file as one document
        documents.push({
            path: `chat/${baseName}/full_content`,
            content: JSON.stringify(chatData, null, 2),
            language: 'json',
            metadata: {
                type: 'chat_raw',
                chat_file: chatFile
            }
        });
    }
    return documents;
}
//# sourceMappingURL=extension.js.map