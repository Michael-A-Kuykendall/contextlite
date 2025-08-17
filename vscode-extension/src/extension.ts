import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { spawn, ChildProcess } from 'child_process';
import axios from 'axios';

let contextliteProcess: ChildProcess | null = null;
let outputChannel: vscode.OutputChannel;

export function activate(context: vscode.ExtensionContext) {
    outputChannel = vscode.window.createOutputChannel('ContextLite');
    
    // Check license status on activation
    checkLicenseStatus(context);
    
    // Register commands
    const addToContext = vscode.commands.registerCommand('contextlite.addToContext', () => {
        if (!checkLicenseAndWarn(context)) return;
        addSelectionToContext();
    });
    
    const assembleContext = vscode.commands.registerCommand('contextlite.assembleContext', () => {
        if (!checkLicenseAndWarn(context)) return;
        assembleContextFromQuery();
    });
    
    const clearContext = vscode.commands.registerCommand('contextlite.clearContext', () => {
        if (!checkLicenseAndWarn(context)) return;
        clearContextDatabase();
    });
    
    const showLicense = vscode.commands.registerCommand('contextlite.showLicense', () => {
        showLicenseInfo(context);
    });
    
    context.subscriptions.push(addToContext, assembleContext, clearContext, showLicense);
    
    // Start ContextLite server
    startContextLiteServer(context);
}

export function deactivate() {
    if (contextliteProcess) {
        contextliteProcess.kill();
    }
}

function checkLicenseStatus(context: vscode.ExtensionContext) {
    const installDate = context.globalState.get('installDate', Date.now());
    if (!context.globalState.get('installDate')) {
        context.globalState.update('installDate', Date.now());
    }
    
    const trialDays = 14;
    const isTrialExpired = (Date.now() - installDate) > (trialDays * 24 * 60 * 60 * 1000);
    const hasValidLicense = hasLicense();
    
    if (isTrialExpired && !hasValidLicense) {
        const daysExpired = Math.floor((Date.now() - installDate - (trialDays * 24 * 60 * 60 * 1000)) / (24 * 60 * 60 * 1000));
        vscode.window.showWarningMessage(
            `ContextLite trial expired ${daysExpired} days ago. Get your commercial license to continue using ContextLite.`,
            'Buy License ($99)',
            'Enter License Key',
            'Remind Later'
        ).then(handleLicensePromptResponse);
    } else if (!isTrialExpired && !hasValidLicense) {
        const daysLeft = Math.ceil((trialDays * 24 * 60 * 60 * 1000 - (Date.now() - installDate)) / (24 * 60 * 60 * 1000));
        outputChannel.appendLine(`ContextLite trial: ${daysLeft} days remaining`);
    }
}

function checkLicenseAndWarn(context: vscode.ExtensionContext): boolean {
    const installDate = context.globalState.get('installDate', Date.now());
    const trialDays = 14;
    const isTrialExpired = (Date.now() - installDate) > (trialDays * 24 * 60 * 60 * 1000);
    
    if (isTrialExpired && !hasLicense()) {
        vscode.window.showWarningMessage(
            'ContextLite trial has expired. Purchase a commercial license to continue.',
            'Buy License ($99)',
            'Enter License Key'
        ).then(handleLicensePromptResponse);
        return false;
    }
    
    return true;
}

function hasLicense(): boolean {
    const license = vscode.workspace.getConfiguration('contextlite').get('licenseKey', '');
    // Simple validation: must start with CL-2024- and be reasonable length
    return typeof license === 'string' && 
           license.startsWith('CL-2024-') && 
           license.length >= 15;
}

function handleLicensePromptResponse(selection: string | undefined) {
    if (selection === 'Buy License ($99)') {
        vscode.env.openExternal(vscode.Uri.parse('https://buy.stripe.com/bJe3cneNfcBp2Z57u67N600'));
    } else if (selection === 'Enter License Key') {
        vscode.window.showInputBox({ 
            prompt: 'Enter your ContextLite license key',
            placeHolder: 'CL-2024-XXXXXXXXXXXXX',
            validateInput: (value: string) => {
                if (!value) return 'License key is required';
                if (!value.startsWith('CL-2024-')) return 'Invalid license key format';
                if (value.length < 15) return 'License key too short';
                return null;
            }
        }).then((key: string | undefined) => {
            if (key) {
                vscode.workspace.getConfiguration('contextlite').update('licenseKey', key, vscode.ConfigurationTarget.Global);
                vscode.window.showInformationMessage('License key saved! ContextLite is now activated.');
            }
        });
    }
}

function showLicenseInfo(context: vscode.ExtensionContext) {
    const installDate = context.globalState.get('installDate', Date.now());
    const trialDays = 14;
    const daysUsed = Math.floor((Date.now() - installDate) / (24 * 60 * 60 * 1000));
    const daysLeft = Math.max(0, trialDays - daysUsed);
    const hasValidLicense = hasLicense();
    
    let message: string;
    let actions: string[] = [];
    
    if (hasValidLicense) {
        message = 'ContextLite Commercial License Active ✅\\n\\nYou have full access to all ContextLite features.';
        actions = ['View Settings'];
    } else if (daysLeft > 0) {
        message = `ContextLite Trial: ${daysLeft} days remaining\\n\\nEnjoy full features during your trial period.`;
        actions = ['Buy License ($99)', 'Enter License Key'];
    } else {
        message = `ContextLite Trial Expired\\n\\nTrial ended ${-daysLeft} days ago. Purchase a commercial license to continue.`;
        actions = ['Buy License ($99)', 'Enter License Key'];
    }
    
    vscode.window.showInformationMessage(message, ...actions).then((selection: string | undefined) => {
        if (selection === 'Buy License ($99)') {
            vscode.env.openExternal(vscode.Uri.parse('https://buy.stripe.com/bJe3cneNfcBp2Z57u67N600'));
        } else if (selection === 'Enter License Key') {
            handleLicensePromptResponse('Enter License Key');
        } else if (selection === 'View Settings') {
            vscode.commands.executeCommand('workbench.action.openSettings', 'contextlite');
        }
    });
}

function startContextLiteServer(context: vscode.ExtensionContext) {
    const config = vscode.workspace.getConfiguration('contextlite');
    const port = config.get('serverPort', 8081);
    
    // Look for contextlite binary in extension directory
    const extensionPath = context.extensionPath;
    const binaryPath = getBinaryPath(extensionPath);
    
    if (!fs.existsSync(binaryPath)) {
        vscode.window.showErrorMessage(`ContextLite binary not found at ${binaryPath}. Please reinstall the extension.`);
        return;
    }
    
    outputChannel.appendLine('Starting ContextLite server...');
    
    contextliteProcess = spawn(binaryPath, [], {
        env: { ...process.env, PORT: port.toString() },
        cwd: extensionPath
    });
    
    contextliteProcess.stdout?.on('data', (data: any) => {
        outputChannel.appendLine(`Server: ${data.toString()}`);
    });
    
    contextliteProcess.stderr?.on('data', (data: any) => {
        outputChannel.appendLine(`Server Error: ${data.toString()}`);
    });
    
    contextliteProcess.on('close', (code: any) => {
        outputChannel.appendLine(`ContextLite server exited with code ${code}`);
        contextliteProcess = null;
    });
    
    // Wait a moment for server to start
    setTimeout(() => {
        outputChannel.appendLine(`ContextLite server started on port ${port}`);
        vscode.window.showInformationMessage('ContextLite is ready!');
    }, 2000);
}

function getBinaryPath(extensionPath: string): string {
    const platform = process.platform;
    if (platform === 'win32') {
        return path.join(extensionPath, 'bin', 'contextlite.exe');
    } else if (platform === 'darwin') {
        return path.join(extensionPath, 'bin', 'contextlite-mac');
    } else {
        return path.join(extensionPath, 'bin', 'contextlite-linux');
    }
}

async function addSelectionToContext() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No active editor');
        return;
    }
    
    const selection = editor.selection;
    const selectedText = editor.document.getText(selection);
    
    if (!selectedText.trim()) {
        vscode.window.showWarningMessage('No text selected');
        return;
    }
    
    try {
        const config = vscode.workspace.getConfiguration('contextlite');
        const port = config.get('serverPort', 8081);
        const currentFilePath = editor.document.uri.fsPath;
        const language = editor.document.languageId;
        
        await axios.post(`http://127.0.0.1:${port}/api/v1/documents`, {
            content: selectedText,
            path: currentFilePath,
            language: language
        }, {
            headers: {
                'Authorization': 'Bearer contextlite-dev-token-2025',
                'Content-Type': 'application/json'
            }
        });
        
        vscode.window.showInformationMessage(`Added ${selectedText.length} characters to context`);
        outputChannel.appendLine(`Added to context: ${currentFilePath} (${selectedText.length} chars)`);
        
    } catch (error) {
        vscode.window.showErrorMessage(`Failed to add to context: ${error}`);
        outputChannel.appendLine(`Error: ${error}`);
    }
}

async function assembleContextFromQuery() {
    const query = await vscode.window.showInputBox({
        prompt: 'Enter your context query',
        placeHolder: 'e.g., "authentication security patterns"'
    });
    
    if (!query) return;
    
    try {
        const config = vscode.workspace.getConfiguration('contextlite');
        const port = config.get('serverPort', 8081);
        const maxTokens = config.get('maxTokens', 4000);
        const maxDocuments = config.get('maxDocuments', 10);
        const useSMT = config.get('useSMT', true);
        
        const response = await axios.post(`http://127.0.0.1:${port}/api/v1/context/assemble`, {
            query: query,
            max_tokens: maxTokens,
            max_documents: maxDocuments,
            use_cache: false,
            use_smt: useSMT
        }, {
            headers: {
                'Authorization': 'Bearer contextlite-dev-token-2025',
                'Content-Type': 'application/json'
            }
        });
        
        const result = response.data;
        
        // Create new document with assembled context
        const contextDoc = await vscode.workspace.openTextDocument({
            content: formatAssembledContext(result),
            language: 'markdown'
        });
        
        await vscode.window.showTextDocument(contextDoc);
        
        vscode.window.showInformationMessage(
            `Assembled ${result.total_documents} documents (${result.total_tokens} tokens) in ${result.timings.total_ms.toFixed(1)}ms`
        );
        
    } catch (error) {
        vscode.window.showErrorMessage(`Failed to assemble context: ${error}`);
        outputChannel.appendLine(`Error: ${error}`);
    }
}

function formatAssembledContext(result: any): string {
    let content = `# ContextLite Assembly Result\\n\\n`;
    content += `**Query:** ${result.query}\\n`;
    content += `**Documents:** ${result.total_documents}\\n`;
    content += `**Tokens:** ${result.total_tokens}\\n`;
    content += `**Coherence Score:** ${result.coherence_score.toFixed(3)}\\n`;
    content += `**SMT Solver:** ${result.smt_metrics.solver_used}\\n`;
    content += `**Total Time:** ${result.timings.total_ms.toFixed(1)}ms\\n\\n`;
    
    content += `## Timing Breakdown\\n`;
    content += `- FTS Harvest: ${result.timings.fts_harvest_ms.toFixed(3)}ms\\n`;
    content += `- Feature Build: ${result.timings.feature_build_ms.toFixed(3)}ms\\n`;
    content += `- SMT Solver: ${result.timings.smt_solver_ms.toFixed(3)}ms\\n`;
    content += `- SMT Wall: ${result.timings.smt_wall_ms.toFixed(3)}ms\\n\\n`;
    
    result.documents.forEach((doc: any, index: number) => {
        content += `## Document ${index + 1}: ${doc.path}\\n`;
        content += `**Utility Score:** ${doc.utility_score.toFixed(4)}\\n`;
        content += `**Language:** ${doc.language}\\n\\n`;
        content += `\`\`\`${doc.language}\\n${doc.content}\\n\`\`\`\\n\\n`;
    });
    
    return content;
}

async function clearContextDatabase() {
    const confirm = await vscode.window.showWarningMessage(
        'This will clear all documents from the ContextLite database. Continue?',
        'Yes, Clear All',
        'Cancel'
    );
    
    if (confirm !== 'Yes, Clear All') return;
    
    try {
        const config = vscode.workspace.getConfiguration('contextlite');
        const port = config.get('serverPort', 8081);
        
        // For now, just show a message - you'd need to add a clear endpoint to your API
        vscode.window.showInformationMessage('Context cleared (restart ContextLite to reset database)');
        outputChannel.appendLine('Context database clear requested');
        
    } catch (error) {
        vscode.window.showErrorMessage(`Failed to clear context: ${error}`);
        outputChannel.appendLine(`Error: ${error}`);
    }
}
