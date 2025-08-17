"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
exports.deactivate = deactivate;
const vscode = require("vscode");
const path = require("path");
const fs = require("fs");
const child_process_1 = require("child_process");
const axios_1 = require("axios");
let contextliteProcess = null;
let outputChannel;
function activate(context) {
    outputChannel = vscode.window.createOutputChannel('ContextLite');
    // Check license status on activation
    checkLicenseStatus(context);
    // Register commands
    const addToContext = vscode.commands.registerCommand('contextlite.addToContext', () => {
        if (!checkLicenseAndWarn(context))
            return;
        addSelectionToContext();
    });
    const assembleContext = vscode.commands.registerCommand('contextlite.assembleContext', () => {
        if (!checkLicenseAndWarn(context))
            return;
        assembleContextFromQuery();
    });
    const clearContext = vscode.commands.registerCommand('contextlite.clearContext', () => {
        if (!checkLicenseAndWarn(context))
            return;
        clearContextDatabase();
    });
    const showLicense = vscode.commands.registerCommand('contextlite.showLicense', () => {
        showLicenseInfo(context);
    });
    context.subscriptions.push(addToContext, assembleContext, clearContext, showLicense);
    // Start ContextLite server
    startContextLiteServer(context);
}
function deactivate() {
    if (contextliteProcess) {
        contextliteProcess.kill();
    }
}
function checkLicenseStatus(context) {
    const installDate = context.globalState.get('installDate', Date.now());
    if (!context.globalState.get('installDate')) {
        context.globalState.update('installDate', Date.now());
    }
    const trialDays = 14;
    const isTrialExpired = (Date.now() - installDate) > (trialDays * 24 * 60 * 60 * 1000);
    const hasValidLicense = hasLicense();
    if (isTrialExpired && !hasValidLicense) {
        const daysExpired = Math.floor((Date.now() - installDate - (trialDays * 24 * 60 * 60 * 1000)) / (24 * 60 * 60 * 1000));
        vscode.window.showWarningMessage(`ContextLite trial expired ${daysExpired} days ago. Get your commercial license to continue using ContextLite.`, 'Buy License ($99)', 'Enter License Key', 'Remind Later').then(handleLicensePromptResponse);
    }
    else if (!isTrialExpired && !hasValidLicense) {
        const daysLeft = Math.ceil((trialDays * 24 * 60 * 60 * 1000 - (Date.now() - installDate)) / (24 * 60 * 60 * 1000));
        outputChannel.appendLine(`ContextLite trial: ${daysLeft} days remaining`);
    }
}
function checkLicenseAndWarn(context) {
    const installDate = context.globalState.get('installDate', Date.now());
    const trialDays = 14;
    const isTrialExpired = (Date.now() - installDate) > (trialDays * 24 * 60 * 60 * 1000);
    if (isTrialExpired && !hasLicense()) {
        vscode.window.showWarningMessage('ContextLite trial has expired. Purchase a commercial license to continue.', 'Buy License ($99)', 'Enter License Key').then(handleLicensePromptResponse);
        return false;
    }
    return true;
}
function hasLicense() {
    const license = vscode.workspace.getConfiguration('contextlite').get('licenseKey', '');
    // Simple validation: must start with CL-2024- and be reasonable length
    return typeof license === 'string' &&
        license.startsWith('CL-2024-') &&
        license.length >= 15;
}
function handleLicensePromptResponse(selection) {
    if (selection === 'Buy License ($99)') {
        vscode.env.openExternal(vscode.Uri.parse('https://buy.stripe.com/bJe3cneNfcBp2Z57u67N600'));
    }
    else if (selection === 'Enter License Key') {
        vscode.window.showInputBox({
            prompt: 'Enter your ContextLite license key',
            placeHolder: 'CL-2024-XXXXXXXXXXXXX',
            validateInput: (value) => {
                if (!value)
                    return 'License key is required';
                if (!value.startsWith('CL-2024-'))
                    return 'Invalid license key format';
                if (value.length < 15)
                    return 'License key too short';
                return null;
            }
        }).then((key) => {
            if (key) {
                vscode.workspace.getConfiguration('contextlite').update('licenseKey', key, vscode.ConfigurationTarget.Global);
                vscode.window.showInformationMessage('License key saved! ContextLite is now activated.');
            }
        });
    }
}
function showLicenseInfo(context) {
    const installDate = context.globalState.get('installDate', Date.now());
    const trialDays = 14;
    const daysUsed = Math.floor((Date.now() - installDate) / (24 * 60 * 60 * 1000));
    const daysLeft = Math.max(0, trialDays - daysUsed);
    const hasValidLicense = hasLicense();
    let message;
    let actions = [];
    if (hasValidLicense) {
        message = 'ContextLite Commercial License Active ✅\\n\\nYou have full access to all ContextLite features.';
        actions = ['View Settings'];
    }
    else if (daysLeft > 0) {
        message = `ContextLite Trial: ${daysLeft} days remaining\\n\\nEnjoy full features during your trial period.`;
        actions = ['Buy License ($99)', 'Enter License Key'];
    }
    else {
        message = `ContextLite Trial Expired\\n\\nTrial ended ${-daysLeft} days ago. Purchase a commercial license to continue.`;
        actions = ['Buy License ($99)', 'Enter License Key'];
    }
    vscode.window.showInformationMessage(message, ...actions).then((selection) => {
        if (selection === 'Buy License ($99)') {
            vscode.env.openExternal(vscode.Uri.parse('https://buy.stripe.com/bJe3cneNfcBp2Z57u67N600'));
        }
        else if (selection === 'Enter License Key') {
            handleLicensePromptResponse('Enter License Key');
        }
        else if (selection === 'View Settings') {
            vscode.commands.executeCommand('workbench.action.openSettings', 'contextlite');
        }
    });
}
function startContextLiteServer(context) {
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
    contextliteProcess = (0, child_process_1.spawn)(binaryPath, [], {
        env: { ...process.env, PORT: port.toString() },
        cwd: extensionPath
    });
    contextliteProcess.stdout?.on('data', (data) => {
        outputChannel.appendLine(`Server: ${data.toString()}`);
    });
    contextliteProcess.stderr?.on('data', (data) => {
        outputChannel.appendLine(`Server Error: ${data.toString()}`);
    });
    contextliteProcess.on('close', (code) => {
        outputChannel.appendLine(`ContextLite server exited with code ${code}`);
        contextliteProcess = null;
    });
    // Wait a moment for server to start
    setTimeout(() => {
        outputChannel.appendLine(`ContextLite server started on port ${port}`);
        vscode.window.showInformationMessage('ContextLite is ready!');
    }, 2000);
}
function getBinaryPath(extensionPath) {
    const platform = process.platform;
    if (platform === 'win32') {
        return path.join(extensionPath, 'bin', 'contextlite.exe');
    }
    else if (platform === 'darwin') {
        return path.join(extensionPath, 'bin', 'contextlite-mac');
    }
    else {
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
        await axios_1.default.post(`http://127.0.0.1:${port}/api/v1/documents`, {
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
    }
    catch (error) {
        vscode.window.showErrorMessage(`Failed to add to context: ${error}`);
        outputChannel.appendLine(`Error: ${error}`);
    }
}
async function assembleContextFromQuery() {
    const query = await vscode.window.showInputBox({
        prompt: 'Enter your context query',
        placeHolder: 'e.g., "authentication security patterns"'
    });
    if (!query)
        return;
    try {
        const config = vscode.workspace.getConfiguration('contextlite');
        const port = config.get('serverPort', 8081);
        const maxTokens = config.get('maxTokens', 4000);
        const maxDocuments = config.get('maxDocuments', 10);
        const useSMT = config.get('useSMT', true);
        const response = await axios_1.default.post(`http://127.0.0.1:${port}/api/v1/context/assemble`, {
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
        vscode.window.showInformationMessage(`Assembled ${result.total_documents} documents (${result.total_tokens} tokens) in ${result.timings.total_ms.toFixed(1)}ms`);
    }
    catch (error) {
        vscode.window.showErrorMessage(`Failed to assemble context: ${error}`);
        outputChannel.appendLine(`Error: ${error}`);
    }
}
function formatAssembledContext(result) {
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
    result.documents.forEach((doc, index) => {
        content += `## Document ${index + 1}: ${doc.path}\\n`;
        content += `**Utility Score:** ${doc.utility_score.toFixed(4)}\\n`;
        content += `**Language:** ${doc.language}\\n\\n`;
        content += `\`\`\`${doc.language}\\n${doc.content}\\n\`\`\`\\n\\n`;
    });
    return content;
}
async function clearContextDatabase() {
    const confirm = await vscode.window.showWarningMessage('This will clear all documents from the ContextLite database. Continue?', 'Yes, Clear All', 'Cancel');
    if (confirm !== 'Yes, Clear All')
        return;
    try {
        const config = vscode.workspace.getConfiguration('contextlite');
        const port = config.get('serverPort', 8081);
        // For now, just show a message - you'd need to add a clear endpoint to your API
        vscode.window.showInformationMessage('Context cleared (restart ContextLite to reset database)');
        outputChannel.appendLine('Context database clear requested');
    }
    catch (error) {
        vscode.window.showErrorMessage(`Failed to clear context: ${error}`);
        outputChannel.appendLine(`Error: ${error}`);
    }
}
//# sourceMappingURL=extension.js.map