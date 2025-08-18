const vscode = require('vscode');
const cp = require('child_process');
const path = require('path');
const os = require('os');

let contextliteProcess = null;

function activate(context) {
    console.log('ContextLite extension is now active');

    // Register commands
    const startCommand = vscode.commands.registerCommand('contextlite.start', startContextLite);
    const indexCommand = vscode.commands.registerCommand('contextlite.index', indexWorkspace);
    const stopCommand = vscode.commands.registerCommand('contextlite.stop', stopContextLite);

    context.subscriptions.push(startCommand, indexCommand, stopCommand);
}

async function startContextLite() {
    if (contextliteProcess) {
        vscode.window.showInformationMessage('ContextLite is already running');
        return;
    }

    try {
        const binaryPath = await findContextLiteBinary();
        if (!binaryPath) {
            const action = await vscode.window.showErrorMessage(
                'ContextLite binary not found. Would you like to download it?',
                'Download', 'Cancel'
            );
            if (action === 'Download') {
                await downloadContextLite();
                return startContextLite();
            }
            return;
        }

        contextliteProcess = cp.spawn(binaryPath, ['--port', '8080'], {
            detached: true,
            stdio: 'ignore'
        });

        contextliteProcess.on('error', (error) => {
            vscode.window.showErrorMessage(`Failed to start ContextLite: ${error.message}`);
            contextliteProcess = null;
        });

        vscode.window.showInformationMessage('ContextLite server started on port 8080');
    } catch (error) {
        vscode.window.showErrorMessage(`Error starting ContextLite: ${error.message}`);
    }
}

async function indexWorkspace() {
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders) {
        vscode.window.showErrorMessage('No workspace folder open');
        return;
    }

    const binaryPath = await findContextLiteBinary();
    if (!binaryPath) {
        vscode.window.showErrorMessage('ContextLite binary not found');
        return;
    }

    const workspacePath = workspaceFolders[0].uri.fsPath;
    
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: 'Indexing workspace with ContextLite...',
        cancellable: false
    }, async (progress) => {
        return new Promise((resolve, reject) => {
            const indexProcess = cp.spawn(binaryPath, ['index', workspacePath], {
                stdio: 'pipe'
            });

            indexProcess.on('close', (code) => {
                if (code === 0) {
                    vscode.window.showInformationMessage('Workspace indexed successfully');
                    resolve();
                } else {
                    vscode.window.showErrorMessage('Failed to index workspace');
                    reject(new Error(`Process exited with code ${code}`));
                }
            });
        });
    });
}

function stopContextLite() {
    if (contextliteProcess) {
        contextliteProcess.kill();
        contextliteProcess = null;
        vscode.window.showInformationMessage('ContextLite server stopped');
    } else {
        vscode.window.showInformationMessage('ContextLite is not running');
    }
}

async function findContextLiteBinary() {
    // Check if contextlite is in PATH
    return new Promise((resolve) => {
        cp.exec('contextlite --version', (error) => {
            if (!error) {
                resolve('contextlite');
            } else {
                // Check common installation locations
                const possiblePaths = [
                    path.join(os.homedir(), '.local', 'bin', 'contextlite'),
                    path.join(os.homedir(), '.contextlite', 'contextlite'),
                    '/usr/local/bin/contextlite',
                    '/usr/bin/contextlite'
                ];

                if (os.platform() === 'win32') {
                    possiblePaths.push(
                        path.join(os.homedir(), '.contextlite', 'contextlite.exe'),
                        'C:\\Program Files\\ContextLite\\contextlite.exe'
                    );
                }

                // Check each path
                for (const binPath of possiblePaths) {
                    try {
                        require('fs').accessSync(binPath, require('fs').constants.F_OK);
                        resolve(binPath);
                        return;
                    } catch (e) {
                        // Continue checking
                    }
                }
                resolve(null);
            }
        });
    });
}

async function downloadContextLite() {
    vscode.window.showInformationMessage(
        'Please download ContextLite from: https://github.com/Michael-A-Kuykendall/contextlite/releases/latest'
    );
}

function deactivate() {
    if (contextliteProcess) {
        contextliteProcess.kill();
    }
}

module.exports = {
    activate,
    deactivate
};
