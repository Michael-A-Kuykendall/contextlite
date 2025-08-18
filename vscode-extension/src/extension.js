"use strict";
var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {
    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
};
var __generator = (this && this.__generator) || function (thisArg, body) {
    var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g = Object.create((typeof Iterator === "function" ? Iterator : Object).prototype);
    return g.next = verb(0), g["throw"] = verb(1), g["return"] = verb(2), typeof Symbol === "function" && (g[Symbol.iterator] = function() { return this; }), g;
    function verb(n) { return function (v) { return step([n, v]); }; }
    function step(op) {
        if (f) throw new TypeError("Generator is already executing.");
        while (g && (g = 0, op[0] && (_ = 0)), _) try {
            if (f = 1, y && (t = op[0] & 2 ? y["return"] : op[0] ? y["throw"] || ((t = y["return"]) && t.call(y), 0) : y.next) && !(t = t.call(y, op[1])).done) return t;
            if (y = 0, t) op = [op[0] & 2, t.value];
            switch (op[0]) {
                case 0: case 1: t = op; break;
                case 4: _.label++; return { value: op[1], done: false };
                case 5: _.label++; y = op[1]; op = [0]; continue;
                case 7: op = _.ops.pop(); _.trys.pop(); continue;
                default:
                    if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }
                    if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }
                    if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }
                    if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }
                    if (t[2]) _.ops.pop();
                    _.trys.pop(); continue;
            }
            op = body.call(thisArg, _);
        } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }
        if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };
    }
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
exports.deactivate = deactivate;
// VS Code Extension for ContextLite
var vscode = require("vscode");
var cp = require("child_process");
var fs = require("fs");
var path = require("path");
var os = require("os");
var contextLiteProcess = null;
var outputChannel;
var statusBarItem;
function activate(context) {
    outputChannel = vscode.window.createOutputChannel('ContextLite');
    statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
    // Register commands
    context.subscriptions.push(vscode.commands.registerCommand('contextlite.start', startContextLite), vscode.commands.registerCommand('contextlite.stop', stopContextLite), vscode.commands.registerCommand('contextlite.status', showStatus), vscode.commands.registerCommand('contextlite.indexWorkspace', indexWorkspace), vscode.commands.registerCommand('contextlite.openUI', openUI), outputChannel, statusBarItem);
    // Auto-start if enabled
    var config = vscode.workspace.getConfiguration('contextlite');
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
function startContextLite() {
    return __awaiter(this, void 0, void 0, function () {
        var binaryPath, download, config, port, error_1;
        var _a, _b;
        return __generator(this, function (_c) {
            switch (_c.label) {
                case 0:
                    if (contextLiteProcess) {
                        vscode.window.showInformationMessage('ContextLite is already running');
                        return [2 /*return*/];
                    }
                    _c.label = 1;
                case 1:
                    _c.trys.push([1, 7, , 8]);
                    return [4 /*yield*/, findContextLiteBinary()];
                case 2:
                    binaryPath = _c.sent();
                    if (!!binaryPath) return [3 /*break*/, 6];
                    return [4 /*yield*/, vscode.window.showInformationMessage('ContextLite binary not found. Download it?', 'Download', 'Cancel')];
                case 3:
                    download = _c.sent();
                    if (!(download === 'Download')) return [3 /*break*/, 5];
                    return [4 /*yield*/, downloadContextLite()];
                case 4:
                    _c.sent();
                    return [2 /*return*/];
                case 5: return [2 /*return*/];
                case 6:
                    config = vscode.workspace.getConfiguration('contextlite');
                    port = config.get('serverPort', 8080);
                    contextLiteProcess = cp.spawn(binaryPath, ['--port', port.toString()], {
                        stdio: ['ignore', 'pipe', 'pipe']
                    });
                    (_a = contextLiteProcess.stdout) === null || _a === void 0 ? void 0 : _a.on('data', function (data) {
                        outputChannel.appendLine(data.toString());
                    });
                    (_b = contextLiteProcess.stderr) === null || _b === void 0 ? void 0 : _b.on('data', function (data) {
                        outputChannel.appendLine("ERROR: ".concat(data.toString()));
                    });
                    contextLiteProcess.on('close', function (code) {
                        outputChannel.appendLine("ContextLite process exited with code ".concat(code));
                        contextLiteProcess = null;
                        updateStatusBar('Stopped');
                    });
                    updateStatusBar('Running');
                    vscode.window.showInformationMessage('ContextLite started successfully');
                    // Auto-index workspace if available
                    if (vscode.workspace.workspaceFolders) {
                        setTimeout(function () { return indexWorkspace(); }, 2000);
                    }
                    return [3 /*break*/, 8];
                case 7:
                    error_1 = _c.sent();
                    outputChannel.appendLine("Failed to start ContextLite: ".concat(error_1));
                    vscode.window.showErrorMessage("Failed to start ContextLite: ".concat(error_1));
                    return [3 /*break*/, 8];
                case 8: return [2 /*return*/];
            }
        });
    });
}
function stopContextLite() {
    return __awaiter(this, void 0, void 0, function () {
        return __generator(this, function (_a) {
            if (!contextLiteProcess) {
                vscode.window.showInformationMessage('ContextLite is not running');
                return [2 /*return*/];
            }
            contextLiteProcess.kill();
            contextLiteProcess = null;
            updateStatusBar('Stopped');
            vscode.window.showInformationMessage('ContextLite stopped');
            return [2 /*return*/];
        });
    });
}
function showStatus() {
    return __awaiter(this, void 0, void 0, function () {
        var status, config, port;
        return __generator(this, function (_a) {
            status = contextLiteProcess ? 'Running' : 'Stopped';
            config = vscode.workspace.getConfiguration('contextlite');
            port = config.get('serverPort', 8080);
            vscode.window.showInformationMessage("ContextLite Status: ".concat(status).concat(status === 'Running' ? " (Port ".concat(port, ")") : ''));
            return [2 /*return*/];
        });
    });
}
function indexWorkspace() {
    return __awaiter(this, void 0, void 0, function () {
        var workspaceFolder, config, port, fetch_1, response, error_2;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0:
                    if (!contextLiteProcess) {
                        vscode.window.showWarningMessage('Start ContextLite first');
                        return [2 /*return*/];
                    }
                    if (!vscode.workspace.workspaceFolders) {
                        vscode.window.showWarningMessage('No workspace folder open');
                        return [2 /*return*/];
                    }
                    workspaceFolder = vscode.workspace.workspaceFolders[0];
                    config = vscode.workspace.getConfiguration('contextlite');
                    port = config.get('serverPort', 8080);
                    _a.label = 1;
                case 1:
                    _a.trys.push([1, 3, , 4]);
                    fetch_1 = require('node-fetch');
                    return [4 /*yield*/, fetch_1("http://localhost:".concat(port, "/api/workspace/index"), {
                            method: 'POST',
                            headers: { 'Content-Type': 'application/json' },
                            body: JSON.stringify({ path: workspaceFolder.uri.fsPath })
                        })];
                case 2:
                    response = _a.sent();
                    if (response.ok) {
                        vscode.window.showInformationMessage('Workspace indexed successfully');
                    }
                    else {
                        throw new Error("HTTP ".concat(response.status));
                    }
                    return [3 /*break*/, 4];
                case 3:
                    error_2 = _a.sent();
                    outputChannel.appendLine("Failed to index workspace: ".concat(error_2));
                    vscode.window.showErrorMessage("Failed to index workspace: ".concat(error_2));
                    return [3 /*break*/, 4];
                case 4: return [2 /*return*/];
            }
        });
    });
}
function openUI() {
    return __awaiter(this, void 0, void 0, function () {
        var config, port, url;
        return __generator(this, function (_a) {
            config = vscode.workspace.getConfiguration('contextlite');
            port = config.get('serverPort', 8080);
            url = "http://localhost:".concat(port);
            vscode.env.openExternal(vscode.Uri.parse(url));
            return [2 /*return*/];
        });
    });
}
function updateStatusBar(status) {
    statusBarItem.text = "$(database) ContextLite: ".concat(status);
    statusBarItem.show();
}
function findContextLiteBinary() {
    return __awaiter(this, void 0, void 0, function () {
        var config, customPath, possiblePaths, _i, possiblePaths_1, binPath;
        return __generator(this, function (_a) {
            config = vscode.workspace.getConfiguration('contextlite');
            customPath = config.get('binaryPath');
            if (customPath && fs.existsSync(customPath)) {
                return [2 /*return*/, customPath];
            }
            possiblePaths = [
                'contextlite', // In PATH
                path.join(os.homedir(), '.local', 'bin', 'contextlite'),
                path.join(os.homedir(), 'bin', 'contextlite'),
                '/usr/local/bin/contextlite',
                '/usr/bin/contextlite'
            ];
            for (_i = 0, possiblePaths_1 = possiblePaths; _i < possiblePaths_1.length; _i++) {
                binPath = possiblePaths_1[_i];
                try {
                    cp.execSync("\"".concat(binPath, "\" --version"), { stdio: 'ignore' });
                    return [2 /*return*/, binPath];
                }
                catch (_b) {
                    continue;
                }
            }
            return [2 /*return*/, null];
        });
    });
}
function downloadContextLite() {
    return __awaiter(this, void 0, void 0, function () {
        return __generator(this, function (_a) {
            vscode.window.showInformationMessage('Please visit https://contextlite.com/download to install ContextLite', 'Open Download Page').then(function (selection) {
                if (selection === 'Open Download Page') {
                    vscode.env.openExternal(vscode.Uri.parse('https://contextlite.com/download'));
                }
            });
            return [2 /*return*/];
        });
    });
}
