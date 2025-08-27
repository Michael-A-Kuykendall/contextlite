"use strict";
/**
 * ContextLite Binary Manager for Node.js
 *
 * Handles detection, download, and management of ContextLite binaries
 * across different platforms and installation methods.
 */
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.BinaryManager = exports.DownloadError = exports.BinaryNotFoundError = void 0;
const fs_1 = require("fs");
const fs_2 = require("fs");
const path_1 = require("path");
const os_1 = require("os");
const node_fetch_1 = __importDefault(require("node-fetch"));
class BinaryNotFoundError extends Error {
    constructor(message = 'ContextLite binary not found') {
        super(message);
        this.name = 'BinaryNotFoundError';
    }
}
exports.BinaryNotFoundError = BinaryNotFoundError;
class DownloadError extends Error {
    constructor(message) {
        super(message);
        this.name = 'DownloadError';
    }
}
exports.DownloadError = DownloadError;
class BinaryManager {
    constructor() {
        this.githubRepo = 'Michael-A-Kuykendall/contextlite';
        this.binaryName = (0, os_1.platform)() === 'win32' ? 'contextlite.exe' : 'contextlite';
        this.platform = this.detectPlatform();
        this.arch = this.detectArchitecture();
    }
    /**
     * Find ContextLite binary using multiple detection strategies.
     */
    async getBinaryPath() {
        // Strategy 1: Check PATH
        const pathBinary = this.findInPath();
        if (pathBinary) {
            return pathBinary;
        }
        // Strategy 2: Check common install locations
        const systemBinary = this.findInSystemLocations();
        if (systemBinary) {
            return systemBinary;
        }
        // Strategy 3: Check package data directory
        const packageBinary = this.findInPackageData();
        if (packageBinary) {
            return packageBinary;
        }
        // Strategy 4: Check user data directory
        const userBinary = this.findInUserData();
        if (userBinary) {
            return userBinary;
        }
        return null;
    }
    /**
     * Download ContextLite binary from GitHub releases.
     */
    async downloadBinary(version = 'latest') {
        try {
            const downloadUrl = await this.getDownloadUrl(version);
            const destPath = this.getUserBinaryPath();
            console.log(`📥 Downloading ContextLite ${version} for ${this.platform}-${this.arch}...`);
            const response = await (0, node_fetch_1.default)(downloadUrl);
            if (!response.ok) {
                throw new Error(`HTTP ${response.status}: ${response.statusText}`);
            }
            // Create directory if it doesn't exist
            (0, fs_1.mkdirSync)((0, path_1.dirname)(destPath), { recursive: true });
            // Download and save binary
            const fileStream = (0, fs_2.createWriteStream)(destPath);
            response.body?.pipe(fileStream);
            await new Promise((resolve, reject) => {
                fileStream.on('finish', () => resolve());
                fileStream.on('error', reject);
            });
            // Make executable on Unix systems
            if ((0, os_1.platform)() !== 'win32') {
                (0, fs_1.chmodSync)(destPath, 0o755);
            }
            console.log(`✅ ContextLite downloaded to: ${destPath}`);
            return destPath;
        }
        catch (error) {
            throw new DownloadError(`Failed to download binary: ${error}`);
        }
    }
    /**
     * Find binary in system PATH.
     */
    findInPath() {
        const pathVar = process.env.PATH || '';
        const pathSeparator = (0, os_1.platform)() === 'win32' ? ';' : ':';
        const paths = pathVar.split(pathSeparator);
        for (const dir of paths) {
            if (!dir)
                continue;
            const binaryPath = (0, path_1.join)(dir, this.binaryName);
            if ((0, fs_1.existsSync)(binaryPath)) {
                return binaryPath;
            }
        }
        return null;
    }
    /**
     * Find binary in common system installation locations.
     */
    findInSystemLocations() {
        let locations = [];
        if ((0, os_1.platform)() === 'win32') {
            const programFiles = process.env.PROGRAMFILES || 'C:\\Program Files';
            const programFilesX86 = process.env['PROGRAMFILES(X86)'] || 'C:\\Program Files (x86)';
            const localAppData = process.env.LOCALAPPDATA || '';
            locations = [
                (0, path_1.join)(programFiles, 'ContextLite', this.binaryName),
                (0, path_1.join)(programFilesX86, 'ContextLite', this.binaryName),
                (0, path_1.join)(localAppData, 'Programs', 'ContextLite', this.binaryName),
            ];
        }
        else if ((0, os_1.platform)() === 'darwin') {
            locations = [
                '/usr/local/bin/contextlite',
                '/opt/homebrew/bin/contextlite',
                '/Applications/ContextLite.app/Contents/MacOS/contextlite',
                (0, path_1.join)((0, os_1.homedir)(), 'Applications', 'ContextLite.app', 'Contents', 'MacOS', 'contextlite'),
            ];
        }
        else {
            locations = [
                '/usr/local/bin/contextlite',
                '/usr/bin/contextlite',
                '/opt/contextlite/contextlite',
                (0, path_1.join)((0, os_1.homedir)(), '.local', 'bin', 'contextlite'),
            ];
        }
        for (const location of locations) {
            if ((0, fs_1.existsSync)(location)) {
                return location;
            }
        }
        return null;
    }
    /**
     * Find binary in Node.js package data directory.
     */
    findInPackageData() {
        const packageDir = (0, path_1.join)(__dirname, '..');
        const binaryPath = (0, path_1.join)(packageDir, 'bin', this.binaryName);
        return (0, fs_1.existsSync)(binaryPath) ? binaryPath : null;
    }
    /**
     * Find binary in user data directory.
     */
    findInUserData() {
        const userBinary = this.getUserBinaryPath();
        return (0, fs_1.existsSync)(userBinary) ? userBinary : null;
    }
    /**
     * Get the path where user-specific binary should be stored.
     */
    getUserBinaryPath() {
        let dataDir;
        if ((0, os_1.platform)() === 'win32') {
            dataDir = (0, path_1.join)(process.env.APPDATA || (0, os_1.homedir)(), 'ContextLite');
        }
        else if ((0, os_1.platform)() === 'darwin') {
            dataDir = (0, path_1.join)((0, os_1.homedir)(), 'Library', 'Application Support', 'ContextLite');
        }
        else {
            dataDir = (0, path_1.join)(process.env.XDG_DATA_HOME || (0, path_1.join)((0, os_1.homedir)(), '.local', 'share'), 'contextlite');
        }
        return (0, path_1.join)(dataDir, 'bin', this.binaryName);
    }
    /**
     * Detect the current platform.
     */
    detectPlatform() {
        const platformName = (0, os_1.platform)();
        switch (platformName) {
            case 'darwin':
                return 'darwin';
            case 'win32':
                return 'windows';
            default:
                return 'linux';
        }
    }
    /**
     * Detect the current architecture.
     */
    detectArchitecture() {
        const archName = (0, os_1.arch)();
        switch (archName) {
            case 'x64':
                return 'amd64';
            case 'arm64':
                return 'arm64';
            default:
                return 'amd64'; // Default fallback
        }
    }
    /**
     * Get download URL for the specified version and platform.
     */
    async getDownloadUrl(version) {
        if (version === 'latest') {
            // Get latest release info from GitHub API
            const apiUrl = `https://api.github.com/repos/${this.githubRepo}/releases/latest`;
            const response = await (0, node_fetch_1.default)(apiUrl);
            if (!response.ok) {
                throw new Error(`Failed to fetch release info: ${response.statusText}`);
            }
            const releaseData = await response.json();
            version = releaseData.tag_name.replace(/^v/, '');
        }
        // Construct binary filename based on platform and architecture
        let filename;
        if (this.platform === 'windows') {
            filename = `contextlite-${version}-windows-${this.arch}.zip`;
        }
        else {
            filename = `contextlite-${version}-${this.platform}-${this.arch}.tar.gz`;
        }
        return `https://github.com/${this.githubRepo}/releases/download/v${version}/${filename}`;
    }
}
exports.BinaryManager = BinaryManager;
//# sourceMappingURL=binary-manager.js.map