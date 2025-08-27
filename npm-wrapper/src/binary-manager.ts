/**
 * ContextLite Binary Manager for Node.js
 * 
 * Handles detection, download, and management of ContextLite binaries
 * across different platforms and installation methods.
 */

import { spawn } from 'child_process';
import { existsSync, chmodSync, mkdirSync } from 'fs';
import { createWriteStream } from 'fs';
import { dirname, join } from 'path';
import { homedir, platform, arch, type } from 'os';
import fetch from 'node-fetch';

export class BinaryNotFoundError extends Error {
    constructor(message: string = 'ContextLite binary not found') {
        super(message);
        this.name = 'BinaryNotFoundError';
    }
}

export class DownloadError extends Error {
    constructor(message: string) {
        super(message);
        this.name = 'DownloadError';
    }
}

export class BinaryManager {
    private readonly binaryName: string;
    private readonly platform: string;
    private readonly arch: string;
    private readonly githubRepo = 'Michael-A-Kuykendall/contextlite';

    constructor() {
        this.binaryName = platform() === 'win32' ? 'contextlite.exe' : 'contextlite';
        this.platform = this.detectPlatform();
        this.arch = this.detectArchitecture();
    }

    /**
     * Find ContextLite binary using multiple detection strategies.
     */
    async getBinaryPath(): Promise<string | null> {
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
    async downloadBinary(version: string = 'latest'): Promise<string> {
        try {
            const downloadUrl = await this.getDownloadUrl(version);
            const destPath = this.getUserBinaryPath();

            console.log(`📥 Downloading ContextLite ${version} for ${this.platform}-${this.arch}...`);

            const response = await fetch(downloadUrl);
            if (!response.ok) {
                throw new Error(`HTTP ${response.status}: ${response.statusText}`);
            }

            // Create directory if it doesn't exist
            mkdirSync(dirname(destPath), { recursive: true });

            // Download and save binary
            const fileStream = createWriteStream(destPath);
            response.body?.pipe(fileStream);

            await new Promise<void>((resolve, reject) => {
                fileStream.on('finish', resolve);
                fileStream.on('error', reject);
            });

            // Make executable on Unix systems
            if (platform() !== 'win32') {
                chmodSync(destPath, 0o755);
            }

            console.log(`✅ ContextLite downloaded to: ${destPath}`);
            return destPath;

        } catch (error) {
            throw new DownloadError(`Failed to download binary: ${error}`);
        }
    }

    /**
     * Find binary in system PATH.
     */
    private findInPath(): string | null {
        const pathVar = process.env.PATH || '';
        const pathSeparator = platform() === 'win32' ? ';' : ':';
        const paths = pathVar.split(pathSeparator);

        for (const dir of paths) {
            if (!dir) continue;
            const binaryPath = join(dir, this.binaryName);
            if (existsSync(binaryPath)) {
                return binaryPath;
            }
        }

        return null;
    }

    /**
     * Find binary in common system installation locations.
     */
    private findInSystemLocations(): string | null {
        let locations: string[] = [];

        if (platform() === 'win32') {
            const programFiles = process.env.PROGRAMFILES || 'C:\\Program Files';
            const programFilesX86 = process.env['PROGRAMFILES(X86)'] || 'C:\\Program Files (x86)';
            const localAppData = process.env.LOCALAPPDATA || '';

            locations = [
                join(programFiles, 'ContextLite', this.binaryName),
                join(programFilesX86, 'ContextLite', this.binaryName),
                join(localAppData, 'Programs', 'ContextLite', this.binaryName),
            ];
        } else if (platform() === 'darwin') {
            locations = [
                '/usr/local/bin/contextlite',
                '/opt/homebrew/bin/contextlite',
                '/Applications/ContextLite.app/Contents/MacOS/contextlite',
                join(homedir(), 'Applications', 'ContextLite.app', 'Contents', 'MacOS', 'contextlite'),
            ];
        } else {
            locations = [
                '/usr/local/bin/contextlite',
                '/usr/bin/contextlite',
                '/opt/contextlite/contextlite',
                join(homedir(), '.local', 'bin', 'contextlite'),
            ];
        }

        for (const location of locations) {
            if (existsSync(location)) {
                return location;
            }
        }

        return null;
    }

    /**
     * Find binary in Node.js package data directory.
     */
    private findInPackageData(): string | null {
        const packageDir = join(__dirname, '..');
        const binaryPath = join(packageDir, 'bin', this.binaryName);

        return existsSync(binaryPath) ? binaryPath : null;
    }

    /**
     * Find binary in user data directory.
     */
    private findInUserData(): string | null {
        const userBinary = this.getUserBinaryPath();
        return existsSync(userBinary) ? userBinary : null;
    }

    /**
     * Get the path where user-specific binary should be stored.
     */
    private getUserBinaryPath(): string {
        let dataDir: string;

        if (platform() === 'win32') {
            dataDir = join(process.env.APPDATA || homedir(), 'ContextLite');
        } else if (platform() === 'darwin') {
            dataDir = join(homedir(), 'Library', 'Application Support', 'ContextLite');
        } else {
            dataDir = join(process.env.XDG_DATA_HOME || join(homedir(), '.local', 'share'), 'contextlite');
        }

        return join(dataDir, 'bin', this.binaryName);
    }

    /**
     * Detect the current platform.
     */
    private detectPlatform(): string {
        const platformName = platform();
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
    private detectArchitecture(): string {
        const archName = arch();
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
    private async getDownloadUrl(version: string): Promise<string> {
        if (version === 'latest') {
            // Get latest release info from GitHub API
            const apiUrl = `https://api.github.com/repos/${this.githubRepo}/releases/latest`;
            const response = await fetch(apiUrl);
            
            if (!response.ok) {
                throw new Error(`Failed to fetch release info: ${response.statusText}`);
            }
            
            const releaseData = await response.json() as any;
            version = releaseData.tag_name.replace(/^v/, '');
        }

        // Construct binary filename based on platform and architecture
        let filename: string;
        if (this.platform === 'windows') {
            filename = `contextlite-${version}-windows-${this.arch}.zip`;
        } else {
            filename = `contextlite-${version}-${this.platform}-${this.arch}.tar.gz`;
        }

        return `https://github.com/${this.githubRepo}/releases/download/v${version}/${filename}`;
    }
}
