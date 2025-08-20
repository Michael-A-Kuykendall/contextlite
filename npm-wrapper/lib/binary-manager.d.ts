/**
 * ContextLite Binary Manager for Node.js
 *
 * Handles detection, download, and management of ContextLite binaries
 * across different platforms and installation methods.
 */
export declare class BinaryNotFoundError extends Error {
    constructor(message?: string);
}
export declare class DownloadError extends Error {
    constructor(message: string);
}
export declare class BinaryManager {
    private readonly binaryName;
    private readonly platform;
    private readonly arch;
    private readonly githubRepo;
    constructor();
    /**
     * Find ContextLite binary using multiple detection strategies.
     */
    getBinaryPath(): Promise<string | null>;
    /**
     * Download ContextLite binary from GitHub releases.
     */
    downloadBinary(version?: string): Promise<string>;
    /**
     * Find binary in system PATH.
     */
    private findInPath;
    /**
     * Find binary in common system installation locations.
     */
    private findInSystemLocations;
    /**
     * Find binary in Node.js package data directory.
     */
    private findInPackageData;
    /**
     * Find binary in user data directory.
     */
    private findInUserData;
    /**
     * Get the path where user-specific binary should be stored.
     */
    private getUserBinaryPath;
    /**
     * Detect the current platform.
     */
    private detectPlatform;
    /**
     * Detect the current architecture.
     */
    private detectArchitecture;
    /**
     * Get download URL for the specified version and platform.
     */
    private getDownloadUrl;
}
//# sourceMappingURL=binary-manager.d.ts.map