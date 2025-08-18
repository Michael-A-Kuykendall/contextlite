#!/usr/bin/env node

/**
 * ContextLite CLI Wrapper for Node.js
 * 
 * This script provides the main entry point for the ContextLite npm package.
 * It handles binary detection, download, and execution.
 */

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

const { BinaryManager } = require('../lib/binary-manager');

async function main() {
    try {
        const binaryManager = new BinaryManager();
        const binaryPath = await binaryManager.getBinaryPath();
        
        if (!binaryPath) {
            console.error('❌ ContextLite binary not found!');
            console.error('\n🔧 To install ContextLite binary:');
            console.error('   Visit: https://github.com/Michael-A-Kuykendall/contextlite/releases');
            console.error('   Or reinstall this package: npm install -g contextlite');
            process.exit(1);
        }
        
        // Pass all arguments to the ContextLite binary
        const args = process.argv.slice(2);
        
        const child = spawn(binaryPath, args, {
            stdio: 'inherit',
            windowsHide: false
        });
        
        child.on('error', (error) => {
            console.error(`❌ Failed to execute ContextLite binary: ${error.message}`);
            process.exit(1);
        });
        
        child.on('exit', (code, signal) => {
            if (signal) {
                console.error(`\n⏹️  ContextLite interrupted by signal: ${signal}`);
                process.exit(128 + (signal === 'SIGINT' ? 2 : 15));
            } else {
                process.exit(code || 0);
            }
        });
        
        // Handle Ctrl+C gracefully
        process.on('SIGINT', () => {
            child.kill('SIGINT');
        });
        
        process.on('SIGTERM', () => {
            child.kill('SIGTERM');
        });
        
    } catch (error) {
        console.error(`❌ ContextLite error: ${error.message}`);
        process.exit(1);
    }
}

if (require.main === module) {
    main().catch(error => {
        console.error(`❌ Unexpected error: ${error.message}`);
        process.exit(1);
    });
}
