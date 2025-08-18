#!/usr/bin/env node

/**
 * Post-install script to download ContextLite binary
 * 
 * This script runs after npm install to automatically download
 * the appropriate ContextLite binary for the current platform.
 */

const { BinaryManager } = require('../lib/binary-manager');
const fs = require('fs');
const path = require('path');

async function fetchBinary() {
    try {
        console.log('🔍 Checking for ContextLite binary...');
        
        const binaryManager = new BinaryManager();
        const existingBinary = await binaryManager.getBinaryPath();
        
        if (existingBinary) {
            console.log(`✅ ContextLite binary found at: ${existingBinary}`);
            return;
        }
        
        console.log('📥 Downloading ContextLite binary...');
        
        try {
            const downloadedPath = await binaryManager.downloadBinary('latest');
            console.log(`✅ ContextLite binary downloaded successfully: ${downloadedPath}`);
        } catch (downloadError) {
            console.warn('⚠️  Failed to download ContextLite binary automatically.');
            console.warn('   You can download it manually from:');
            console.warn('   https://github.com/Michael-A-Kuykendall/contextlite/releases');
            console.warn(`   Error: ${downloadError.message}`);
        }
        
    } catch (error) {
        console.warn('⚠️  Error during binary setup:');
        console.warn(`   ${error.message}`);
        console.warn('   ContextLite may still work if the binary is installed globally.');
    }
}

// Only run if this is not a dev install
if (process.env.NODE_ENV !== 'development' && !process.env.npm_config_dev) {
    fetchBinary().catch(error => {
        console.warn(`⚠️  Binary fetch failed: ${error.message}`);
        process.exit(0); // Don't fail the install
    });
}
