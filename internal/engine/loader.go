/*
 * ContextLite - optimization-Optimized AI Context Engine
 * Copyright (c) 2025 Michael A. Kuykendall
 * 
 * Patent Pending - Provisional Patent Filed
 * US Provisional Patent Application No. [PENDING]
 * 
 * This software contains proprietary algorithms protected by patent law.
 * Unauthorized reverse engineering or algorithm extraction is prohibited.
 * 
 * Licensed under Dual License:
 * - MIT License for open source use
 * - Commercial License for business use
 * 
 * See LICENSE-MIT.md and LICENSE-COMMERCIAL.md for terms.
 */

package engine

import (
	"os"
	"path/filepath"
	"runtime"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// LoadEngine attempts to load the private JSON CLI engine, falls back to core engine
func LoadEngine(cfg *config.Config, storage types.StorageInterface) types.ContextEngine {
	// Try to find private binary first
	if binaryPath := findPrivateBinary(); binaryPath != "" {
		return NewJSONCLIEngine(cfg, storage, binaryPath)
	}
	
	// Fallback to core engine (proven BM25 + heuristics)
	return NewCoreEngine(cfg, storage)
}

// findPrivateBinary searches for the private JSON CLI binary
func findPrivateBinary() string {
	// Try both with and without .exe extension for Windows compatibility
	var binaryNames []string
	switch runtime.GOOS {
	case "windows":
		binaryNames = []string{"contextlite-library.exe", "contextlite-library"}
	default:
		binaryNames = []string{"contextlite-library"}
	}
	
	// Try multiple locations for the private binary
	searchPaths := []string{
		"./",                                          // Current directory
		"../contextlite-private/build/",              // Development setup
		"/usr/local/bin/",                            // System install
		filepath.Join(getExecutableDir(), "bin/"),    // Relative to executable
		filepath.Join(getExecutableDir(), "../bin/"), // Parent bin directory
	}
	
	for _, basePath := range searchPaths {
		for _, binaryName := range binaryNames {
			binaryPath := filepath.Join(basePath, binaryName)
			
			// Check if binary exists and is executable
			if fileExists(binaryPath) && isExecutable(binaryPath) {
				return binaryPath
			}
		}
	}
	
	return "" // Private binary not found
}

// getExecutableDir returns the directory containing the current executable
func getExecutableDir() string {
	if execPath, err := getExecutablePath(); err == nil {
		return filepath.Dir(execPath)
	}
	return "."
}

// getExecutablePath returns the path to the current executable
func getExecutablePath() (string, error) {
	// This is a simplified version - could be enhanced with more robust detection
	return filepath.Abs(".")
}

// PrivateEngineAvailable checks if private JSON CLI binary is available
func PrivateEngineAvailable() bool {
	return findPrivateBinary() != ""
}

// fileExists checks if a file exists
func fileExists(filename string) bool {
	_, err := os.Stat(filename)
	return err == nil
}

// isExecutable checks if a file has execute permissions
func isExecutable(filename string) bool {
	info, err := os.Stat(filename)
	if err != nil {
		return false
	}
	
	// On Windows, check file extension OR assume binary is executable if it exists
	if runtime.GOOS == "windows" {
		ext := filepath.Ext(filename)
		return ext == ".exe" || ext == "" // Allow binaries without .exe extension
	}
	
	// On Unix-like systems, check execute permission
	return info.Mode()&0111 != 0
}

// GetEngineInfo returns information about the loaded engine
func GetEngineInfo(engine types.ContextEngine) map[string]interface{} {
	info := map[string]interface{}{
		"type": "unknown",
		"features": []string{},
	}
	
	// Try to determine engine type
	switch engine.(type) {
	case *CoreEngine:
		info["type"] = "core-engine"
		info["features"] = []string{"bm25-scoring", "heuristic-selection", "production-ready"}
		info["description"] = "Core engine with proven BM25 and heuristic algorithms"
		info["communication"] = "direct"
	case *JSONCLIEngine:
		info["type"] = "private-optimized"
		info["features"] = []string{"optimization-optimization", "7d-features", "patent-pending"}
		info["description"] = "Full Advanced engine with proprietary algorithms"
		info["communication"] = "json-cli"
	default:
		// Unknown engine type
		info["type"] = "unknown"
		info["features"] = []string{"unknown"}
		info["description"] = "Unknown engine implementation"
		info["communication"] = "unknown"
	}
	
	return info
}
