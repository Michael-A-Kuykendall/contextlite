/*
 * ContextLite Private Library C Interface
 * Copyright (c) 2025 Michael A. Kuykendall
 * 
 * Patent Pending - Provisional Patent Filed
 * 
 * This file provides a C interface for the private ContextLite engine
 * allowing it to be used as a compiled library from the public repository.
 */

//go:build library
// +build library

package main

import "C"
import (
	"encoding/json"
)

// Conditional compilation: only build this when library tag is present
// This prevents build errors when private repository is not available

var (
	engines = make(map[int]interface{}) // Use interface{} instead of private type
	nextID  = 1
)

//export CreateEngine
func CreateEngine(configJSON *C.char) C.int {
	// This is a stub implementation for when private binary is not available
	// In production, this would interface with the private binary
	return -1 // Return error code when private engine not available
}

//export DestroyEngine
func DestroyEngine(engineID C.int) {
	// Stub implementation - would cleanup engine resources
	id := int(engineID)
	if _, exists := engines[id]; exists {
		delete(engines, id)
	}
}

//export AssembleContext
func AssembleContext(engineID C.int, requestJSON *C.char) *C.char {
	// Stub implementation - would call private engine
	return C.CString(`{"error": "private engine not available - install ContextLite Pro"}`)
}

//export GetEngineStats
func GetEngineStats(engineID C.int) *C.char {
	// Stub implementation - would return engine statistics
	errorResp := map[string]string{"error": "private engine not available - install ContextLite Pro"}
	errorJSON, _ := json.Marshal(errorResp)
	return C.CString(string(errorJSON))
}

//export IsEngineReady
func IsEngineReady(engineID C.int) C.int {
	// Stub implementation - always return not ready (0) for community version
	return 0
}

//export GetVersion
func GetVersion() *C.char {
	return C.CString("ContextLite Community v1.1.22 - Pro features require upgrade")
}

// Required main function for library builds
func main() {
	// This main function should never be called in library mode
	// It's only here to satisfy Go's package main requirement
}
