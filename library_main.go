/*
 * ContextLite Private Library C Interface
 * Copyright (c) 2025 Michael A. Kuykendall
 * 
 * Patent Pending - Provisional Patent Filed
 * 
 * This file provides a C interface for the private ContextLite engine
 * allowing it to be used as a compiled library from the public repository.
 */

package main

import "C"
import (
	"context"
	"encoding/json"
	"unsafe"

	"contextlite-private/internal"
	"contextlite-private/pkg/types"
)

var (
	engines = make(map[int]*internal.PrivateEngine)
	nextID  = 1
)

//export CreateEngine
func CreateEngine(configJSON *C.char) C.int {
	configStr := C.GoString(configJSON)
	
	var config types.EngineConfig
	if err := json.Unmarshal([]byte(configStr), &config); err != nil {
		return -1
	}
	
	// Note: Storage interface would need to be provided by public repo
	// For now, we'll return a placeholder
	engine, err := internal.NewPrivateEngine(nil, &config)
	if err != nil {
		return -1
	}
	
	engineID := nextID
	engines[engineID] = engine
	nextID++
	
	return C.int(engineID)
}

//export DestroyEngine
func DestroyEngine(engineID C.int) {
	id := int(engineID)
	if engine, exists := engines[id]; exists {
		engine.Close()
		delete(engines, id)
	}
}

//export AssembleContext
func AssembleContext(engineID C.int, requestJSON *C.char) *C.char {
	id := int(engineID)
	engine, exists := engines[id]
	if !exists {
		return C.CString(`{"error": "engine not found"}`)
	}
	
	requestStr := C.GoString(requestJSON)
	var request types.ContextRequest
	if err := json.Unmarshal([]byte(requestStr), &request); err != nil {
		return C.CString(`{"error": "invalid request"}`)
	}
	
	result, err := engine.AssembleContext(context.Background(), request)
	if err != nil {
		errorResp := map[string]string{"error": err.Error()}
		errorJSON, _ := json.Marshal(errorResp)
		return C.CString(string(errorJSON))
	}
	
	resultJSON, err := json.Marshal(result)
	if err != nil {
		return C.CString(`{"error": "serialization failed"}`)
	}
	
	return C.CString(string(resultJSON))
}

//export GetEngineStats
func GetEngineStats(engineID C.int) *C.char {
	id := int(engineID)
	engine, exists := engines[id]
	if !exists {
		return C.CString(`{"error": "engine not found"}`)
	}
	
	stats, err := engine.GetStats()
	if err != nil {
		errorResp := map[string]string{"error": err.Error()}
		errorJSON, _ := json.Marshal(errorResp)
		return C.CString(string(errorJSON))
	}
	
	statsJSON, err := json.Marshal(stats)
	if err != nil {
		return C.CString(`{"error": "serialization failed"}`)
	}
	
	return C.CString(string(statsJSON))
}

//export FreeString
func FreeString(str *C.char) {
	C.free(unsafe.Pointer(str))
}

// Version information
//export GetVersion
func GetVersion() *C.char {
	return C.CString("1.0.0-private")
}

// Required for shared library
func main() {}
