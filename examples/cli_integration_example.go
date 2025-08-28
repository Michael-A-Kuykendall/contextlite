package main

import (
	"encoding/json"
	"fmt"
	"log"
	"os"
	"path/filepath"
)

// Simple example showing how to integrate ContextLite discovery into CLI tools
func main() {
	fmt.Println("🚀 ContextLite CLI Integration Example")
	fmt.Println("=====================================")
	
	// Example 1: For Claude CLI integration
	fmt.Println("\n📝 Example 1: Claude CLI Integration")
	claudeExample()
	
	// Example 2: For cursor integration  
	fmt.Println("\n🎯 Example 2: Cursor Integration")
	cursorExample()
	
	// Example 3: For rust-chain integration
	fmt.Println("\n🦀 Example 3: Rust-chain Integration")
	rustChainExample()
}

func claudeExample() {
	// This is what you'd integrate into Claude CLI
	currentDir, _ := os.Getwd()
	projectName := filepath.Base(currentDir)
	userQuery := "How does authentication work in this codebase?"
	
	fmt.Printf("   Project: %s\n", projectName)
	fmt.Printf("   Query: %s\n", userQuery)
	
	// Get context from ContextLite (this would be a function call to the CLI tool)
	contextResult := getProjectContext(projectName, userQuery)
	
	if contextResult["success"] == true {
		documents := contextResult["documents"].([]interface{})
		fmt.Printf("   ✅ Found %d relevant files for enhanced context\n", len(documents))
		
		// Claude would then use this context to provide better answers
		fmt.Println("   💡 Claude can now provide answers using your project's actual code")
	} else {
		fmt.Printf("   ⚠️ No ContextLite available: %v\n", contextResult["error"])
		fmt.Println("   💡 Claude continues without enhanced context")
	}
}

func cursorExample() {
	// This is what cursor could implement
	currentFile := "src/auth.rs" // Example current file
	
	fmt.Printf("   Current file: %s\n", currentFile)
	
	// Get related files from ContextLite
	relatedFiles := getRelatedFiles(currentFile)
	
	if len(relatedFiles) > 0 {
		fmt.Printf("   ✅ Found %d related files\n", len(relatedFiles))
		fmt.Printf("   📁 Related: %v\n", relatedFiles[:min(3, len(relatedFiles))])
		fmt.Println("   💡 Cursor can show these files in sidebar for context")
	} else {
		fmt.Println("   ⚠️ No related files found")
	}
}

func rustChainExample() {
	// This is what rust-chain could implement
	patterns := []string{
		"error handling patterns",
		"async function implementations",
		"trait definitions",
	}
	
	fmt.Printf("   Analyzing patterns: %v\n", patterns)
	
	foundPatterns := 0
	for _, pattern := range patterns {
		result := getProjectContext("rust-project", pattern)
		if result["success"] == true {
			foundPatterns++
		}
	}
	
	fmt.Printf("   ✅ Found code examples for %d/%d patterns\n", foundPatterns, len(patterns))
	fmt.Println("   💡 rust-chain can now provide specific examples from your codebase")
}

// Mock function - in reality this would call the contextlite-cli executable
func getProjectContext(projectName, query string) map[string]interface{} {
	// This would execute: ./contextlite-cli query projectName "query"
	// For demo purposes, return a mock result
	return map[string]interface{}{
		"success": true,
		"documents": []interface{}{
			map[string]interface{}{"path": "src/auth.go", "score": 0.95},
			map[string]interface{}{"path": "src/middleware.go", "score": 0.87},
		},
	}
}

// Mock function - in reality this would call the contextlite-cli executable  
func getRelatedFiles(currentFile string) []string {
	// This would execute: ./contextlite-cli query project "files related to currentFile"
	// For demo purposes, return mock related files
	return []string{"src/auth.go", "src/middleware.go", "tests/auth_test.go"}
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}
