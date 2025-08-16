package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"time"
)

const (
	baseURL = "http://127.0.0.1:8080"
	token   = "contextlite-dev-token-2025"
)

type ContextRequest struct {
	Query        string `json:"query"`
	MaxTokens    int    `json:"max_tokens"`
	MaxDocuments int    `json:"max_documents"`
	UseSMT       bool   `json:"use_smt"`
	UseCache     bool   `json:"use_cache"`
}

type DocumentRequest struct {
	Path     string `json:"path"`
	Content  string `json:"content"`
	Type     string `json:"type"`
	Language string `json:"language"`
}

func main() {
	fmt.Println("🔐 ContextLite Authentication & Scale Demonstration")
	fmt.Println("==================================================")

	// Test 1: Authentication failure
	fmt.Println("\n1. Testing authentication failure (no token):")
	testAuthFailure()

	// Test 2: Authentication success
	fmt.Println("\n2. Testing authentication success (with token):")
	testAuthSuccess()

	// Test 3: Add multiple documents for scale testing
	fmt.Println("\n3. Adding documents for scale testing:")
	addTestDocuments()

	// Test 4: Context assembly with proper metrics
	fmt.Println("\n4. Testing context assembly with metrics:")
	testContextAssembly()

	fmt.Println("\n✅ All authentication and basic scale tests completed!")
}

func testAuthFailure() {
	req := ContextRequest{
		Query:        "machine learning",
		MaxTokens:    1000,
		MaxDocuments: 3,
		UseSMT:       true,
		UseCache:     true,
	}

	jsonData, _ := json.Marshal(req)
	
	// Make request without Authorization header
	resp, err := http.Post(baseURL+"/api/v1/context/assemble", "application/json", bytes.NewBuffer(jsonData))
	if err != nil {
		log.Printf("❌ Request failed: %v", err)
		return
	}
	defer resp.Body.Close()

	fmt.Printf("   Status: %d %s\n", resp.StatusCode, resp.Status)
	if resp.StatusCode == 401 {
		fmt.Println("   ✅ Authentication properly enforced (401 Unauthorized)")
	} else {
		fmt.Printf("   ❌ Expected 401, got %d\n", resp.StatusCode)
	}
}

func testAuthSuccess() {
	client := &http.Client{Timeout: 10 * time.Second}
	
	req := ContextRequest{
		Query:        "test",
		MaxTokens:    500,
		MaxDocuments: 2,
		UseSMT:       true,
		UseCache:     false,
	}

	jsonData, _ := json.Marshal(req)
	
	httpReq, _ := http.NewRequest("POST", baseURL+"/api/v1/context/assemble", bytes.NewBuffer(jsonData))
	httpReq.Header.Set("Content-Type", "application/json")
	httpReq.Header.Set("Authorization", "Bearer "+token)

	resp, err := client.Do(httpReq)
	if err != nil {
		log.Printf("❌ Request failed: %v", err)
		return
	}
	defer resp.Body.Close()

	fmt.Printf("   Status: %d %s\n", resp.StatusCode, resp.Status)
	if resp.StatusCode == 200 {
		fmt.Println("   ✅ Authentication successful (200 OK)")
	} else {
		fmt.Printf("   ❌ Expected 200, got %d\n", resp.StatusCode)
	}
}

func addTestDocuments() {
	client := &http.Client{Timeout: 10 * time.Second}
	
	documents := []DocumentRequest{
		{
			Path:     "ml_basics.md",
			Content:  "Machine learning is a subset of artificial intelligence that focuses on algorithms that can learn from data. It includes supervised learning, unsupervised learning, and reinforcement learning approaches.",
			Type:     "text",
			Language: "english",
		},
		{
			Path:     "deep_learning.md", 
			Content:  "Deep learning uses neural networks with multiple layers to learn complex patterns in data. Convolutional neural networks are used for image recognition while recurrent neural networks handle sequential data.",
			Type:     "text",
			Language: "english",
		},
		{
			Path:     "data_science.py",
			Content:  "import pandas as pd\\nimport numpy as np\\nfrom sklearn.model_selection import train_test_split\\n\\n# Data preprocessing for machine learning\\ndef preprocess_data(df):\\n    # Handle missing values\\n    df = df.fillna(df.mean())\\n    return df",
			Type:     "code",
			Language: "python",
		},
		{
			Path:     "statistics.md",
			Content:  "Statistical analysis forms the foundation of data science. Key concepts include probability distributions, hypothesis testing, regression analysis, and statistical inference. These methods help in understanding data patterns.",
			Type:     "text", 
			Language: "english",
		},
		{
			Path:     "algorithms.md",
			Content:  "Common machine learning algorithms include linear regression, logistic regression, decision trees, random forests, support vector machines, and neural networks. Each has different strengths and use cases.",
			Type:     "text",
			Language: "english",
		},
	}

	for i, doc := range documents {
		jsonData, _ := json.Marshal(doc)
		
		httpReq, _ := http.NewRequest("POST", baseURL+"/api/v1/documents", bytes.NewBuffer(jsonData))
		httpReq.Header.Set("Content-Type", "application/json")
		httpReq.Header.Set("Authorization", "Bearer "+token)

		resp, err := client.Do(httpReq)
		if err != nil {
			log.Printf("❌ Failed to add document %d: %v", i+1, err)
			continue
		}
		resp.Body.Close()

		fmt.Printf("   Document %d (%s): %d %s\n", i+1, doc.Path, resp.StatusCode, resp.Status)
	}
}

func testContextAssembly() {
	client := &http.Client{Timeout: 10 * time.Second}
	
	req := ContextRequest{
		Query:        "machine learning algorithms data",
		MaxTokens:    800,
		MaxDocuments: 4,
		UseSMT:       true,
		UseCache:     false,
	}

	jsonData, _ := json.Marshal(req)
	
	httpReq, _ := http.NewRequest("POST", baseURL+"/api/v1/context/assemble", bytes.NewBuffer(jsonData))
	httpReq.Header.Set("Content-Type", "application/json")
	httpReq.Header.Set("Authorization", "Bearer "+token)

	start := time.Now()
	resp, err := client.Do(httpReq)
	elapsed := time.Since(start)

	if err != nil {
		log.Printf("❌ Context assembly failed: %v", err)
		return
	}
	defer resp.Body.Close()

	fmt.Printf("   Status: %d %s\n", resp.StatusCode, resp.Status)
	fmt.Printf("   Response time: %v\n", elapsed)

	if resp.StatusCode == 200 {
		var result map[string]interface{}
		json.NewDecoder(resp.Body).Decode(&result)
		
		if smt, ok := result["smt_metrics"].(map[string]interface{}); ok {
			fmt.Printf("   SMT Solver: %v\n", smt["solver_used"])
			fmt.Printf("   Variables: %.0f\n", smt["variable_count"])
			fmt.Printf("   Constraints: %.0f\n", smt["constraint_count"])
			fmt.Printf("   SMT solve time: %.0fms\n", smt["solve_time_ms"])
		}
		
		if timings, ok := result["timings"].(map[string]interface{}); ok {
			fmt.Printf("   Total time: %.0fms\n", timings["total_ms"])
		}
		
		if docs, ok := result["documents"].([]interface{}); ok {
			fmt.Printf("   Documents selected: %d\n", len(docs))
		}
		
		fmt.Println("   ✅ Context assembly successful with detailed metrics")
	}
}
