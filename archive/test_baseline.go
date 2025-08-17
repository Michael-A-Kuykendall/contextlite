package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
)

func main() {
	// Create a baseline comparison request
	requestBody := map[string]interface{}{
		"query":         "security authentication patterns",
		"max_documents": 3,
	}

	jsonData, err := json.Marshal(requestBody)
	if err != nil {
		fmt.Printf("Error marshaling request: %v\n", err)
		os.Exit(1)
	}

	// Make the API call
	resp, err := http.Post("http://127.0.0.1:8081/api/v1/context/baseline", 
		"application/json", 
		bytes.NewBuffer(jsonData))
	if err != nil {
		fmt.Printf("Error making request: %v\n", err)
		os.Exit(1)
	}
	defer resp.Body.Close()

	// Check for auth error
	if resp.StatusCode == 401 {
		fmt.Println("Authentication required. Adding auth token...")
		
		// Retry with auth header
		req, err := http.NewRequest("POST", "http://127.0.0.1:8081/api/v1/context/baseline", 
			bytes.NewBuffer(jsonData))
		if err != nil {
			fmt.Printf("Error creating request: %v\n", err)
			os.Exit(1)
		}
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer contextlite-dev-token-2025")
		
		client := &http.Client{}
		resp, err = client.Do(req)
		if err != nil {
			fmt.Printf("Error making authenticated request: %v\n", err)
			os.Exit(1)
		}
		defer resp.Body.Close()
	}

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		fmt.Printf("Error reading response: %v\n", err)
		os.Exit(1)
	}

	if resp.StatusCode != 200 {
		fmt.Printf("HTTP Error %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	var result map[string]interface{}
	if err := json.Unmarshal(body, &result); err != nil {
		fmt.Printf("Error parsing JSON: %v\n", err)
		os.Exit(1)
	}

	prettyJSON, err := json.MarshalIndent(result, "", "  ")
	if err != nil {
		fmt.Printf("Error formatting JSON: %v\n", err)
		os.Exit(1)
	}

	fmt.Println("=== Baseline Comparison Results ===")
	fmt.Println(string(prettyJSON))
}
