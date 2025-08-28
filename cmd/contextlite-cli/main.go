package main

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// ContextLiteInstance represents a discovered ContextLite instance
type ContextLiteInstance struct {
	Port        int                    `json:"port"`
	URL         string                 `json:"url"`
	Status      string                 `json:"status"`
	ProjectName string                 `json:"project_name"`
	ProjectPath string                 `json:"project_path"`
	Registered  bool                   `json:"registered"`
	Health      map[string]interface{} `json:"health,omitempty"`
}

// ProjectRegistry represents the VS Code extension's port registry
type ProjectRegistry map[string]struct {
	ProjectName string `json:"projectName"`
	ProjectPath string `json:"projectPath"`
	Port        int    `json:"port"`
	ConfigPath  string `json:"configPath"`
	DBPath      string `json:"dbPath"`
}

// ContextLiteDiscovery handles discovery of ContextLite instances
type ContextLiteDiscovery struct {
	portRange    []int
	registryPath string
}

// NewDiscovery creates a new discovery client
func NewDiscovery() *ContextLiteDiscovery {
	homeDir, _ := os.UserHomeDir()
	registryPath := filepath.Join(homeDir, ".contextlite", "port_registry.json")
	
	return &ContextLiteDiscovery{
		portRange:    []int{8080, 8081, 8082, 8083, 8084, 8085, 8086, 8087, 8088, 8089, 8090},
		registryPath: registryPath,
	}
}

// LoadRegistry loads the port registry from VS Code extension
func (d *ContextLiteDiscovery) LoadRegistry() ProjectRegistry {
	registry := make(ProjectRegistry)
	
	if _, err := os.Stat(d.registryPath); os.IsNotExist(err) {
		return registry
	}
	
	data, err := ioutil.ReadFile(d.registryPath)
	if err != nil {
		return registry
	}
	
	json.Unmarshal(data, &registry)
	return registry
}

// IsInstanceHealthy checks if ContextLite is running on the given port
func (d *ContextLiteDiscovery) IsInstanceHealthy(port int) bool {
	client := &http.Client{Timeout: 2 * time.Second}
	resp, err := client.Get(fmt.Sprintf("http://localhost:%d/health", port))
	if err != nil {
		return false
	}
	defer resp.Body.Close()
	return resp.StatusCode == 200
}

// GetInstanceInfo gets detailed health information from a ContextLite instance
func (d *ContextLiteDiscovery) GetInstanceInfo(port int) *ContextLiteInstance {
	client := &http.Client{Timeout: 5 * time.Second}
	resp, err := client.Get(fmt.Sprintf("http://localhost:%d/health", port))
	if err != nil {
		return nil
	}
	defer resp.Body.Close()
	
	if resp.StatusCode != 200 {
		return nil
	}
	
	var health map[string]interface{}
	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return nil
	}
	
	json.Unmarshal(body, &health)
	
	return &ContextLiteInstance{
		Port:   port,
		URL:    fmt.Sprintf("http://localhost:%d", port),
		Status: "healthy",
		Health: health,
	}
}

// DiscoverInstances finds all running ContextLite instances
func (d *ContextLiteDiscovery) DiscoverInstances() []*ContextLiteInstance {
	var instances []*ContextLiteInstance
	registry := d.LoadRegistry()
	
	// Check registered instances first
	for _, project := range registry {
		if d.IsInstanceHealthy(project.Port) {
			instance := d.GetInstanceInfo(project.Port)
			if instance != nil {
				instance.Registered = true
				instance.ProjectName = project.ProjectName
				instance.ProjectPath = project.ProjectPath
				instances = append(instances, instance)
			}
		}
	}
	
	// Scan for unregistered instances
	registeredPorts := make(map[int]bool)
	for _, instance := range instances {
		registeredPorts[instance.Port] = true
	}
	
	for _, port := range d.portRange {
		if !registeredPorts[port] && d.IsInstanceHealthy(port) {
			instance := d.GetInstanceInfo(port)
			if instance != nil {
				instance.Registered = false
				instance.ProjectName = fmt.Sprintf("unregistered-%d", port)
				instance.ProjectPath = "unknown"
				instances = append(instances, instance)
			}
		}
	}
	
	return instances
}

// FindProjectInstance finds ContextLite instance for a specific project
func (d *ContextLiteDiscovery) FindProjectInstance(projectIdentifier string) *ContextLiteInstance {
	instances := d.DiscoverInstances()
	
	// Try exact project name match
	for _, instance := range instances {
		if instance.ProjectName == projectIdentifier {
			return instance
		}
	}
	
	// Try project path match
	for _, instance := range instances {
		if strings.Contains(strings.ToLower(instance.ProjectPath), strings.ToLower(projectIdentifier)) {
			return instance
		}
	}
	
	// Try partial name match
	for _, instance := range instances {
		if strings.Contains(strings.ToLower(instance.ProjectName), strings.ToLower(projectIdentifier)) {
			return instance
		}
	}
	
	return nil
}

// QueryContext queries context from a specific project's ContextLite instance
func (d *ContextLiteDiscovery) QueryContext(projectIdentifier, query string, maxResults int) map[string]interface{} {
	instance := d.FindProjectInstance(projectIdentifier)
	if instance == nil {
		instances := d.DiscoverInstances()
		var available []string
		for _, inst := range instances {
			available = append(available, inst.ProjectName)
		}
		
		return map[string]interface{}{
			"error":     fmt.Sprintf("No ContextLite instance found for project: %s", projectIdentifier),
			"available": available,
		}
	}
	
	// Prepare query payload
	payload := map[string]interface{}{
		"query":         query,
		"max_documents": maxResults,
		"use_optimization": true,
	}
	
	payloadBytes, err := json.Marshal(payload)
	if err != nil {
		return map[string]interface{}{
			"error": fmt.Sprintf("Failed to marshal query: %v", err),
		}
	}
	
	// Make HTTP request
	client := &http.Client{Timeout: 30 * time.Second}
	req, err := http.NewRequest("POST", instance.URL+"/api/v1/context/assemble", strings.NewReader(string(payloadBytes)))
	if err != nil {
		return map[string]interface{}{
			"error": fmt.Sprintf("Failed to create request: %v", err),
		}
	}
	
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("X-Workspace-ID", instance.ProjectName)
	
	resp, err := client.Do(req)
	if err != nil {
		return map[string]interface{}{
			"error": fmt.Sprintf("Failed to query project: %v", err),
		}
	}
	defer resp.Body.Close()
	
	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return map[string]interface{}{
			"error": fmt.Sprintf("Failed to read response: %v", err),
		}
	}
	
	if resp.StatusCode != 200 {
		return map[string]interface{}{
			"error": fmt.Sprintf("Query failed with status %d: %s", resp.StatusCode, string(body)),
		}
	}
	
	var result map[string]interface{}
	if err := json.Unmarshal(body, &result); err != nil {
		return map[string]interface{}{
			"error": fmt.Sprintf("Failed to parse response: %v", err),
		}
	}
	
	return map[string]interface{}{
		"success": true,
		"project": instance.ProjectName,
		"port":    instance.Port,
		"query":   query,
		"results": result,
	}
}

func main() {
	if len(os.Args) < 2 {
		printUsage()
		return
	}
	
	discovery := NewDiscovery()
	command := os.Args[1]
	
	switch command {
	case "discover":
		instances := discovery.DiscoverInstances()
		
		fmt.Println("🔍 ContextLite Instance Discovery")
		fmt.Println(strings.Repeat("=", 50))
		
		if len(instances) == 0 {
			fmt.Println("❌ No ContextLite instances found")
			fmt.Println("\nTip: Start ContextLite from VS Code or run 'contextlite' manually")
			return
		}
		
		for i, instance := range instances {
			statusIcon := "✅"
			if !instance.Registered {
				statusIcon = "⚠️"
			}
			
			fmt.Printf("\n%s Instance %d:\n", statusIcon, i+1)
			fmt.Printf("   Project: %s\n", instance.ProjectName)
			fmt.Printf("   Port: %d\n", instance.Port)
			fmt.Printf("   URL: %s\n", instance.URL)
			fmt.Printf("   Registered: %v\n", instance.Registered)
			
			// Show health info if available
			if health := instance.Health; health != nil {
				if db, ok := health["database"].(map[string]interface{}); ok {
					if docs, ok := db["documents_indexed"].(string); ok {
						fmt.Printf("   Documents: %s\n", docs)
					}
				}
				
				if workspaces, ok := health["workspaces"].(map[string]interface{}); ok {
					if total, ok := workspaces["total_workspaces"].(float64); ok {
						fmt.Printf("   Workspaces: %.0f\n", total)
					}
				}
			}
		}
		
	case "connect":
		if len(os.Args) < 3 {
			fmt.Println("❌ Project name required for connect action")
			fmt.Println("Usage: contextlite-cli connect <project-name>")
			return
		}
		
		projectName := os.Args[2]
		instance := discovery.FindProjectInstance(projectName)
		
		if instance == nil {
			fmt.Printf("❌ No ContextLite instance found for project: %s\n", projectName)
			fmt.Println("\nAvailable projects:")
			for _, inst := range discovery.DiscoverInstances() {
				fmt.Printf("   • %s\n", inst.ProjectName)
			}
			return
		}
		
		fmt.Printf("✅ Found ContextLite instance for %s\n", projectName)
		fmt.Printf("   URL: %s\n", instance.URL)
		fmt.Printf("   Port: %d\n", instance.Port)
		fmt.Printf("   Status: %s\n", instance.Status)
		
		// Test connection
		if discovery.IsInstanceHealthy(instance.Port) {
			fmt.Println("   Connection: ✅ Healthy")
		} else {
			fmt.Println("   Connection: ❌ Failed")
		}
		
	case "query":
		if len(os.Args) < 4 {
			fmt.Println("❌ Project name and query text required")
			fmt.Println("Usage: contextlite-cli query <project-name> \"<search query>\"")
			return
		}
		
		projectName := os.Args[2]
		queryText := os.Args[3]
		
		result := discovery.QueryContext(projectName, queryText, 10)
		
		if errorMsg, ok := result["error"].(string); ok {
			fmt.Printf("❌ %s\n", errorMsg)
			if available, ok := result["available"].([]string); ok {
				fmt.Println("\nAvailable projects:")
				for _, proj := range available {
					fmt.Printf("   • %s\n", proj)
				}
			}
			return
		}
		
		fmt.Printf("✅ Query results for '%s':\n", projectName)
		fmt.Printf("   Query: %s\n", result["query"])
		fmt.Printf("   Port: %.0f\n", result["port"])
		
		if results, ok := result["results"].(map[string]interface{}); ok {
			if documents, ok := results["documents"].([]interface{}); ok {
				fmt.Printf("   Found: %d documents\n", len(documents))
				
				for i, docInterface := range documents {
					if i >= 5 { // Show first 5
						break
					}
					
					if doc, ok := docInterface.(map[string]interface{}); ok {
						fmt.Printf("\n   📄 Document %d:\n", i+1)
						
						if path, ok := doc["path"].(string); ok {
							fmt.Printf("      Path: %s\n", path)
						}
						
						if score, ok := doc["score"].(float64); ok {
							fmt.Printf("      Relevance: %.3f\n", score)
						}
						
						if content, ok := doc["content"].(string); ok {
							preview := content
							if len(content) > 100 {
								preview = content[:100] + "..."
							}
							fmt.Printf("      Preview: %s\n", preview)
						}
					}
				}
			}
		}
		
	case "list-projects":
		instances := discovery.DiscoverInstances()
		
		fmt.Println("📋 Registered Projects")
		fmt.Println(strings.Repeat("=", 30))
		
		if len(instances) == 0 {
			fmt.Println("No projects found")
			return
		}
		
		for _, instance := range instances {
			status := "✅ Registered"
			if !instance.Registered {
				status = "⚠️ Discovered"
			}
			fmt.Printf("   %-20s Port %-5d %s\n", instance.ProjectName, instance.Port, status)
		}
		
	case "status":
		instances := discovery.DiscoverInstances()
		registry := discovery.LoadRegistry()
		
		fmt.Println("📊 ContextLite System Status")
		fmt.Println(strings.Repeat("=", 35))
		fmt.Printf("   Healthy Instances: %d\n", len(instances))
		fmt.Printf("   Registry Entries: %d\n", len(registry))
		fmt.Printf("   Port Range: %d-%d\n", discovery.portRange[0], discovery.portRange[len(discovery.portRange)-1])
		
		if len(instances) > 0 {
			fmt.Println("\n   Active Projects:")
			for _, instance := range instances {
				fmt.Printf("     • %s (port %d)\n", instance.ProjectName, instance.Port)
			}
		}
		
	default:
		printUsage()
	}
}

func printUsage() {
	fmt.Println("ContextLite CLI Discovery Tool")
	fmt.Println("==============================")
	fmt.Println("")
	fmt.Println("Usage:")
	fmt.Println("  contextlite-cli discover                     # Show all running instances")
	fmt.Println("  contextlite-cli connect <project>            # Get connection info for project")
	fmt.Println("  contextlite-cli query <project> \"search\"     # Query project's context")
	fmt.Println("  contextlite-cli list-projects                # List all registered projects")
	fmt.Println("  contextlite-cli status                       # Show overall status")
	fmt.Println("")
	fmt.Println("Examples:")
	fmt.Println("  contextlite-cli discover")
	fmt.Println("  contextlite-cli connect contextlite")
	fmt.Println("  contextlite-cli query contextlite \"authentication patterns\"")
}
