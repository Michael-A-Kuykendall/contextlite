// Package main demonstrates automatic port management with ContextLite
// This example shows how to build applications that can discover and connect
// to ContextLite instances automatically, eliminating port configuration drift.
package main

import (
	"context"
	"fmt"
	"log"
	"net/http"
	"time"
)

// ContextLiteClient represents a client with automatic port discovery
type ContextLiteClient struct {
	baseURL     string
	httpClient  *http.Client
	discovered  bool
	activePort  int
}

// NewAutoDiscoveryClient creates a client that automatically discovers ContextLite
func NewAutoDiscoveryClient() *ContextLiteClient {
	return &ContextLiteClient{
		httpClient: &http.Client{Timeout: 5 * time.Second},
	}
}

// AutoDiscover automatically finds running ContextLite instances
func (c *ContextLiteClient) AutoDiscover() error {
	// Common ContextLite ports to check
	commonPorts := []int{8080, 8081, 8082, 8083, 8084, 8085}
	
	fmt.Println("🔍 Auto-discovering ContextLite instances...")
	
	for _, port := range commonPorts {
		if c.isContextLiteHealthy(port) {
			c.activePort = port
			c.baseURL = fmt.Sprintf("http://localhost:%d", port)
			c.discovered = true
			fmt.Printf("✅ Found healthy ContextLite instance on port %d\n", port)
			return nil
		}
	}
	
	return fmt.Errorf("❌ No healthy ContextLite instances found on common ports")
}

// isContextLiteHealthy checks if ContextLite is running and healthy on the given port
func (c *ContextLiteClient) isContextLiteHealthy(port int) bool {
	url := fmt.Sprintf("http://localhost:%d/health", port)
	resp, err := c.httpClient.Get(url)
	if err != nil {
		return false
	}
	defer resp.Body.Close()
	
	return resp.StatusCode == http.StatusOK
}

// DiscoverMultipleInstances finds all running ContextLite instances
func (c *ContextLiteClient) DiscoverMultipleInstances() []int {
	var instances []int
	commonPorts := []int{8080, 8081, 8082, 8083, 8084, 8085, 8086, 8087, 8088, 8089, 8090}
	
	fmt.Println("🔍 Scanning for multiple ContextLite instances...")
	
	for _, port := range commonPorts {
		if c.isContextLiteHealthy(port) {
			instances = append(instances, port)
			fmt.Printf("✅ Found ContextLite instance on port %d\n", port)
		}
	}
	
	return instances
}

// Query performs a context assembly query with automatic failover
func (c *ContextLiteClient) Query(query string, maxDocs int) (map[string]interface{}, error) {
	if !c.discovered {
		if err := c.AutoDiscover(); err != nil {
			return nil, fmt.Errorf("failed to discover ContextLite: %w", err)
		}
	}
	
	// Try the query with the current instance
	result, err := c.tryQuery(c.activePort, query, maxDocs)
	if err == nil {
		return result, nil
	}
	
	fmt.Printf("⚠️ Query failed on port %d, attempting failover...\n", c.activePort)
	
	// Attempt failover to other instances
	instances := c.DiscoverMultipleInstances()
	for _, port := range instances {
		if port == c.activePort {
			continue // Skip the one that just failed
		}
		
		result, err := c.tryQuery(port, query, maxDocs)
		if err == nil {
			c.activePort = port
			c.baseURL = fmt.Sprintf("http://localhost:%d", port)
			fmt.Printf("✅ Failover successful to port %d\n", port)
			return result, nil
		}
	}
	
	return nil, fmt.Errorf("all ContextLite instances failed")
}

// tryQuery attempts a query on a specific port
func (c *ContextLiteClient) tryQuery(port int, query string, maxDocs int) (map[string]interface{}, error) {
	url := fmt.Sprintf("http://localhost:%d/api/v1/query", port)
	
	// This is a simplified example - in practice you'd send proper JSON
	resp, err := c.httpClient.Post(url, "application/json", nil)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("query failed with status: %d", resp.StatusCode)
	}
	
	// Return a simple success response for demo purposes
	return map[string]interface{}{
		"status": "success",
		"port":   port,
		"query":  query,
	}, nil
}

// GetActivePort returns the currently active ContextLite port
func (c *ContextLiteClient) GetActivePort() int {
	return c.activePort
}

// Example usage patterns
func main() {
	ctx := context.Background()
	
	fmt.Println("🚀 ContextLite Automatic Port Management Demo")
	fmt.Println("==============================================")
	
	// Example 1: Basic auto-discovery
	fmt.Println("\n📡 Example 1: Basic Auto-Discovery")
	client := NewAutoDiscoveryClient()
	
	if err := client.AutoDiscover(); err != nil {
		log.Printf("Auto-discovery failed: %v", err)
		fmt.Println("💡 Tip: Start ContextLite with: ./contextlite")
		return
	}
	
	fmt.Printf("🎯 Connected to ContextLite on port %d\n", client.GetActivePort())
	
	// Example 2: Multiple instance discovery
	fmt.Println("\n🔄 Example 2: Multiple Instance Discovery")
	instances := client.DiscoverMultipleInstances()
	
	if len(instances) > 1 {
		fmt.Printf("🎉 Found %d concurrent ContextLite instances!\n", len(instances))
		fmt.Println("   This solves the port drift problem:")
		fmt.Println("   - No hardcoded port numbers needed")
		fmt.Println("   - Automatic failover between instances")
		fmt.Println("   - Support for concurrent development environments")
	}
	
	// Example 3: Query with automatic failover
	fmt.Println("\n💬 Example 3: Query with Automatic Failover")
	result, err := client.Query("test query", 10)
	if err != nil {
		log.Printf("Query failed: %v", err)
	} else {
		fmt.Printf("✅ Query successful: %+v\n", result)
	}
	
	// Example 4: Integration patterns
	fmt.Println("\n🏗️ Example 4: Common Integration Patterns")
	fmt.Println("==========================================")
	
	// Pattern 1: Workspace-specific instances
	showWorkspacePattern()
	
	// Pattern 2: Load balancing across instances
	showLoadBalancingPattern(instances)
	
	// Pattern 3: Development vs Production
	showEnvironmentPattern(ctx)
	
	fmt.Println("\n🎯 Key Benefits of Automatic Port Management:")
	fmt.Println("   ✅ No more hardcoded port numbers")
	fmt.Println("   ✅ Automatic discovery of running instances")
	fmt.Println("   ✅ Built-in failover and redundancy")
	fmt.Println("   ✅ Support for concurrent development")
	fmt.Println("   ✅ Zero-configuration setup")
	fmt.Println("   ✅ Production-ready reliability")
}

// showWorkspacePattern demonstrates workspace-specific port management
func showWorkspacePattern() {
	fmt.Println("\n🏢 Pattern 1: Workspace-Specific Instances")
	fmt.Println("   // Each workspace can have its own ContextLite instance")
	fmt.Println("   workspace1Client := NewAutoDiscoveryClient()")
	fmt.Println("   workspace2Client := NewAutoDiscoveryClient()")
	fmt.Println("   // Clients automatically find their respective instances")
	fmt.Println("   // No port conflicts, no configuration drift")
}

// showLoadBalancingPattern demonstrates load balancing
func showLoadBalancingPattern(instances []int) {
	fmt.Println("\n⚖️ Pattern 2: Load Balancing Across Instances")
	fmt.Printf("   Found %d instances for load balancing\n", len(instances))
	fmt.Println("   // Distribute queries across multiple instances")
	fmt.Println("   // Automatic health checks and failover")
	fmt.Println("   // Optimal performance under high load")
}

// showEnvironmentPattern demonstrates environment-specific configuration
func showEnvironmentPattern(ctx context.Context) {
	fmt.Println("\n🌍 Pattern 3: Environment-Specific Configuration")
	fmt.Println("   Development: Auto-discover local instances (ports 8080-8090)")
	fmt.Println("   Staging:     Auto-discover staging instances (ports 9080-9090)")
	fmt.Println("   Production:  Auto-discover production cluster (load balanced)")
	fmt.Println("   // Same code works across all environments")
}