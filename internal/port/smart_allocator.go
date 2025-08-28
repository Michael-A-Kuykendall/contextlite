package port

import (
	"encoding/json"
	"fmt"
	"log"
	"net"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"syscall"
	"contextlite/pkg/config"
)

// PortAllocationResult represents the result from port registry
type PortAllocationResult struct {
	Port        int    `json:"port"`
	ProcessID   int    `json:"process_id"`
	ProjectName string `json:"project_name"`
	ProjectPath string `json:"project_path"`
	Status      string `json:"status"`
}

// SmartPortAllocator integrates with the system-wide port registry
type SmartPortAllocator struct {
	registryPath string
}

// NewSmartPortAllocator creates a new allocator that uses the system registry
func NewSmartPortAllocator() *SmartPortAllocator {
	// Find the port-registry binary
	execPath, err := os.Executable()
	if err != nil {
		log.Printf("Warning: Could not find executable path: %v", err)
		return &SmartPortAllocator{registryPath: "port-registry"}
	}
	
	// Look for port-registry in the same directory as contextlite
	dir := filepath.Dir(execPath)
	registryPath := filepath.Join(dir, "port-registry")
	
	// On Windows, add .exe extension
	if filepath.Ext(execPath) == ".exe" {
		registryPath += ".exe"
	}
	
	// Fallback to PATH if not found
	if _, err := os.Stat(registryPath); os.IsNotExist(err) {
		registryPath = "port-registry"
	}
	
	return &SmartPortAllocator{registryPath: registryPath}
}

// AllocatePortForProject allocates a port using the system registry
func (spa *SmartPortAllocator) AllocatePortForProject(projectName, projectPath string) (int, error) {
	// Call the port registry
	cmd := exec.Command(spa.registryPath, "allocate", projectName, projectPath)
	output, err := cmd.Output()
	if err != nil {
		return 0, fmt.Errorf("port registry failed: %v", err)
	}
	
	// Parse JSON response
	var result PortAllocationResult
	if err := json.Unmarshal(output, &result); err != nil {
		return 0, fmt.Errorf("failed to parse port registry response: %v", err)
	}
	
	log.Printf("🎯 Port Registry: Allocated port %d for project '%s'", result.Port, projectName)
	return result.Port, nil
}

// ReleasePort releases a port allocation
func (spa *SmartPortAllocator) ReleasePort(port int) error {
	cmd := exec.Command(spa.registryPath, "release", fmt.Sprintf("%d", port))
	output, err := cmd.Output()
	if err != nil {
		log.Printf("Warning: Failed to release port %d: %v", port, err)
		return err
	}
	
	log.Printf("🔓 Port Registry: Released port %d", port)
	log.Printf("Registry output: %s", string(output))
	return nil
}

// GetProjectPort gets or allocates a port for the current project
func GetProjectPort(cfg *config.Config) (int, error) {
	// If port is explicitly configured, use it
	if cfg.Server.Port != 0 {
		return cfg.Server.Port, nil
	}
	
	// Determine project name and path
	projectPath, err := os.Getwd()
	if err != nil {
		return 0, fmt.Errorf("failed to get current directory: %v", err)
	}
	
	projectName := filepath.Base(projectPath)
	
	// Use smart port allocator
	allocator := NewSmartPortAllocator()
	port, err := allocator.AllocatePortForProject(projectName, projectPath)
	if err != nil {
		// Fallback to simple port finding if registry fails
		log.Printf("Warning: Port registry failed, falling back to simple allocation: %v", err)
		return findSimpleAvailablePort()
	}
	
	// Update config with allocated port
	cfg.Server.Port = port
	
	return port, nil
}

// findSimpleAvailablePort is a fallback when registry is not available
func findSimpleAvailablePort() (int, error) {
	// Try ports in the 8080-8200 range
	for port := 8080; port <= 8200; port++ {
		if isPortAvailable(port) {
			return port, nil
		}
	}
	return 0, fmt.Errorf("no available ports found in range 8080-8200")
}

// isPortAvailable checks if a port is available (simple version)
func isPortAvailable(port int) bool {
	addr := fmt.Sprintf(":%d", port)
	l, err := net.Listen("tcp", addr)
	if err != nil {
		return false
	}
	l.Close()
	return true
}

// SetupGracefulPortRelease sets up automatic port release on exit
func SetupGracefulPortRelease(port int) {
	// Set up signal handlers for graceful shutdown
	go func() {
		c := make(chan os.Signal, 1)
		signal.Notify(c, os.Interrupt, syscall.SIGTERM)
		
		<-c
		log.Println("🛑 Received shutdown signal, releasing port...")
		
		allocator := NewSmartPortAllocator()
		allocator.ReleasePort(port)
		
		os.Exit(0)
	}()
}
