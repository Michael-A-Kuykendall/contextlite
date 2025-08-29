package port

import (
	"encoding/json"
	"fmt"
	"log"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"contextlite/pkg/config"
)

// LightweightPortManager - Event-driven, no background processes
type LightweightPortManager struct {
	registryPath string
}

// NewLightweightPortManager creates a manager with zero background overhead
func NewLightweightPortManager() *LightweightPortManager {
	// Find the port-registry binary
	execPath, err := os.Executable()
	if err != nil {
		log.Printf("Warning: Could not find executable path: %v", err)
		return &LightweightPortManager{registryPath: "port-registry"}
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
	
	return &LightweightPortManager{registryPath: registryPath}
}

// GetProjectPort - Event-driven allocation with cleanup-on-demand
func (lpm *LightweightPortManager) GetProjectPort(cfg *config.Config) (int, error) {
	// If port is explicitly configured, use it (no registry needed)
	if cfg.Server.Port != 0 {
		return cfg.Server.Port, nil
	}
	
	// Determine project name and path
	projectPath, err := os.Getwd()
	if err != nil {
		return 0, fmt.Errorf("failed to get current directory: %v", err)
	}
	
	projectName := filepath.Base(projectPath)
	
	// Cleanup-on-demand: clean stale entries before allocation
	// This is much more efficient than background polling
	lpm.cleanupOnDemand()
	
	// Allocate port
	port, err := lpm.allocatePort(projectName, projectPath)
	if err != nil {
		// Fallback to simple port finding if registry fails
		log.Printf("Warning: Port registry failed, falling back to simple allocation: %v", err)
		return lpm.findSimpleAvailablePort()
	}
	
	log.Printf("🎯 Port allocated: %d (project: %s)", port, projectName)
	return port, nil
}

// cleanupOnDemand - Only cleanup when actually needed (event-driven)
func (lpm *LightweightPortManager) cleanupOnDemand() {
	// Run cleanup only when someone is requesting a port
	// This is how Docker and Kubernetes do it - event-driven, not time-based
	cmd := exec.Command(lpm.registryPath, "cleanup")
	output, err := cmd.Output()
	if err != nil {
		// Don't fail if cleanup fails, just log
		log.Printf("Debug: Port registry cleanup had issues (non-fatal): %v", err)
		return
	}
	
	// Parse cleanup results quietly
	var result map[string]interface{}
	if err := json.Unmarshal(output, &result); err == nil {
		if cleaned, ok := result["cleaned_entries"].(float64); ok && cleaned > 0 {
			log.Printf("🧹 Cleaned %0.f stale port allocations", cleaned)
		}
	}
}

// allocatePort - Direct allocation without background overhead
func (lpm *LightweightPortManager) allocatePort(projectName, projectPath string) (int, error) {
	cmd := exec.Command(lpm.registryPath, "allocate", projectName, projectPath)
	output, err := cmd.Output()
	if err != nil {
		return 0, fmt.Errorf("port registry allocation failed: %v", err)
	}
	
	// Parse JSON response
	var result map[string]interface{}
	if err := json.Unmarshal(output, &result); err != nil {
		return 0, fmt.Errorf("failed to parse port registry response: %v", err)
	}
	
	if port, ok := result["port"].(float64); ok {
		return int(port), nil
	}
	
	return 0, fmt.Errorf("no port returned from registry")
}

// ReleasePort - Event-driven cleanup (only when actually stopping)
func (lpm *LightweightPortManager) ReleasePort(port int) error {
	cmd := exec.Command(lpm.registryPath, "release", fmt.Sprintf("%d", port))
	_, err := cmd.Output()
	if err != nil {
		log.Printf("Warning: Failed to release port %d: %v", port, err)
		return err
	}
	
	log.Printf("🔓 Port %d released", port)
	return nil
}

// findSimpleAvailablePort - Lightweight fallback
func (lpm *LightweightPortManager) findSimpleAvailablePort() (int, error) {
	// Try ports in a reasonable range - no complex scanning
	for port := 8080; port <= 8099; port++ {
		if lpm.isPortAvailable(port) {
			log.Printf("🎯 Fallback port allocated: %d", port)
			return port, nil
		}
	}
	return 0, fmt.Errorf("no available ports found in range 8080-8099")
}

// isPortAvailable - Quick check without overhead
func (lpm *LightweightPortManager) isPortAvailable(port int) bool {
	// This is very fast - just try to bind
	addr := fmt.Sprintf(":%d", port)
	l, err := net.Listen("tcp", addr)
	if err != nil {
		return false
	}
	l.Close()
	return true
}

// GetInvisiblePort - The main entry point for invisible port management
func GetInvisiblePort(cfg *config.Config) (int, error) {
	manager := NewLightweightPortManager()
	return manager.GetProjectPort(cfg)
}

