package main

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"net"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"
)

// ProjectPortManager handles intelligent port assignment and persistence
type ProjectPortManager struct {
	mu            sync.RWMutex
	registryPath  string
	portRegistry  map[string]*ProjectInstance
	portRange     []int
	cleanupTicker *time.Ticker
}

// ProjectInstance represents a ContextLite instance for a specific project
type ProjectInstance struct {
	ProjectName string    `json:"project_name"`
	ProjectPath string    `json:"project_path"`
	Port        int       `json:"port"`
	PID         int       `json:"pid"`
	StartTime   time.Time `json:"start_time"`
	LastSeen    time.Time `json:"last_seen"`
	ConfigPath  string    `json:"config_path"`
	DBPath      string    `json:"db_path"`
	Status      string    `json:"status"` // "running", "stopped", "unknown"
}

// NewProjectPortManager creates a new port manager
func NewProjectPortManager() *ProjectPortManager {
	homeDir, _ := os.UserHomeDir()
	registryPath := filepath.Join(homeDir, ".contextlite", "port_registry.json")
	
	manager := &ProjectPortManager{
		registryPath: registryPath,
		portRegistry: make(map[string]*ProjectInstance),
		portRange:    []int{8080, 8081, 8082, 8083, 8084, 8085, 8086, 8087, 8088, 8089, 8090},
	}
	
	// Load existing registry
	manager.loadRegistry()
	
	// Start cleanup routine
	manager.startCleanupRoutine()
	
	return manager
}

// GetOrAssignPort gets existing port for project or assigns a new one
func (pm *ProjectPortManager) GetOrAssignPort(projectPath string) (*ProjectInstance, error) {
	pm.mu.Lock()
	defer pm.mu.Unlock()
	
	projectName := filepath.Base(projectPath)
	normalizedPath := pm.normalizePath(projectPath)
	
	// Check if project already has a port assigned
	if instance, exists := pm.portRegistry[normalizedPath]; exists {
		// Verify the port is still available and process is running
		if pm.isPortHealthy(instance.Port) {
			instance.LastSeen = time.Now()
			instance.Status = "running"
			pm.saveRegistry()
			return instance, nil
		}
		
		// Port is dead, remove the old instance
		delete(pm.portRegistry, normalizedPath)
	}
	
	// Assign new port
	port, err := pm.findAvailablePort()
	if err != nil {
		return nil, fmt.Errorf("no available ports: %w", err)
	}
	
	instance := &ProjectInstance{
		ProjectName: projectName,
		ProjectPath: normalizedPath,
		Port:        port,
		StartTime:   time.Now(),
		LastSeen:    time.Now(),
		ConfigPath:  filepath.Join(projectPath, ".contextlite", "config.yaml"),
		DBPath:      filepath.Join(projectPath, ".contextlite", "contextlite.db"),
		Status:      "assigned",
	}
	
	pm.portRegistry[normalizedPath] = instance
	pm.saveRegistry()
	
	// Create project-specific configuration
	if err := pm.createProjectConfig(instance); err != nil {
		return nil, fmt.Errorf("failed to create project config: %w", err)
	}
	
	return instance, nil
}

// findAvailablePort finds the next available port in the range
func (pm *ProjectPortManager) findAvailablePort() (int, error) {
	usedPorts := make(map[int]bool)
	
	// Mark ports used by registered instances
	for _, instance := range pm.portRegistry {
		if instance.Status == "running" {
			usedPorts[instance.Port] = true
		}
	}
	
	// Find first available port
	for _, port := range pm.portRange {
		if !usedPorts[port] && pm.isPortAvailable(port) {
			return port, nil
		}
	}
	
	return 0, fmt.Errorf("no available ports in range %v", pm.portRange)
}

// isPortAvailable checks if a port is available for binding
func (pm *ProjectPortManager) isPortAvailable(port int) bool {
	ln, err := net.Listen("tcp", fmt.Sprintf(":%d", port))
	if err != nil {
		return false
	}
	ln.Close()
	return true
}

// isPortHealthy checks if ContextLite is responding on the port
func (pm *ProjectPortManager) isPortHealthy(port int) bool {
	conn, err := net.DialTimeout("tcp", fmt.Sprintf("localhost:%d", port), 2*time.Second)
	if err != nil {
		return false
	}
	conn.Close()
	
	// TODO: Add HTTP health check here
	// Could do: GET http://localhost:port/health
	return true
}

// createProjectConfig creates a project-specific ContextLite configuration
func (pm *ProjectPortManager) createProjectConfig(instance *ProjectInstance) error {
	configDir := filepath.Dir(instance.ConfigPath)
	if err := os.MkdirAll(configDir, 0755); err != nil {
		return err
	}
	
	config := fmt.Sprintf(`# Auto-generated ContextLite configuration for %s
# Generated at: %s
# Port: %d

server:
  port: %d
  host: "127.0.0.1"
  cors_enabled: true

storage:
  database_path: "%s"
  cache_size_mb: 256

cluster:
  enabled: true
  node_id: "contextlite-%s-%d"
  
  affinity:
    workspace_routing: true
    sticky_sessions: true
    rules:
      "%s":
        resource_tier: "high"
        max_memory_mb: 512
        priority: 8

# Project isolation settings
privacy:
  project_isolation: true
  exclude_patterns:
    - "*.env*"
    - "*.key" 
    - "*.pem"
    - "secrets/*"
    - "node_modules/*"
    - ".git/*"
    - "vendor/*"
    - "__pycache__/*"
    - "*.pyc"
    - ".DS_Store"
    - "Thumbs.db"

# Performance optimization
performance:
  cache_embeddings: true
  enable_smart_indexing: true
  update_frequency: "on_save"
  precompute_similar_files: true

# SMT solver settings optimized for development
smt:
  solver_timeout_ms: 1000
  max_candidates: 100
  objective_style: "code_context"
  enable_code_structure_analysis: true

# Weights optimized for code understanding
weights:
  relevance: 0.30
  recency: 0.20
  entanglement: 0.20
  specificity: 0.15
  authority: 0.10
  prior: 0.05

# Logging
logging:
  level: "info"
  file: "%s"

# Port management metadata
port_management:
  assigned_by: "contextlite-port-manager"
  assignment_time: "%s"
  project_path: "%s"
  auto_cleanup: true
`,
		instance.ProjectName,
		instance.StartTime.Format(time.RFC3339),
		instance.Port,
		instance.Port,
		instance.DBPath,
		instance.ProjectName,
		instance.Port,
		instance.ProjectName,
		filepath.Join(configDir, "contextlite.log"),
		instance.StartTime.Format(time.RFC3339),
		instance.ProjectPath,
	)
	
	return ioutil.WriteFile(instance.ConfigPath, []byte(config), 0644)
}

// ListActiveInstances returns all currently active ContextLite instances
func (pm *ProjectPortManager) ListActiveInstances() []*ProjectInstance {
	pm.mu.RLock()
	defer pm.mu.RUnlock()
	
	var active []*ProjectInstance
	for _, instance := range pm.portRegistry {
		if pm.isPortHealthy(instance.Port) {
			instance.Status = "running"
			active = append(active, instance)
		}
	}
	
	return active
}

// CleanupDeadInstances removes instances that are no longer running
func (pm *ProjectPortManager) CleanupDeadInstances() int {
	pm.mu.Lock()
	defer pm.mu.Unlock()
	
	cleaned := 0
	for path, instance := range pm.portRegistry {
		if !pm.isPortHealthy(instance.Port) {
			// Instance is dead, remove it
			delete(pm.portRegistry, path)
			cleaned++
		}
	}
	
	if cleaned > 0 {
		pm.saveRegistry()
	}
	
	return cleaned
}

// GetInstanceByProject finds instance by project path
func (pm *ProjectPortManager) GetInstanceByProject(projectPath string) *ProjectInstance {
	pm.mu.RLock()
	defer pm.mu.RUnlock()
	
	normalizedPath := pm.normalizePath(projectPath)
	return pm.portRegistry[normalizedPath]
}

// GetInstanceByPort finds instance by port number
func (pm *ProjectPortManager) GetInstanceByPort(port int) *ProjectInstance {
	pm.mu.RLock()
	defer pm.mu.RUnlock()
	
	for _, instance := range pm.portRegistry {
		if instance.Port == port {
			return instance
		}
	}
	return nil
}

// normalizePath normalizes file paths for consistent comparison
func (pm *ProjectPortManager) normalizePath(path string) string {
	abs, err := filepath.Abs(path)
	if err != nil {
		return path
	}
	return strings.ToLower(filepath.Clean(abs))
}

// loadRegistry loads the port registry from disk
func (pm *ProjectPortManager) loadRegistry() error {
	if _, err := os.Stat(pm.registryPath); os.IsNotExist(err) {
		return nil // No registry file yet
	}
	
	data, err := ioutil.ReadFile(pm.registryPath)
	if err != nil {
		return err
	}
	
	var registry map[string]*ProjectInstance
	if err := json.Unmarshal(data, &registry); err != nil {
		return err
	}
	
	pm.portRegistry = registry
	return nil
}

// saveRegistry saves the port registry to disk
func (pm *ProjectPortManager) saveRegistry() error {
	// Ensure directory exists
	dir := filepath.Dir(pm.registryPath)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return err
	}
	
	data, err := json.MarshalIndent(pm.portRegistry, "", "  ")
	if err != nil {
		return err
	}
	
	return ioutil.WriteFile(pm.registryPath, data, 0644)
}

// startCleanupRoutine starts a background routine to cleanup dead instances
func (pm *ProjectPortManager) startCleanupRoutine() {
	pm.cleanupTicker = time.NewTicker(30 * time.Second)
	
	go func() {
		for range pm.cleanupTicker.C {
			pm.CleanupDeadInstances()
		}
	}()
}

// Stop stops the port manager and cleanup routine
func (pm *ProjectPortManager) Stop() {
	if pm.cleanupTicker != nil {
		pm.cleanupTicker.Stop()
	}
}

// CLI commands for port management
func main() {
	if len(os.Args) < 2 {
		printUsage()
		return
	}
	
	manager := NewProjectPortManager()
	defer manager.Stop()
	
	command := os.Args[1]
	
	switch command {
	case "assign":
		if len(os.Args) < 3 {
			fmt.Println("Usage: contextlite-port assign <project-path>")
			return
		}
		projectPath := os.Args[2]
		instance, err := manager.GetOrAssignPort(projectPath)
		if err != nil {
			fmt.Printf("Error: %v\n", err)
			os.Exit(1)
		}
		fmt.Printf("Assigned port %d to project %s\n", instance.Port, instance.ProjectName)
		fmt.Printf("Config: %s\n", instance.ConfigPath)
		
	case "list":
		instances := manager.ListActiveInstances()
		fmt.Printf("Active ContextLite instances:\n")
		fmt.Printf("%-20s %-6s %-30s %-20s\n", "Project", "Port", "Path", "Status")
		fmt.Printf("%s\n", strings.Repeat("-", 80))
		for _, instance := range instances {
			fmt.Printf("%-20s %-6d %-30s %-20s\n", 
				instance.ProjectName, 
				instance.Port, 
				truncatePath(instance.ProjectPath, 30),
				instance.Status)
		}
		
	case "cleanup":
		cleaned := manager.CleanupDeadInstances()
		fmt.Printf("Cleaned up %d dead instances\n", cleaned)
		
	case "status":
		if len(os.Args) < 3 {
			fmt.Println("Usage: contextlite-port status <project-path>")
			return
		}
		projectPath := os.Args[2]
		instance := manager.GetInstanceByProject(projectPath)
		if instance == nil {
			fmt.Println("No instance found for project")
			return
		}
		
		healthy := manager.isPortHealthy(instance.Port)
		status := "stopped"
		if healthy {
			status = "running"
		}
		
		fmt.Printf("Project: %s\n", instance.ProjectName)
		fmt.Printf("Port: %d\n", instance.Port)
		fmt.Printf("Status: %s\n", status)
		fmt.Printf("Config: %s\n", instance.ConfigPath)
		fmt.Printf("Database: %s\n", instance.DBPath)
		fmt.Printf("Started: %s\n", instance.StartTime.Format(time.RFC3339))
		
	case "start":
		if len(os.Args) < 3 {
			fmt.Println("Usage: contextlite-port start <project-path>")
			return
		}
		projectPath := os.Args[2]
		instance, err := manager.GetOrAssignPort(projectPath)
		if err != nil {
			fmt.Printf("Error: %v\n", err)
			os.Exit(1)
		}
		
		// Start ContextLite with the assigned configuration
		fmt.Printf("Starting ContextLite for %s on port %d...\n", instance.ProjectName, instance.Port)
		fmt.Printf("Command: contextlite --config %s\n", instance.ConfigPath)
		fmt.Printf("URL: http://localhost:%d\n", instance.Port)
		
	default:
		printUsage()
	}
}

func printUsage() {
	fmt.Println("ContextLite Port Manager - Intelligent port assignment and management")
	fmt.Println("")
	fmt.Println("Usage:")
	fmt.Println("  contextlite-port assign <project-path>   # Assign port to project")
	fmt.Println("  contextlite-port start <project-path>    # Start ContextLite for project")
	fmt.Println("  contextlite-port list                    # List active instances")
	fmt.Println("  contextlite-port status <project-path>   # Show status of project instance")
	fmt.Println("  contextlite-port cleanup                 # Cleanup dead instances")
	fmt.Println("")
	fmt.Println("Examples:")
	fmt.Println("  contextlite-port assign /path/to/my-project")
	fmt.Println("  contextlite-port start /path/to/my-project")
	fmt.Println("  contextlite-port list")
}

func truncatePath(path string, maxLen int) string {
	if len(path) <= maxLen {
		return path
	}
	return "..." + path[len(path)-maxLen+3:]
}
