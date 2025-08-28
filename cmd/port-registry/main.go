package main

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"net"
	"os"
	"os/user"
	"path/filepath"
	"sync"
	"syscall"
	"time"
	"os/exec"
	"strconv"
	"runtime"
)

// PortRegistryEntry represents a single port allocation
type PortRegistryEntry struct {
	Port         int       `json:"port"`
	ProjectName  string    `json:"project_name"`
	ProjectPath  string    `json:"project_path"`
	ProcessID    int       `json:"process_id"`
	AllocatedAt  time.Time `json:"allocated_at"`
	LastSeen     time.Time `json:"last_seen"`
	Status       string    `json:"status"` // "active", "stale", "dead"
	ConfigPath   string    `json:"config_path,omitempty"`
	DatabasePath string    `json:"database_path,omitempty"`
}

// PortRegistry manages system-wide port allocations for ContextLite
type PortRegistry struct {
	registryPath string
	lockPath     string
	mutex        sync.RWMutex
	entries      map[int]*PortRegistryEntry
}

// NewPortRegistry creates or loads the system-wide port registry
func NewPortRegistry() (*PortRegistry, error) {
	// Get user-specific registry path (cross-platform)
	registryDir, err := getRegistryDirectory()
	if err != nil {
		return nil, fmt.Errorf("failed to get registry directory: %v", err)
	}
	
	// Ensure directory exists
	if err := os.MkdirAll(registryDir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create registry directory: %v", err)
	}
	
	registryPath := filepath.Join(registryDir, "port_registry.json")
	lockPath := filepath.Join(registryDir, "port_registry.lock")
	
	pr := &PortRegistry{
		registryPath: registryPath,
		lockPath:     lockPath,
		entries:      make(map[int]*PortRegistryEntry),
	}
	
	// Load existing registry
	if err := pr.load(); err != nil {
		return nil, fmt.Errorf("failed to load registry: %v", err)
	}
	
	// Clean up stale entries
	pr.cleanup()
	
	return pr, nil
}

// getRegistryDirectory returns the appropriate directory for the registry
func getRegistryDirectory() (string, error) {
	currentUser, err := user.Current()
	if err != nil {
		return "", err
	}
	
	var baseDir string
	
	switch runtime.GOOS {
	case "windows":
		// Windows: Use APPDATA
		baseDir = os.Getenv("APPDATA")
		if baseDir == "" {
			baseDir = filepath.Join(currentUser.HomeDir, "AppData", "Roaming")
		}
		return filepath.Join(baseDir, "ContextLite"), nil
		
	case "darwin":
		// macOS: Use ~/Library/Application Support
		return filepath.Join(currentUser.HomeDir, "Library", "Application Support", "ContextLite"), nil
		
	default:
		// Linux/Unix: Use XDG_DATA_HOME or ~/.local/share
		dataHome := os.Getenv("XDG_DATA_HOME")
		if dataHome == "" {
			dataHome = filepath.Join(currentUser.HomeDir, ".local", "share")
		}
		return filepath.Join(dataHome, "contextlite"), nil
	}
}

// AllocatePort finds and reserves an available port for a project
func (pr *PortRegistry) AllocatePort(projectName, projectPath string) (*PortRegistryEntry, error) {
	pr.mutex.Lock()
	defer pr.mutex.Unlock()
	
	// Check if project already has a port allocated
	normalizedPath := filepath.Clean(projectPath)
	for _, entry := range pr.entries {
		if entry.ProjectPath == normalizedPath && pr.isProcessAlive(entry.ProcessID) {
			// Update last seen and return existing allocation
			entry.LastSeen = time.Now()
			entry.Status = "active"
			pr.save()
			return entry, nil
		}
	}
	
	// Find available port using our dynamic algorithm
	port, err := pr.findAvailablePort()
	if err != nil {
		return nil, err
	}
	
	// Create new entry
	entry := &PortRegistryEntry{
		Port:        port,
		ProjectName: projectName,
		ProjectPath: normalizedPath,
		ProcessID:   os.Getpid(),
		AllocatedAt: time.Now(),
		LastSeen:    time.Now(),
		Status:      "active",
	}
	
	// Reserve the port
	pr.entries[port] = entry
	
	// Save registry
	if err := pr.save(); err != nil {
		delete(pr.entries, port)
		return nil, fmt.Errorf("failed to save registry: %v", err)
	}
	
	fmt.Printf("✅ Allocated port %d to project '%s' (PID: %d)\n", port, projectName, entry.ProcessID)
	return entry, nil
}

// findAvailablePort uses intelligent algorithm to find free ports
func (pr *PortRegistry) findAvailablePort() (int, error) {
	// Define safe port ranges (avoiding common services)
	ranges := []struct {
		start, end int
		priority   int
	}{
		{8000, 8999, 1},   // Primary development range
		{9000, 9999, 2},   // Secondary range  
		{10000, 19999, 3}, // User application range
		{20000, 29999, 4}, // Extended range
	}
	
	// Excluded ports (common services)
	excluded := map[int]bool{
		8080: true, 8443: true, 8888: true, 9090: true,
		3000: true, 3001: true, 4200: true, 5000: true,
		5432: true, 6379: true, 27017: true,
	}
	
	// Try each range in priority order
	for _, portRange := range ranges {
		for attempt := 0; attempt < 50; attempt++ {
			// Pick random port in range
			port := portRange.start + (time.Now().Nanosecond() % (portRange.end - portRange.start + 1))
			
			// Skip excluded ports
			if excluded[port] {
				continue
			}
			
			// Skip already allocated ports
			if _, exists := pr.entries[port]; exists {
				continue
			}
			
			// Test if port is actually available
			if pr.isPortAvailable(port) {
				return port, nil
			}
		}
	}
	
	return 0, fmt.Errorf("no available ports found after scanning all ranges")
}

// isPortAvailable tests if a port is actually bindable
func (pr *PortRegistry) isPortAvailable(port int) bool {
	listener, err := net.Listen("tcp", fmt.Sprintf(":%d", port))
	if err != nil {
		return false
	}
	listener.Close()
	return true
}

// isProcessAlive checks if a process is still running
func (pr *PortRegistry) isProcessAlive(pid int) bool {
	if pid <= 0 {
		return false
	}
	
	// Cross-platform process existence check
	switch runtime.GOOS {
	case "windows":
		// Use tasklist on Windows
		cmd := exec.Command("tasklist", "/FI", fmt.Sprintf("PID eq %d", pid), "/FO", "CSV")
		output, err := cmd.Output()
		if err != nil {
			return false
		}
		return len(output) > 100 // tasklist returns header even if no process found
		
	default:
		// Use kill -0 on Unix-like systems (doesn't actually send signal)
		process, err := os.FindProcess(pid)
		if err != nil {
			return false
		}
		
		err = process.Signal(syscall.Signal(0))
		return err == nil
	}
}

// ReleasePort releases a port allocation
func (pr *PortRegistry) ReleasePort(port int) error {
	pr.mutex.Lock()
	defer pr.mutex.Unlock()
	
	entry, exists := pr.entries[port]
	if !exists {
		return fmt.Errorf("port %d not found in registry", port)
	}
	
	// Verify caller owns this allocation
	if entry.ProcessID != os.Getpid() && pr.isProcessAlive(entry.ProcessID) {
		return fmt.Errorf("port %d is owned by another process (PID: %d)", port, entry.ProcessID)
	}
	
	delete(pr.entries, port)
	
	if err := pr.save(); err != nil {
		return fmt.Errorf("failed to save registry: %v", err)
	}
	
	fmt.Printf("🔓 Released port %d from project '%s'\n", port, entry.ProjectName)
	return nil
}

// cleanup removes stale entries from the registry
func (pr *PortRegistry) cleanup() int {
	pr.mutex.Lock()
	defer pr.mutex.Unlock()
	
	var cleaned []int
	for port, entry := range pr.entries {
		// Check if process is still alive
		if !pr.isProcessAlive(entry.ProcessID) {
			// Double-check port is not in use by different process
			if pr.isPortAvailable(port) {
				cleaned = append(cleaned, port)
				delete(pr.entries, port)
			} else {
				// Port in use by different process, mark as orphaned
				entry.Status = "orphaned"
				entry.LastSeen = time.Now()
			}
		} else {
			// Process alive, mark as active
			entry.Status = "active"
			entry.LastSeen = time.Now()
		}
	}
	
	if len(cleaned) > 0 {
		pr.save()
		fmt.Printf("🧹 Cleaned up %d stale port allocations: %v\n", len(cleaned), cleaned)
	}
	
	return len(cleaned)
}

// ListAllocations returns all current port allocations
func (pr *PortRegistry) ListAllocations() []*PortRegistryEntry {
	pr.mutex.RLock()
	defer pr.mutex.RUnlock()
	
	var result []*PortRegistryEntry
	for _, entry := range pr.entries {
		result = append(result, entry)
	}
	return result
}

// load reads the registry from disk
func (pr *PortRegistry) load() error {
	if _, err := os.Stat(pr.registryPath); os.IsNotExist(err) {
		// Registry file doesn't exist yet, start fresh
		return nil
	}
	
	data, err := ioutil.ReadFile(pr.registryPath)
	if err != nil {
		return err
	}
	
	var entries []*PortRegistryEntry
	if err := json.Unmarshal(data, &entries); err != nil {
		return err
	}
	
	// Convert to map
	for _, entry := range entries {
		pr.entries[entry.Port] = entry
	}
	
	return nil
}

// save writes the registry to disk with file locking
func (pr *PortRegistry) save() error {
	// Simple file locking using atomic rename
	tempPath := pr.registryPath + ".tmp"
	
	// Convert map to slice for JSON
	var entries []*PortRegistryEntry
	for _, entry := range pr.entries {
		entries = append(entries, entry)
	}
	
	data, err := json.MarshalIndent(entries, "", "  ")
	if err != nil {
		return err
	}
	
	// Write to temp file first
	if err := ioutil.WriteFile(tempPath, data, 0644); err != nil {
		return err
	}
	
	// Atomic rename
	return os.Rename(tempPath, pr.registryPath)
}

// Main CLI interface
func main() {
	if len(os.Args) < 2 {
		fmt.Println("ContextLite System-Wide Port Registry")
		fmt.Println("Usage: port-registry <command> [args...]")
		fmt.Println()
		fmt.Println("Commands:")
		fmt.Println("  allocate <project-name> <project-path>  - Allocate port for project")
		fmt.Println("  release <port>                          - Release port allocation")
		fmt.Println("  list                                    - List all allocations")
		fmt.Println("  cleanup                                 - Remove stale allocations")
		fmt.Println("  status                                  - Show registry status")
		fmt.Println("  stats                                   - Show detailed statistics (JSON)")
		os.Exit(1)
	}
	
	registry, err := NewPortRegistry()
	if err != nil {
		fmt.Printf("Error: Failed to initialize port registry: %v\n", err)
		os.Exit(1)
	}
	
	command := os.Args[1]
	
	switch command {
	case "allocate":
		if len(os.Args) < 4 {
			fmt.Println("Usage: port-registry allocate <project-name> <project-path>")
			os.Exit(1)
		}
		
		projectName := os.Args[2]
		projectPath := os.Args[3]
		
		entry, err := registry.AllocatePort(projectName, projectPath)
		if err != nil {
			fmt.Printf("Error: %v\n", err)
			os.Exit(1)
		}
		
		// Output JSON for easy parsing
		result := map[string]interface{}{
			"port":         entry.Port,
			"project_name": entry.ProjectName,
			"project_path": entry.ProjectPath,
			"process_id":   entry.ProcessID,
			"status":       "allocated",
		}
		jsonOutput, _ := json.Marshal(result)
		fmt.Println(string(jsonOutput))
		
	case "release":
		if len(os.Args) < 3 {
			fmt.Println("Usage: port-registry release <port>")
			os.Exit(1)
		}
		
		port, err := strconv.Atoi(os.Args[2])
		if err != nil {
			fmt.Printf("Error: Invalid port number: %v\n", err)
			os.Exit(1)
		}
		
		if err := registry.ReleasePort(port); err != nil {
			fmt.Printf("Error: %v\n", err)
			os.Exit(1)
		}
		
	case "list":
		allocations := registry.ListAllocations()
		if len(allocations) == 0 {
			fmt.Println("No port allocations found")
		} else {
			fmt.Printf("Found %d port allocations:\n", len(allocations))
			for _, entry := range allocations {
				alive := registry.isProcessAlive(entry.ProcessID)
				status := entry.Status
				if !alive {
					status = "dead"
				}
				fmt.Printf("  Port %d -> %s (%s) [PID: %d, Status: %s]\n", 
					entry.Port, entry.ProjectName, entry.ProjectPath, entry.ProcessID, status)
			}
		}
		
	case "cleanup":
		fmt.Println("Cleaning up stale port allocations...")
		cleaned := registry.cleanup()
		active := len(registry.ListAllocations())
		
		result := map[string]interface{}{
			"cleaned_entries": cleaned,
			"active_entries":  active,
			"status":         "complete",
		}
		
		jsonOutput, _ := json.Marshal(result)
		fmt.Println(string(jsonOutput))
		
	case "status":
		allocations := registry.ListAllocations()
		active := 0
		dead := 0
		for _, entry := range allocations {
			if registry.isProcessAlive(entry.ProcessID) {
				active++
			} else {
				dead++
			}
		}
		
		fmt.Printf("Port Registry Status:\n")
		fmt.Printf("  Registry Path: %s\n", registry.registryPath)
		fmt.Printf("  Total Allocations: %d\n", len(allocations))
		fmt.Printf("  Active Processes: %d\n", active)
		fmt.Printf("  Dead Processes: %d\n", dead)
		
	case "stats":
		allocations := registry.ListAllocations()
		active := 0
		dead := 0
		ports := make([]int, 0)
		projects := make([]string, 0)
		
		for _, entry := range allocations {
			ports = append(ports, entry.Port)
			projects = append(projects, entry.ProjectName)
			if registry.isProcessAlive(entry.ProcessID) {
				active++
			} else {
				dead++
			}
		}
		
		stats := map[string]interface{}{
			"registry_path":     registry.registryPath,
			"total_allocations": len(allocations),
			"active_processes":  active,
			"dead_processes":    dead,
			"allocated_ports":   ports,
			"projects":          projects,
			"timestamp":         time.Now().Unix(),
		}
		
		jsonOutput, _ := json.Marshal(stats)
		fmt.Println(string(jsonOutput))
		
	default:
		fmt.Printf("Unknown command: %s\n", command)
		os.Exit(1)
	}
}
