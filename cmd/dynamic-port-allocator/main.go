package main

import (
	"fmt"
	"net"
	"math/rand"
	"time"
	"os"
	"encoding/json"
)

// PortRange defines a range of ports to scan
type PortRange struct {
	Start       int    `json:"start"`
	End         int    `json:"end"`
	Description string `json:"description"`
}

// DynamicPortConfig holds the configuration for dynamic port allocation
type DynamicPortConfig struct {
	ScanRanges      []PortRange `json:"scan_ranges"`
	ExcludedPorts   []int       `json:"excluded_ports"`
	MaxAttempts     int         `json:"max_attempts"`
	PreferredSpacing int        `json:"preferred_spacing"`
}

// PortAllocator handles dynamic port discovery and allocation
type PortAllocator struct {
	config       DynamicPortConfig
	allocatedPorts map[int]string // port -> project_name
	rand         *rand.Rand
}

// NewPortAllocator creates a new dynamic port allocator
func NewPortAllocator(config DynamicPortConfig) *PortAllocator {
	return &PortAllocator{
		config:         config,
		allocatedPorts: make(map[int]string),
		rand:          rand.New(rand.NewSource(time.Now().UnixNano())),
	}
}

// IsPortAvailable checks if a port is available by actually trying to bind to it
func (pa *PortAllocator) IsPortAvailable(port int) bool {
	// Check if port is in excluded list
	for _, excluded := range pa.config.ExcludedPorts {
		if port == excluded {
			return false
		}
	}
	
	// Check if we've already allocated this port
	if _, exists := pa.allocatedPorts[port]; exists {
		return false
	}
	
	// Try to bind to the port to test actual availability
	address := fmt.Sprintf(":%d", port)
	listener, err := net.Listen("tcp", address)
	if err != nil {
		return false
	}
	
	// Port is available, close the test connection
	listener.Close()
	return true
}

// FindAvailablePort finds an available port using dynamic scanning
func (pa *PortAllocator) FindAvailablePort(projectName string) (int, error) {
	attempts := 0
	
	for attempts < pa.config.MaxAttempts {
		// Choose a random port range to scan
		rangeIndex := pa.rand.Intn(len(pa.config.ScanRanges))
		portRange := pa.config.ScanRanges[rangeIndex]
		
		// Pick a random port within the range
		portSpan := portRange.End - portRange.Start + 1
		basePort := portRange.Start + pa.rand.Intn(portSpan)
		
		// Try the base port and nearby ports with preferred spacing
		for offset := 0; offset < pa.config.PreferredSpacing*2; offset++ {
			candidatePort := basePort + offset
			
			// Make sure we're still in range
			if candidatePort > portRange.End {
				break
			}
			
			if pa.IsPortAvailable(candidatePort) {
				// Found an available port!
				pa.allocatedPorts[candidatePort] = projectName
				fmt.Printf("Allocated port %d to project '%s'\n", candidatePort, projectName)
				return candidatePort, nil
			}
		}
		
		attempts++
	}
	
	return 0, fmt.Errorf("could not find available port after %d attempts", pa.config.MaxAttempts)
}

// ReleasePort releases a port allocation
func (pa *PortAllocator) ReleasePort(port int) {
	if projectName, exists := pa.allocatedPorts[port]; exists {
		delete(pa.allocatedPorts, port)
		fmt.Printf("Released port %d from project '%s'\n", port, projectName)
	}
}

// GetAllocatedPorts returns all currently allocated ports
func (pa *PortAllocator) GetAllocatedPorts() map[int]string {
	result := make(map[int]string)
	for port, project := range pa.allocatedPorts {
		result[port] = project
	}
	return result
}

// ScanPortRange scans a range for available ports (for diagnostics)
func (pa *PortAllocator) ScanPortRange(start, end int) []int {
	var available []int
	
	for port := start; port <= end; port++ {
		if pa.IsPortAvailable(port) {
			available = append(available, port)
		}
	}
	
	return available
}

// DefaultPortConfig returns a sensible default configuration
func DefaultPortConfig() DynamicPortConfig {
	return DynamicPortConfig{
		ScanRanges: []PortRange{
			{Start: 8000, End: 8999, Description: "Primary development range"},
			{Start: 9000, End: 9999, Description: "Secondary development range"},
			{Start: 10000, End: 19999, Description: "User application range"},
			{Start: 20000, End: 29999, Description: "Extended user range"},
		},
		ExcludedPorts: []int{
			8080, 8443, 8888, 9090, 3000, 3001, 4200, 5000, 5432, 6379, 27017,
		},
		MaxAttempts:      100,
		PreferredSpacing: 10,
	}
}

func main() {
	if len(os.Args) < 2 {
		fmt.Println("Usage: dynamic-port-allocator <command> [args...]")
		fmt.Println("Commands:")
		fmt.Println("  find <project-name>     - Find and allocate a port for project")
		fmt.Println("  release <port>          - Release a port allocation")
		fmt.Println("  scan <start> <end>      - Scan a port range for available ports")
		fmt.Println("  list                    - List all allocated ports")
		os.Exit(1)
	}
	
	// Create allocator with default config
	allocator := NewPortAllocator(DefaultPortConfig())
	
	command := os.Args[1]
	
	switch command {
	case "find":
		if len(os.Args) < 3 {
			fmt.Println("Usage: dynamic-port-allocator find <project-name>")
			os.Exit(1)
		}
		projectName := os.Args[2]
		port, err := allocator.FindAvailablePort(projectName)
		if err != nil {
			fmt.Printf("Error: %v\n", err)
			os.Exit(1)
		}
		
		// Output JSON for easy parsing
		result := map[string]interface{}{
			"port":         port,
			"project_name": projectName,
			"status":       "allocated",
		}
		jsonOutput, _ := json.Marshal(result)
		fmt.Println(string(jsonOutput))
		
	case "scan":
		if len(os.Args) < 4 {
			fmt.Println("Usage: dynamic-port-allocator scan <start> <end>")
			os.Exit(1)
		}
		
		var start, end int
		fmt.Sscanf(os.Args[2], "%d", &start)
		fmt.Sscanf(os.Args[3], "%d", &end)
		
		available := allocator.ScanPortRange(start, end)
		fmt.Printf("Available ports in range %d-%d: %v\n", start, end, available)
		fmt.Printf("Total available: %d ports\n", len(available))
		
	case "list":
		allocated := allocator.GetAllocatedPorts()
		if len(allocated) == 0 {
			fmt.Println("No ports currently allocated")
		} else {
			fmt.Println("Currently allocated ports:")
			for port, project := range allocated {
				fmt.Printf("  Port %d -> Project '%s'\n", port, project)
			}
		}
		
	default:
		fmt.Printf("Unknown command: %s\n", command)
		os.Exit(1)
	}
}
