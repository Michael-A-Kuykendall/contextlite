package port

import (
	"fmt"
	"log"
	"net/http"
	"time"
	
	"contextlite/pkg/config"
)

// InvisiblePortManager - Now uses lightweight, event-driven approach
type InvisiblePortManager struct {
	currentPort         int
	lightweightManager *LightweightPortManager
}

// NewInvisiblePortManager creates a zero-overhead port manager
func NewInvisiblePortManager() *InvisiblePortManager {
	return &InvisiblePortManager{
		lightweightManager: NewLightweightPortManager(),
	}
}

// StartInvisiblePortManagement - No background processes, all event-driven
func (ipm *InvisiblePortManager) StartInvisiblePortManagement(cfg *config.Config) (int, error) {
	// Get port allocation (event-driven, cleanup-on-demand)
	port, err := ipm.lightweightManager.GetProjectPort(cfg)
	if err != nil {
		return 0, fmt.Errorf("failed to allocate port: %v", err)
	}
	
	ipm.currentPort = port
	
	// Set up graceful shutdown (event-driven)
	ipm.setupGracefulShutdown()
	
	log.Printf("🚀 ContextLite Server starting on port %d", port)
	
	return port, nil
}

// setupGracefulShutdown - Event-driven cleanup (only on exit signal)
func (ipm *InvisiblePortManager) setupGracefulShutdown() {
	SetupGracefulPortRelease(ipm.currentPort)
}

// GetPortStats - On-demand statistics (no background collection)
func (ipm *InvisiblePortManager) GetPortStats() (map[string]interface{}, error) {
	// This would call the registry stats command on-demand
	// No background statistics collection
	stats := map[string]interface{}{
		"current_port": ipm.currentPort,
		"management_type": "lightweight_event_driven",
		"background_processes": 0,
		"memory_overhead": "minimal",
	}
	return stats, nil
}

// Example integration with main server startup (ZERO overhead)
func StartContextLiteServerWithInvisiblePortManagement(cfg *config.Config) error {
	// Create lightweight port manager (no background processes)
	portManager := NewInvisiblePortManager()
	
	// Get port (event-driven, cleanup-on-demand)
	port, err := portManager.StartInvisiblePortManagement(cfg)
	if err != nil {
		return fmt.Errorf("port management failed: %v", err)
	}
	
	// Update config with allocated port
	cfg.Server.Port = port
	
	// Start your regular server
	mux := http.NewServeMux()
	
	// Add debug endpoint for port statistics (on-demand)
	mux.HandleFunc("/debug/port-stats", func(w http.ResponseWriter, r *http.Request) {
		stats, err := portManager.GetPortStats()
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		
		w.Header().Set("Content-Type", "application/json")
		fmt.Fprintf(w, "%v", stats)
	})
	
	// Add your regular endpoints here
	mux.HandleFunc("/health", func(w http.ResponseWriter, r *http.Request) {
		fmt.Fprintf(w, `{"status":"ok","port":%d}`, port)
	})
	
	// Start server
	server := &http.Server{
		Addr:    fmt.Sprintf(":%d", port),
		Handler: mux,
		ReadTimeout: 30 * time.Second,
		WriteTimeout: 30 * time.Second,
	}
	
	log.Printf("🎯 Server listening on http://localhost:%d", port)
	log.Printf("✨ Zero-overhead port management active")
	
	// Start server (blocking)
	return server.ListenAndServe()
}

// WizardOfOzPortManagement - Updated demo showing zero overhead
func WizardOfOzPortManagement() {
	fmt.Println("🧙‍♂️ Wizard of Oz Port Management - ZERO OVERHEAD VERSION")
	fmt.Println("======================================================")
	fmt.Println()
	
	// User just runs: contextlite
	// Behind the scenes:
	
	fmt.Println("👤 User runs: ./contextlite")
	fmt.Println("🎭 Behind the scenes (ZERO background processes)...")
	fmt.Println("   🔍 Port registry: Quick cleanup-on-demand")
	fmt.Println("   🎯 Port registry: Allocated port 8800 (event-driven)")
	fmt.Println("   🚀 Server: Starting on port 8800")
	fmt.Println("   ✨ Zero memory overhead, no polling, no background daemons")
	fmt.Println()
	
	// User doesn't know about ports at all
	fmt.Println("✨ User experience:")
	fmt.Println("   ✅ ContextLite Server starting...")
	fmt.Println("   ✅ Ready at http://localhost:8800")
	fmt.Println("   🌟 Everything just works!")
	fmt.Println()
	
	// No background processes!
	fmt.Println("🎯 Memory-Friendly Architecture:")
	fmt.Println("   ✅ No background polling (Docker/Kubernetes pattern)")
	fmt.Println("   ✅ Event-driven cleanup (only when needed)")
	fmt.Println("   ✅ On-demand process detection (no continuous scanning)")
	fmt.Println("   ✅ Cleanup-on-allocation (industry standard)")
	fmt.Println("   ✅ Zero memory overhead when idle")
	fmt.Println()
	
	fmt.Println("🎯 Result: Ports are invisible AND memory-friendly!")
}
