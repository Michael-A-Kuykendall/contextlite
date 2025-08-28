package port

import (
	"encoding/json"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"time"
)

// PortAuditDaemon runs automated maintenance of the port registry
type PortAuditDaemon struct {
	registryPath string
	stopChan     chan bool
	running      bool
}

// AuditConfig controls the audit behavior
type AuditConfig struct {
	// How often to run full audit (default: 5 minutes)
	AuditInterval time.Duration
	
	// How often to do quick health checks (default: 30 seconds)
	HealthCheckInterval time.Duration
	
	// Maximum age for stale entries (default: 1 hour)
	MaxStaleAge time.Duration
	
	// Enable verbose logging
	VerboseLogging bool
}

// DefaultAuditConfig returns sensible defaults
func DefaultAuditConfig() *AuditConfig {
	return &AuditConfig{
		AuditInterval:       5 * time.Minute,
		HealthCheckInterval: 30 * time.Second,
		MaxStaleAge:         1 * time.Hour,
		VerboseLogging:      false,
	}
}

// NewPortAuditDaemon creates a new audit daemon
func NewPortAuditDaemon() *PortAuditDaemon {
	// Find the port-registry binary
	execPath, err := os.Executable()
	if err != nil {
		log.Printf("Warning: Could not find executable path: %v", err)
		return &PortAuditDaemon{registryPath: "port-registry"}
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
	
	return &PortAuditDaemon{
		registryPath: registryPath,
		stopChan:     make(chan bool),
		running:      false,
	}
}

// Start begins the audit daemon in the background
func (pad *PortAuditDaemon) Start(config *AuditConfig) {
	if pad.running {
		return
	}
	
	if config == nil {
		config = DefaultAuditConfig()
	}
	
	pad.running = true
	
	// Start background goroutine
	go pad.runAuditLoop(config)
	
	if config.VerboseLogging {
		log.Printf("🔍 Port Audit Daemon: Started with audit interval %v", config.AuditInterval)
	}
}

// Stop gracefully stops the audit daemon
func (pad *PortAuditDaemon) Stop() {
	if !pad.running {
		return
	}
	
	pad.stopChan <- true
	pad.running = false
	log.Printf("🛑 Port Audit Daemon: Stopped")
}

// runAuditLoop is the main audit loop
func (pad *PortAuditDaemon) runAuditLoop(config *AuditConfig) {
	auditTicker := time.NewTicker(config.AuditInterval)
	healthTicker := time.NewTicker(config.HealthCheckInterval)
	
	defer auditTicker.Stop()
	defer healthTicker.Stop()
	
	// Run initial audit
	pad.runFullAudit(config)
	
	for {
		select {
		case <-pad.stopChan:
			return
			
		case <-auditTicker.C:
			pad.runFullAudit(config)
			
		case <-healthTicker.C:
			pad.runHealthCheck(config)
		}
	}
}

// runFullAudit performs a comprehensive registry cleanup
func (pad *PortAuditDaemon) runFullAudit(config *AuditConfig) {
	if config.VerboseLogging {
		log.Printf("🔍 Port Audit: Running full audit...")
	}
	
	// Call port registry cleanup
	cmd := exec.Command(pad.registryPath, "cleanup")
	output, err := cmd.Output()
	if err != nil {
		log.Printf("Warning: Port audit cleanup failed: %v", err)
		return
	}
	
	// Parse cleanup results
	var result map[string]interface{}
	if err := json.Unmarshal(output, &result); err != nil {
		if config.VerboseLogging {
			log.Printf("Port audit output: %s", string(output))
		}
		return
	}
	
	// Log significant cleanup actions
	if cleaned, ok := result["cleaned_entries"].(float64); ok && cleaned > 0 {
		log.Printf("🧹 Port Audit: Cleaned up %.0f stale port allocations", cleaned)
	}
	
	if config.VerboseLogging {
		if active, ok := result["active_entries"].(float64); ok {
			log.Printf("🔍 Port Audit: %.0f active port allocations", active)
		}
	}
}

// runHealthCheck does a quick registry health check
func (pad *PortAuditDaemon) runHealthCheck(config *AuditConfig) {
	// Quick status check - don't log unless there's an issue
	cmd := exec.Command(pad.registryPath, "status")
	_, err := cmd.Output()
	if err != nil {
		log.Printf("⚠️  Port Registry Health Check: Failed - %v", err)
		
		// Try to recover by running a cleanup
		go pad.runFullAudit(config)
	}
}

// GetRegistryStats returns current registry statistics
func (pad *PortAuditDaemon) GetRegistryStats() (map[string]interface{}, error) {
	cmd := exec.Command(pad.registryPath, "stats")
	output, err := cmd.Output()
	if err != nil {
		return nil, fmt.Errorf("failed to get registry stats: %v", err)
	}
	
	var stats map[string]interface{}
	if err := json.Unmarshal(output, &stats); err != nil {
		return nil, fmt.Errorf("failed to parse registry stats: %v", err)
	}
	
	return stats, nil
}

// ForceAudit triggers an immediate full audit
func (pad *PortAuditDaemon) ForceAudit() {
	config := DefaultAuditConfig()
	config.VerboseLogging = true
	pad.runFullAudit(config)
}

// StartSilentAuditDaemon starts the daemon with minimal logging (production mode)
func StartSilentAuditDaemon() *PortAuditDaemon {
	daemon := NewPortAuditDaemon()
	config := DefaultAuditConfig()
	config.VerboseLogging = false
	
	daemon.Start(config)
	return daemon
}

// StartVerboseAuditDaemon starts the daemon with verbose logging (development mode)
func StartVerboseAuditDaemon() *PortAuditDaemon {
	daemon := NewPortAuditDaemon()
	config := DefaultAuditConfig()
	config.VerboseLogging = true
	config.AuditInterval = 2 * time.Minute  // More frequent in dev mode
	
	daemon.Start(config)
	return daemon
}
