package integration

import (
	"testing"

	"contextlite/internal/storage"
	"contextlite/pkg/config"
)

func TestContextLiteStartup(t *testing.T) {
	configPath := "../../configs/default.yaml"

	t.Log("Testing ContextLite basic startup...")

	// Load configuration
	cfg, err := config.Load(configPath)
	if err != nil {
		t.Fatalf("Failed to load config: %v", err)
	}

	// Skip Z3 validation for startup test
	cfg.SMT.Z3.BinaryPath = ""

	t.Logf("Configuration loaded successfully!")
	t.Logf("Server host: %s", cfg.Server.Host)
	t.Logf("Server port: %d", cfg.Server.Port)
	t.Logf("Database path: %s", cfg.Storage.DatabasePath)

	// Test storage initialization
	t.Log("Initializing storage...")
	storage, err := storage.New(cfg.Storage.DatabasePath)
	if err != nil {
		t.Fatalf("Failed to initialize storage: %v", err)
	}
	defer storage.Close()

	t.Log("Storage initialized successfully!")
	t.Log("Test completed successfully!")
}
