package main

import (
	"context"
	"flag"
	"fmt"
	"log"
	"net/http"
	"os"
	"os/signal"
	"strconv"
	"syscall"
	"time"

	"go.uber.org/zap"

	"contextlite/internal/api"
	"contextlite/internal/engine"
	"contextlite/internal/license"
	"contextlite/internal/storage"
	"contextlite/pkg/config"
)

var (
	Version = "1.0.28"
	Commit  = "dev"
	Date    = "unknown"
)

func main() {
	var configPath string
	var showVersion bool
	flag.StringVar(&configPath, "config", "configs/default.yaml", "Path to configuration file")
	flag.BoolVar(&showVersion, "version", false, "Show version information")
	flag.Parse()

	if showVersion {
		fmt.Printf("ContextLite %s (commit: %s, built: %s)\n", Version, Commit, Date)
		return
	}

	if err := runServer(configPath, nil); err != nil {
		log.Fatalf("Server failed: %v", err)
	}
}

// runServer contains the main server logic, extracted for testing
// stopChan allows tests to inject a way to stop the server
func runServer(configPath string, stopChan <-chan struct{}) error {
	// Load configuration
	cfg, err := config.Load(configPath)
	if err != nil {
		return fmt.Errorf("failed to load config: %w", err)
	}

	// Setup logger
	logger, err := setupLogger(cfg.Logging.Level)
	if err != nil {
		return fmt.Errorf("failed to setup logger: %w", err)
	}
	defer logger.Sync()

	logger.Info("Starting ContextLite", zap.String("config", configPath))

	// Initialize license manager and feature gate with trial support
	featureGate := license.NewEnhancedFeatureGate()
	
	// Log license/trial status
	status := featureGate.GetStatus()
	logger.Info("License/Trial Status", 
		zap.String("tier", featureGate.GetTier()),
		zap.String("status", status["status"].(string)),
		zap.String("message", status["message"].(string)))
	
	// Log trial information if applicable
	if trialInfo, ok := status["trial"].(map[string]interface{}); ok {
		if isActive, ok := trialInfo["is_active"].(bool); ok && isActive {
			remaining := trialInfo["days_remaining"].(int)
			logger.Info("Trial Information", 
				zap.Int("days_remaining", remaining),
				zap.Bool("first_run", trialInfo["first_run"].(bool)))
		}
	}

	// Initialize storage
	storage, err := storage.New(cfg.Storage.DatabasePath)
	if err != nil {
		logger.Fatal("Failed to initialize storage", zap.Error(err))
		return fmt.Errorf("failed to initialize storage: %w", err)
	}
	defer storage.Close()

	logger.Info("Storage initialized", zap.String("database", cfg.Storage.DatabasePath))

	// Initialize context engine (loads private engine if available, falls back to public)
	contextEngine := engine.LoadEngine(cfg, storage)

	// Initialize API server with feature gate
	apiServer := api.New(contextEngine, storage, cfg, logger, featureGate)

	// Create HTTP server with timeouts
	addr := cfg.Server.Host + ":" + strconv.Itoa(cfg.Server.Port)
	server := &http.Server{
		Addr:         addr,
		Handler:      apiServer,
		ReadTimeout:  30 * time.Second,
		WriteTimeout: 30 * time.Second,
		IdleTimeout:  120 * time.Second,
	}

	// Setup graceful shutdown
	quit := make(chan os.Signal, 1)
	signal.Notify(quit, syscall.SIGINT, syscall.SIGTERM)

	// Start server in a goroutine
	serverErr := make(chan error, 1)
	go func() {
		logger.Info("Starting HTTP server", zap.String("address", addr))
		if err := server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			logger.Fatal("Server failed to start", zap.Error(err))
			serverErr <- err
		}
	}()

	logger.Info("Server started successfully. Press Ctrl+C to stop.")

	// Wait for interrupt signal or test stop signal
	select {
	case <-quit:
		logger.Info("Shutting down server...")
	case <-stopChan:
		logger.Info("Test requested shutdown...")
	case err := <-serverErr:
		return fmt.Errorf("server startup failed: %w", err)
	}

	// Create a deadline to wait for
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	// Attempt graceful shutdown
	if err := server.Shutdown(ctx); err != nil {
		logger.Error("Server forced to shutdown", zap.Error(err))
		return fmt.Errorf("server forced to shutdown: %w", err)
	} else {
		logger.Info("Server exited gracefully")
	}

	return nil
}

func setupLogger(level string) (*zap.Logger, error) {
	var config zap.Config
	
	switch level {
	case "debug":
		config = zap.NewDevelopmentConfig()
	case "info":
		config = zap.NewProductionConfig()
	default:
		config = zap.NewProductionConfig()
	}
	
	return config.Build()
}
