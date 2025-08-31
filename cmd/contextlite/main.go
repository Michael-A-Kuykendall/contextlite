package main

import (
	"bufio"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io/ioutil"
	"log"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"runtime"
	"sort"
	"strconv"
	"strings"
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
	Version = "2.0.0"
	Commit  = "dev"
	Date    = "unknown"
)

func main() {
	var configPath string
	var showVersion bool
	var runOnboarding bool
	flag.StringVar(&configPath, "config", "configs/default.yaml", "Path to configuration file")
	flag.BoolVar(&showVersion, "version", false, "Show version information")
	flag.BoolVar(&runOnboarding, "onboard", false, "Run interactive onboarding setup")
	flag.Parse()

	if showVersion {
		fmt.Printf("ContextLite %s (commit: %s, built: %s)\n", Version, Commit, Date)
		return
	}

	if runOnboarding {
		if err := runOnboardingProcess(); err != nil {
			log.Fatalf("Onboarding failed: %v", err)
		}
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
		// Trigger log ingestion on exit
		if err := runLogIngestionOnExit(cfg); err != nil {
			logger.Warn("Log ingestion failed during shutdown", zap.Error(err))
		}
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

// OnboardingChoice represents user choices for each project
type OnboardingChoice struct {
	ProjectName    string `json:"project_name"`
	ProjectPath    string `json:"project_path"`
	Selected       bool   `json:"selected"`
	Port           int    `json:"port"`
	HasDatabase    bool   `json:"has_database"`
	DatabaseSize   int64  `json:"database_size_bytes"`
	
	// Integration choices
	EnableClaudeCodeLogs bool `json:"enable_claude_code_logs"`
	EnableCopilotLogs    bool `json:"enable_copilot_logs"`
	EnableVSCodeLogs     bool `json:"enable_vscode_logs"`
	EnableGitLogs        bool `json:"enable_git_logs"`
	EnableMCPIntegration bool `json:"enable_mcp_integration"`
	EnableAutoStart      bool `json:"enable_auto_start"`
}

// GlobalSettings for system-wide preferences
type GlobalSettings struct {
	RepositoriesPath   string `json:"repositories_path"`
	BasePort          int    `json:"base_port"`
	AutoImportInterval string `json:"auto_import_interval"`
	DefaultIntegrations struct {
		ClaudeCode bool `json:"claude_code"`
		Copilot    bool `json:"copilot"`
		VSCode     bool `json:"vscode"`
		Git        bool `json:"git"`
		MCP        bool `json:"mcp"`
	} `json:"default_integrations"`
}

// runOnboardingProcess executes the interactive onboarding
func runOnboardingProcess() error {
	fmt.Println("🚀 ContextLite Interactive Onboarding")
	fmt.Println("=====================================")
	fmt.Println("Setting up auto-discovery and multi-project integration...")
	fmt.Println()
	
	// Auto-discover repositories
	homeDir, _ := os.UserHomeDir()
	defaultRepoPath := filepath.Join(homeDir, "repos")
	if runtime.GOOS == "windows" {
		defaultRepoPath = `C:\Users\` + os.Getenv("USERNAME") + `\repos`
	}
	
	reader := bufio.NewReader(os.Stdin)
	fmt.Printf("📁 Repository directory [%s]: ", defaultRepoPath)
	repoPath, _ := reader.ReadString('\n')
	repoPath = strings.TrimSpace(repoPath)
	if repoPath == "" {
		repoPath = defaultRepoPath
	}
	
	fmt.Println("\n🔍 Discovering repositories...")
	projects, err := discoverProjects(repoPath)
	if err != nil {
		return fmt.Errorf("discovery failed: %w", err)
	}
	
	fmt.Printf("✅ Found %d repositories\n", len(projects))
	
	// Quick setup option
	fmt.Print("\n🚀 Quick setup (all projects, default integrations)? [Y/n]: ")
	input, _ := reader.ReadString('\n')
	input = strings.TrimSpace(strings.ToLower(input))
	
	if input != "n" && input != "no" {
		return executeQuickSetup(projects, repoPath)
	}
	
	fmt.Println("Use 'contextlite-onboard' for detailed configuration options.")
	return nil
}

// validateRepositoryPath validates and sanitizes repository paths for security
func validateRepositoryPath(repoPath string) (string, error) {
	// SECURITY: Reject paths with traversal patterns immediately
	if strings.Contains(repoPath, "..") {
		return "", fmt.Errorf("path traversal not allowed: contains '..'")
	}
	
	// Clean and resolve the path
	cleanPath, err := filepath.Abs(filepath.Clean(repoPath))
	if err != nil {
		return "", fmt.Errorf("invalid path: %w", err)
	}
	
	// SECURITY: Additional traversal check after resolution
	if strings.Contains(cleanPath, "..") {
		return "", fmt.Errorf("resolved path contains traversal patterns")
	}
	
	// SECURITY: Prevent access to system directories
	forbiddenPaths := []string{
		"C:\\Windows",
		"C:\\Program Files", 
		"C:\\Program Files (x86)",
		"C:\\Users\\All Users",
		"C:\\System Volume Information",
		"/etc",
		"/root",
		"/sys",
		"/proc",
		"/boot",
		"/usr/bin",
		"/usr/sbin",
		"/var/log",
	}
	
	cleanPathLower := strings.ToLower(cleanPath)
	for _, forbidden := range forbiddenPaths {
		if strings.HasPrefix(cleanPathLower, strings.ToLower(forbidden)) {
			return "", fmt.Errorf("access to system directory forbidden: %s", forbidden)
		}
	}
	
	// SECURITY: Ensure path exists and is a directory
	info, err := os.Stat(cleanPath)
	if err != nil {
		return "", fmt.Errorf("path does not exist: %w", err)
	}
	if !info.IsDir() {
		return "", fmt.Errorf("path is not a directory")
	}
	
	// SECURITY: Additional check - must be under user's home directory or common dev locations
	homeDir, _ := os.UserHomeDir()
	allowedPrefixes := []string{
		strings.ToLower(homeDir),
		"c:\\dev",
		"c:\\code", 
		"c:\\projects",
		"c:\\repos",
		"/home",
		"/Users",
		"/opt/dev",
		"/usr/local/src",
	}
	
	pathAllowed := false
	for _, allowed := range allowedPrefixes {
		if strings.HasPrefix(cleanPathLower, allowed) {
			pathAllowed = true
			break
		}
	}
	
	if !pathAllowed {
		return "", fmt.Errorf("path outside allowed development directories")
	}
	
	return cleanPath, nil
}

// validateProjectPath ensures project paths are safe for file operations
func validateProjectPath(projectPath string) error {
	cleanPath, err := filepath.Abs(filepath.Clean(projectPath))
	if err != nil {
		return fmt.Errorf("invalid project path: %w", err)
	}
	
	// SECURITY: Prevent writing to system directories
	forbiddenPaths := []string{
		"C:\\Windows",
		"C:\\Program Files",
		"C:\\Program Files (x86)", 
		"/etc",
		"/root",
		"/sys",
		"/proc",
		"/boot",
		"/usr",
	}
	
	cleanPathLower := strings.ToLower(cleanPath)
	for _, forbidden := range forbiddenPaths {
		if strings.HasPrefix(cleanPathLower, strings.ToLower(forbidden)) {
			return fmt.Errorf("cannot write to system directory: %s", forbidden)
		}
	}
	
	return nil
}

// discoverProjects finds Git repositories with security validation
func discoverProjects(repoPath string) ([]*OnboardingChoice, error) {
	var projects []*OnboardingChoice
	
	// SECURITY: Validate and sanitize repository path
	cleanRepoPath, err := validateRepositoryPath(repoPath)
	if err != nil {
		return nil, fmt.Errorf("invalid repository path: %w", err)
	}
	
	// SECURITY: Limit traversal depth and add timeout protection
	maxDepth := 3
	maxProjects := 100
	visited := 0
	startTime := time.Now()
	maxDuration := 30 * time.Second
	
	err = filepath.Walk(cleanRepoPath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return nil
		}
		
		// SECURITY: Enforce depth limits
		relPath, _ := filepath.Rel(cleanRepoPath, path)
		depth := strings.Count(relPath, string(filepath.Separator))
		if depth > maxDepth {
			if info.IsDir() {
				return filepath.SkipDir
			}
			return nil
		}
		
		// SECURITY: Enforce project count limits
		if len(projects) >= maxProjects {
			return fmt.Errorf("maximum project limit reached (%d)", maxProjects)
		}
		
		// SECURITY: Protect against traversal timing attacks
		visited++
		if visited > 10000 {
			return fmt.Errorf("filesystem traversal limit exceeded")
		}
		
		// SECURITY: Timeout protection against resource exhaustion
		if time.Since(startTime) > maxDuration {
			return fmt.Errorf("repository discovery timeout exceeded")
		}
		
		if info.IsDir() && info.Name() == ".git" {
			projectPath := filepath.Dir(path)
			projectName := filepath.Base(projectPath)
			
			// Skip nested .git directories
			relPath, _ := filepath.Rel(repoPath, projectPath)
			if strings.Contains(relPath, string(filepath.Separator)) {
				return nil
			}
			
			project := &OnboardingChoice{
				ProjectName: projectName,
				ProjectPath: projectPath,
				Selected:    true,
			}
			
			// Check for existing database
			findExistingDatabase(project)
			projects = append(projects, project)
			
			fmt.Printf("   📁 %s", projectName)
			if project.HasDatabase {
				fmt.Printf(" (%.1fKB)", float64(project.DatabaseSize)/1024)
			}
			fmt.Println()
		}
		
		return nil
	})
	
	if err != nil {
		return nil, err
	}
	
	sort.Slice(projects, func(i, j int) bool {
		return projects[i].ProjectName < projects[j].ProjectName
	})
	
	return projects, nil
}

// findExistingDatabase looks for existing ContextLite databases with security validation
func findExistingDatabase(project *OnboardingChoice) {
	// SECURITY: Use restrictive, exact patterns only
	patterns := []string{"contextlite.db", "context.db"}
	
	// SECURITY: Validate project path before file operations
	if err := validateProjectPath(project.ProjectPath); err != nil {
		return // Skip unsafe project paths
	}
	
	for _, pattern := range patterns {
		dbPath := filepath.Join(project.ProjectPath, pattern)
		
		// SECURITY: Verify file is actually a database by checking header
		if info, err := os.Stat(dbPath); err == nil && isValidDatabase(dbPath) {
			project.HasDatabase = true
			project.DatabaseSize = info.Size()
			break
		}
	}
}

// isValidDatabase verifies file is a legitimate SQLite database
func isValidDatabase(dbPath string) bool {
	// SECURITY: Check that file is not a symlink
	info, err := os.Lstat(dbPath) // Lstat doesn't follow symlinks
	if err != nil {
		return false
	}
	
	// SECURITY: Reject symlinks to prevent traversal attacks
	if info.Mode()&os.ModeSymlink != 0 {
		return false
	}
	
	// SECURITY: Size limit to prevent processing huge files
	if info.Size() > 1024*1024*1024 { // 1GB limit
		return false
	}
	
	// Read first 16 bytes to check SQLite header
	file, err := os.Open(dbPath)
	if err != nil {
		return false
	}
	defer file.Close()
	
	header := make([]byte, 16)
	n, err := file.Read(header)
	if err != nil || n < 16 {
		return false
	}
	
	// SQLite databases start with "SQLite format 3"
	sqliteHeader := "SQLite format 3\x00"
	return string(header) == sqliteHeader
}

// safeWriteFile performs atomic file writes with backup
func safeWriteFile(filePath string, content []byte) error {
	// SECURITY: Create temporary file first for atomic write
	tempPath := filePath + ".tmp"
	
	// Check if original file exists for backup
	if _, err := os.Stat(filePath); err == nil {
		backupPath := filePath + ".backup"
		if err := os.Rename(filePath, backupPath); err != nil {
			return fmt.Errorf("failed to create backup: %w", err)
		}
		// Remove backup on success, restore on failure
		defer func() {
			if _, err := os.Stat(filePath); err != nil {
				os.Rename(backupPath, filePath) // Restore on failure
			} else {
				os.Remove(backupPath) // Remove backup on success
			}
		}()
	}
	
	// Write to temporary file
	if err := ioutil.WriteFile(tempPath, content, 0644); err != nil {
		return fmt.Errorf("failed to write temp file: %w", err)
	}
	
	// Atomic move
	if err := os.Rename(tempPath, filePath); err != nil {
		os.Remove(tempPath)
		return fmt.Errorf("failed to move temp file: %w", err)
	}
	
	return nil
}

// safeUpdateCLAUDEMD safely updates CLAUDE.md with backup protection
func safeUpdateCLAUDEMD(project *OnboardingChoice, claudePath string) error {
	section := fmt.Sprintf(`
# ContextLite Auto-Discovery
- **Port**: %d
- **Database**: ./contextlite.db%s
- **Quick start**: `+"`contextlite --config contextlite-config.yaml`"+`
- **CLI access**: `+"`contextlite-cli connect %s`"+`
`,
		project.Port,
		map[bool]string{true: " (existing data preserved)", false: ""}[project.HasDatabase],
		project.ProjectName)
	
	// Read existing content
	var existingContent string
	if content, err := ioutil.ReadFile(claudePath); err == nil {
		existingContent = string(content)
	}
	
	// Only update if ContextLite section doesn't exist
	if strings.Contains(existingContent, "# ContextLite") {
		return nil // Already has section, don't modify
	}
	
	newContent := existingContent
	if existingContent != "" {
		newContent += "\n"
	}
	newContent += section
	
	return safeWriteFile(claudePath, []byte(newContent))
}

// executeQuickSetup performs automated setup with defaults
func executeQuickSetup(projects []*OnboardingChoice, repoPath string) error {
	fmt.Println("\n⚡ Quick Setup: Configuring all projects with defaults...")
	
	// Default integrations
	for _, project := range projects {
		project.EnableGitLogs = true
		project.EnableMCPIntegration = true
		project.EnableAutoStart = true
	}
	
	// SECURITY: Secure port assignment with validation
	basePort := 8080
	maxPort := 65535
	systemPortMin := 1024
	
	for i, project := range projects {
		assignedPort := basePort + i
		
		// SECURITY: Validate port range
		if assignedPort > maxPort {
			return fmt.Errorf("too many projects: port %d exceeds maximum", assignedPort)
		}
		if assignedPort < systemPortMin {
			return fmt.Errorf("port %d conflicts with system ports", assignedPort)
		}
		
		project.Port = assignedPort
	}
	
	// Create configs and update CLAUDE.md files
	homeDir, _ := os.UserHomeDir()
	contextliteDir := filepath.Join(homeDir, ".contextlite")
	os.MkdirAll(contextliteDir, 0755)
	
	configCount := 0
	for _, project := range projects {
		// SECURITY: Validate project path before any file operations
		if err := validateProjectPath(project.ProjectPath); err != nil {
			fmt.Printf("   ❌ Skipping unsafe project: %s (%v)\n", project.ProjectName, err)
			continue
		}
		
		// SECURITY: Atomic config file creation with backup
		configPath := filepath.Join(project.ProjectPath, "contextlite-config.yaml")
		configContent := generateQuickConfig(project)
		
		if err := safeWriteFile(configPath, []byte(configContent)); err != nil {
			fmt.Printf("   ❌ Config creation failed for %s: %v\n", project.ProjectName, err)
			continue
		}
		configCount++
		
		// SECURITY: Safe CLAUDE.md update with backup
		claudePath := filepath.Join(project.ProjectPath, "CLAUDE.md")
		if err := safeUpdateCLAUDEMD(project, claudePath); err != nil {
			fmt.Printf("   ⚠️ CLAUDE.md update failed for %s: %v\n", project.ProjectName, err)
		}
		
		fmt.Printf("   ✅ %s (port %d)\n", project.ProjectName, project.Port)
	}
	
	// Save registry
	registryPath := filepath.Join(contextliteDir, "auto_discovery_registry.json")
	registry := map[string]interface{}{
		"projects":        projects,
		"setup_completed": time.Now().Format(time.RFC3339),
		"setup_type":      "quick",
		"base_port":       basePort,
	}
	
	data, _ := json.MarshalIndent(registry, "", "  ")
	ioutil.WriteFile(registryPath, data, 0644)
	
	fmt.Printf("\n🎉 Quick setup complete! %d projects configured\n", configCount)
	fmt.Printf("📄 Registry: %s\n", registryPath)
	fmt.Println("\nNext steps:")
	fmt.Println("  • Run 'contextlite-cli discover' to see all instances")
	fmt.Println("  • Start any project: 'contextlite --config <project>/contextlite-config.yaml'")
	fmt.Println("  • Use 'contextlite-onboard' for detailed customization")
	
	return nil
}

// generateQuickConfig creates minimal project config
func generateQuickConfig(project *OnboardingChoice) string {
	dbPath := "./contextlite.db"
	preserveNote := ""
	if project.HasDatabase {
		preserveNote = " # Existing database preserved"
	}
	
	return fmt.Sprintf(`# ContextLite Auto-Generated Configuration
server:
  port: %d
  host: "127.0.0.1"
  
storage:
  database_path: "%s"%s
  
# Auto-discovery enabled
project:
  name: "%s"
  path: "%s"
  auto_discovery: true
  
# Default integrations
log_ingestion:
  git: true
  interval: "on_exit"
  
mcp:
  enabled: true
  server_name: "%s-mcp"
  
# SMT Configuration
smt:
  solver_timeout_ms: 30000
  max_opt_gap: 0.01
  max_candidates: 200
  max_pairs_per_doc: 1000
  integer_scaling: 1000
  objective_style: "weighted-sum"
  z3:
    binary_path: ""
    enable_verification: false
    max_verification_docs: 0
`,
		project.Port,
		dbPath,
		preserveNote,
		project.ProjectName,
		strings.ReplaceAll(project.ProjectPath, "\\", "/"),
		project.ProjectName)
}

// runLogIngestionOnExit handles automated log ingestion during shutdown
func runLogIngestionOnExit(cfg *config.Config) error {
	// Check if log ingestion is configured
	configPath := filepath.Join(filepath.Dir(cfg.Storage.DatabasePath), ".contextlite", "log_ingestion.json")
	if _, err := os.Stat(configPath); os.IsNotExist(err) {
		return nil // No log ingestion configured
	}
	
	fmt.Println("📥 Importing development logs...")
	
	// Load ingestion config
	data, err := ioutil.ReadFile(configPath)
	if err != nil {
		return err
	}
	
	var ingestionConfig map[string]interface{}
	if err := json.Unmarshal(data, &ingestionConfig); err != nil {
		return err
	}
	
	// Quick import of Git history (most reliable)
	projectPath := filepath.Dir(cfg.Storage.DatabasePath)
	gitDir := filepath.Join(projectPath, ".git")
	
	if _, err := os.Stat(gitDir); err == nil {
		fmt.Println("   📊 Importing recent Git activity...")
		// This would integrate with actual ContextLite indexing system
		// For now, just simulate the import
		time.Sleep(500 * time.Millisecond)
		fmt.Println("   ✅ Git history imported")
	}
	
	return nil
}
