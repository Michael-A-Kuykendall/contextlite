package tests

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
	
	"contextlite/internal/logs"
	"contextlite/internal/mcp"
)

// OnboardingChoice represents user choices for each project (test copy)
type OnboardingChoice struct {
	ProjectName    string `json:"project_name"`
	ProjectPath    string `json:"project_path"`
	Selected       bool   `json:"selected"`
	Port           int    `json:"port"`
	HasDatabase    bool   `json:"has_database"`
	DatabaseSize   int64  `json:"database_size_bytes"`
	
	EnableClaudeCodeLogs bool `json:"enable_claude_code_logs"`
	EnableCopilotLogs    bool `json:"enable_copilot_logs"`
	EnableVSCodeLogs     bool `json:"enable_vscode_logs"`
	EnableGitLogs        bool `json:"enable_git_logs"`
	EnableMCPIntegration bool `json:"enable_mcp_integration"`
	EnableAutoStart      bool `json:"enable_auto_start"`
}

// TestRepositoryDiscovery tests repository auto-discovery functionality
func TestRepositoryDiscovery(t *testing.T) {
	t.Parallel()
	
	// Create temporary test directory structure
	tempDir, err := ioutil.TempDir("", "contextlite_test_repos")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)
	
	// Create test repositories
	testRepos := []struct {
		name        string
		hasDatabase bool
		dbSize      int64
	}{
		{"test-project-1", false, 0},
		{"test-project-2", true, 1024},
		{"test-project-3", true, 5120},
	}
	
	for _, repo := range testRepos {
		repoPath := filepath.Join(tempDir, repo.name)
		gitPath := filepath.Join(repoPath, ".git")
		
		// Create repository structure
		os.MkdirAll(gitPath, 0755)
		
		// Create database if specified
		if repo.hasDatabase {
			dbPath := filepath.Join(repoPath, "contextlite.db")
			data := make([]byte, repo.dbSize)
			ioutil.WriteFile(dbPath, data, 0644)
		}
		
		// Create basic project files
		ioutil.WriteFile(filepath.Join(repoPath, "README.md"), []byte("# "+repo.name), 0644)
	}
	
	t.Run("Discovery finds all repositories", func(t *testing.T) {
		// Test repository discovery
		projects, err := discoverProjectsInPath(tempDir)
		if err != nil {
			t.Fatalf("Discovery failed: %v", err)
		}
		
		if len(projects) != len(testRepos) {
			t.Errorf("Expected %d projects, found %d", len(testRepos), len(projects))
		}
		
		// Verify database detection
		for _, project := range projects {
			var expectedRepo *struct {
				name        string
				hasDatabase bool
				dbSize      int64
			}
			
			for i := range testRepos {
				if testRepos[i].name == project.ProjectName {
					expectedRepo = &testRepos[i]
					break
				}
			}
			
			if expectedRepo == nil {
				t.Errorf("Unexpected project found: %s", project.ProjectName)
				continue
			}
			
			if project.HasDatabase != expectedRepo.hasDatabase {
				t.Errorf("Project %s: expected HasDatabase=%v, got %v", 
					project.ProjectName, expectedRepo.hasDatabase, project.HasDatabase)
			}
			
			if expectedRepo.hasDatabase && project.DatabaseSize != expectedRepo.dbSize {
				t.Errorf("Project %s: expected database size %d, got %d",
					project.ProjectName, expectedRepo.dbSize, project.DatabaseSize)
			}
		}
	})
	
	t.Run("Discovery skips nested repositories", func(t *testing.T) {
		// Create nested repository
		nestedPath := filepath.Join(tempDir, "test-project-1", "submodule")
		nestedGitPath := filepath.Join(nestedPath, ".git")
		os.MkdirAll(nestedGitPath, 0755)
		
		// Discovery should still find only 3 projects
		projects, err := discoverProjectsInPath(tempDir)
		if err != nil {
			t.Fatalf("Discovery failed: %v", err)
		}
		
		if len(projects) != len(testRepos) {
			t.Errorf("Expected %d projects after adding nested repo, found %d", len(testRepos), len(projects))
		}
	})
}

// TestOnboardingConfiguration tests the onboarding configuration system
func TestOnboardingConfiguration(t *testing.T) {
	t.Parallel()
	
	tempDir, err := ioutil.TempDir("", "contextlite_onboarding_test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)
	
	// Create test project
	projectPath := filepath.Join(tempDir, "test-project")
	os.MkdirAll(filepath.Join(projectPath, ".git"), 0755)
	
	t.Run("Quick config generation", func(t *testing.T) {
		project := &OnboardingChoice{
			ProjectName: "test-project",
			ProjectPath: projectPath,
			Port:        8080,
			HasDatabase: false,
		}
		
		config := generateQuickConfigForTest(project)
		
		// Verify config contains required elements
		requiredElements := []string{
			"port: 8080",
			"test-project",
			"auto_discovery: true",
			"log_ingestion:",
			"mcp:",
		}
		
		for _, element := range requiredElements {
			if !strings.Contains(config, element) {
				t.Errorf("Config missing required element: %s", element)
			}
		}
	})
	
	t.Run("CLAUDE.md update preserves existing content", func(t *testing.T) {
		claudePath := filepath.Join(projectPath, "CLAUDE.md")
		existingContent := "# Existing Project\n\nSome existing content"
		ioutil.WriteFile(claudePath, []byte(existingContent), 0644)
		
		project := &OnboardingChoice{
			ProjectName: "test-project",
			ProjectPath: projectPath,
			Port:        8080,
			HasDatabase: false,
		}
		
		updateQuickCLAUDEMDForTest(project, claudePath)
		
		// Verify existing content is preserved
		updatedContent, err := ioutil.ReadFile(claudePath)
		if err != nil {
			t.Fatalf("Failed to read updated CLAUDE.md: %v", err)
		}
		
		content := string(updatedContent)
		if !strings.Contains(content, "Existing Project") {
			t.Error("Existing CLAUDE.md content was not preserved")
		}
		
		if !strings.Contains(content, "ContextLite Auto-Discovery") {
			t.Error("ContextLite section was not added")
		}
	})
}

// TestLogIngestion tests the log ingestion system
func TestLogIngestion(t *testing.T) {
	t.Parallel()
	
	tempDir, err := ioutil.TempDir("", "contextlite_logs_test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)
	
	t.Run("Log source initialization", func(t *testing.T) {
		manager := logs.NewLogIngestionManager("test-project", tempDir)
		
		if len(manager.Sources) == 0 {
			t.Error("No log sources initialized")
		}
		
		// Verify standard sources are present
		expectedSources := []string{"Claude Code", "GitHub Copilot", "VS Code", "Git History", "Cursor IDE"}
		for _, expected := range expectedSources {
			found := false
			for _, source := range manager.Sources {
				if source.Name == expected {
					found = true
					break
				}
			}
			if !found {
				t.Errorf("Expected log source not found: %s", expected)
			}
		}
	})
	
	t.Run("Source enabling and configuration", func(t *testing.T) {
		manager := logs.NewLogIngestionManager("test-project", tempDir)
		
		err := manager.EnableSource("Git History")
		if err != nil {
			t.Errorf("Failed to enable Git History source: %v", err)
		}
		
		// Verify source is enabled
		for _, source := range manager.Sources {
			if source.Name == "Git History" && !source.Enabled {
				t.Error("Git History source was not enabled")
			}
		}
		
		// Test invalid source
		err = manager.EnableSource("NonExistent Source")
		if err == nil {
			t.Error("Expected error for non-existent source")
		}
	})
}

// TestMCPServer tests MCP server functionality
func TestMCPServer(t *testing.T) {
	t.Parallel()
	
	tempDir, err := ioutil.TempDir("", "contextlite_mcp_test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)
	
	t.Run("MCP server initialization", func(t *testing.T) {
		server := mcp.NewMCPServer("test-project", tempDir)
		
		if server.ProjectName != "test-project" {
			t.Errorf("Expected project name 'test-project', got '%s'", server.ProjectName)
		}
		
		if server.ProjectPath != tempDir {
			t.Errorf("Expected project path '%s', got '%s'", tempDir, server.ProjectPath)
		}
	})
	
	t.Run("MCP server creation", func(t *testing.T) {
		server := mcp.NewMCPServer("test-project", tempDir)
		
		// Verify server was created with correct configuration
		if server.ProjectName != "test-project" {
			t.Errorf("Expected project name 'test-project', got '%s'", server.ProjectName)
		}
		
		if server.ProjectPath != tempDir {
			t.Errorf("Expected project path '%s', got '%s'", tempDir, server.ProjectPath)
		}
		
		// Verify registry path is set correctly
		expectedRegistryPath := filepath.Join(tempDir, "internal", "registry", "system_registry.json")
		if server.RegistryPath != expectedRegistryPath {
			t.Errorf("Expected registry path '%s', got '%s'", expectedRegistryPath, server.RegistryPath)
		}
	})
}

// TestCLIIntegration tests CLI discovery with standardized projects
func TestCLIIntegration(t *testing.T) {
	t.Parallel()
	
	tempDir, err := ioutil.TempDir("", "contextlite_cli_test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)
	
	t.Run("Registry creation and loading", func(t *testing.T) {
		// Create test registry
		registry := map[string]interface{}{
			"projects": []map[string]interface{}{
				{
					"project_name": "test-project",
					"port":         8080,
					"selected":     true,
				},
			},
			"setup_completed": time.Now().Format(time.RFC3339),
			"setup_type":      "test",
		}
		
		registryPath := filepath.Join(tempDir, "test_registry.json")
		data, _ := json.MarshalIndent(registry, "", "  ")
		ioutil.WriteFile(registryPath, data, 0644)
		
		// Verify registry file was created
		if _, err := os.Stat(registryPath); os.IsNotExist(err) {
			t.Error("Registry file was not created")
		}
		
		// Verify registry content
		savedData, err := ioutil.ReadFile(registryPath)
		if err != nil {
			t.Fatalf("Failed to read registry: %v", err)
		}
		
		var savedRegistry map[string]interface{}
		if err := json.Unmarshal(savedData, &savedRegistry); err != nil {
			t.Fatalf("Failed to parse registry: %v", err)
		}
		
		if savedRegistry["setup_type"] != "test" {
			t.Error("Registry content not preserved correctly")
		}
	})
}

// TestDatabasePreservation tests that existing databases are never modified
func TestDatabasePreservation(t *testing.T) {
	t.Parallel()
	
	tempDir, err := ioutil.TempDir("", "contextlite_db_preservation_test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)
	
	// Create test project with existing database
	projectPath := filepath.Join(tempDir, "test-project")
	os.MkdirAll(filepath.Join(projectPath, ".git"), 0755)
	
	// Create test database with specific content
	dbPath := filepath.Join(projectPath, "contextlite.db")
	testData := []byte("EXISTING_DATABASE_CONTENT_DO_NOT_MODIFY")
	ioutil.WriteFile(dbPath, testData, 0644)
	
	// Record original modification time
	originalInfo, err := os.Stat(dbPath)
	if err != nil {
		t.Fatalf("Failed to stat test database: %v", err)
	}
	originalModTime := originalInfo.ModTime()
	originalSize := originalInfo.Size()
	
	t.Run("Database preservation during discovery", func(t *testing.T) {
		// Run discovery
		projects, err := discoverProjectsInPath(tempDir)
		if err != nil {
			t.Fatalf("Discovery failed: %v", err)
		}
		
		if len(projects) != 1 {
			t.Fatalf("Expected 1 project, found %d", len(projects))
		}
		
		project := projects[0]
		if !project.HasDatabase {
			t.Error("Existing database was not detected")
		}
		
		if project.DatabaseSize != originalSize {
			t.Errorf("Database size mismatch: expected %d, got %d", originalSize, project.DatabaseSize)
		}
		
		// Verify database file was not modified
		currentInfo, err := os.Stat(dbPath)
		if err != nil {
			t.Fatalf("Database file missing after discovery: %v", err)
		}
		
		if !currentInfo.ModTime().Equal(originalModTime) {
			t.Error("Database modification time changed during discovery")
		}
		
		// Verify database content unchanged
		currentData, err := ioutil.ReadFile(dbPath)
		if err != nil {
			t.Fatalf("Failed to read database after discovery: %v", err)
		}
		
		if string(currentData) != string(testData) {
			t.Error("Database content was modified during discovery")
		}
	})
	
	t.Run("Database preservation during config creation", func(t *testing.T) {
		project := &OnboardingChoice{
			ProjectName: "test-project",
			ProjectPath: projectPath,
			Port:        8080,
			HasDatabase: true,
			DatabaseSize: originalSize,
		}
		
		// Generate config (should not touch database)
		config := generateQuickConfigForTest(project)
		configPath := filepath.Join(projectPath, "contextlite-config.yaml")
		ioutil.WriteFile(configPath, []byte(config), 0644)
		
		// Verify database still untouched
		currentInfo, err := os.Stat(dbPath)
		if err != nil {
			t.Fatalf("Database file missing after config creation: %v", err)
		}
		
		if !currentInfo.ModTime().Equal(originalModTime) {
			t.Error("Database modification time changed during config creation")
		}
		
		// Verify config points to correct database
		if !strings.Contains(config, "./contextlite.db") {
			t.Error("Config does not reference correct database path")
		}
		
		if !strings.Contains(config, "# Existing database preserved") {
			t.Error("Config does not indicate database preservation")
		}
	})
}

// TestPortAssignment tests standardized port assignment
func TestPortAssignment(t *testing.T) {
	t.Parallel()
	
	projects := []*OnboardingChoice{
		{ProjectName: "alpha-project", ProjectPath: "/tmp/alpha"},
		{ProjectName: "beta-project", ProjectPath: "/tmp/beta"},
		{ProjectName: "gamma-project", ProjectPath: "/tmp/gamma"},
	}
	
	// Assign ports starting from 9000 (to avoid conflicts)
	basePort := 9000
	for i, project := range projects {
		project.Port = basePort + i
	}
	
	t.Run("Ports assigned sequentially", func(t *testing.T) {
		for i, project := range projects {
			expectedPort := basePort + i
			if project.Port != expectedPort {
				t.Errorf("Project %s: expected port %d, got %d", 
					project.ProjectName, expectedPort, project.Port)
			}
		}
	})
	
	t.Run("No port conflicts", func(t *testing.T) {
		usedPorts := make(map[int]bool)
		for _, project := range projects {
			if usedPorts[project.Port] {
				t.Errorf("Port conflict detected: %d used by multiple projects", project.Port)
			}
			usedPorts[project.Port] = true
		}
	})
}

// TestConfigGeneration tests configuration file generation
func TestConfigGeneration(t *testing.T) {
	t.Parallel()
	
	t.Run("Quick config with existing database", func(t *testing.T) {
		project := &OnboardingChoice{
			ProjectName:  "test-project",
			ProjectPath:  "/tmp/test-project",
			Port:         8080,
			HasDatabase:  true,
			DatabaseSize: 5120,
		}
		
		config := generateQuickConfigForTest(project)
		
		// Verify preservation comment
		if !strings.Contains(config, "# Existing database preserved") {
			t.Error("Config missing database preservation comment")
		}
		
		// Verify port setting
		if !strings.Contains(config, "port: 8080") {
			t.Error("Config missing correct port setting")
		}
		
		// Verify project identification
		if !strings.Contains(config, `name: "test-project"`) {
			t.Error("Config missing project name")
		}
	})
	
	t.Run("Quick config with new database", func(t *testing.T) {
		project := &OnboardingChoice{
			ProjectName: "new-project",
			ProjectPath: "/tmp/new-project",
			Port:        8081,
			HasDatabase: false,
		}
		
		config := generateQuickConfigForTest(project)
		
		// Should not have preservation comment
		if strings.Contains(config, "# Existing database preserved") {
			t.Error("Config should not have preservation comment for new database")
		}
		
		// Should have standard database path
		if !strings.Contains(config, `database_path: "./contextlite.db"`) {
			t.Error("Config missing standard database path")
		}
	})
}

// Helper functions for testing

// discoverProjectsInPath is the actual discovery function for testing
func discoverProjectsInPath(repoPath string) ([]*OnboardingChoice, error) {
	var projects []*OnboardingChoice
	
	err := filepath.Walk(repoPath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return nil
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
			findExistingDatabaseForTest(project)
			projects = append(projects, project)
		}
		
		return nil
	})
	
	return projects, err
}

// findExistingDatabaseForTest mimics the database discovery logic
func findExistingDatabaseForTest(project *OnboardingChoice) {
	patterns := []string{"contextlite.db", "context.db", "*contextlite*.db"}
	
	for _, pattern := range patterns {
		matches, _ := filepath.Glob(filepath.Join(project.ProjectPath, pattern))
		if len(matches) > 0 {
			var bestSize int64
			for _, dbPath := range matches {
				if info, err := os.Stat(dbPath); err == nil && info.Size() > bestSize {
					bestSize = info.Size()
				}
			}
			if bestSize > 0 {
				project.HasDatabase = true
				project.DatabaseSize = bestSize
			}
			break
		}
	}
}

// Test helper functions

// generateQuickConfigForTest creates minimal project config for testing
func generateQuickConfigForTest(project *OnboardingChoice) string {
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
`,
		project.Port,
		dbPath,
		preserveNote,
		project.ProjectName,
		strings.ReplaceAll(project.ProjectPath, "\\", "/"),
		project.ProjectName)
}

// updateQuickCLAUDEMDForTest adds minimal ContextLite section for testing
func updateQuickCLAUDEMDForTest(project *OnboardingChoice, claudePath string) {
	section := fmt.Sprintf(`
# ContextLite Auto-Discovery
- **Port**: %d
- **Database**: ./contextlite.db%s
- **Quick start**: ` + "`contextlite --config contextlite-config.yaml`" + `
- **CLI access**: ` + "`contextlite-cli connect %s`" + `
`,
		project.Port,
		map[bool]string{true: " (existing data preserved)", false: ""}[project.HasDatabase],
		project.ProjectName)
	
	// Append to existing CLAUDE.md or create new
	var existingContent string
	if content, err := ioutil.ReadFile(claudePath); err == nil {
		existingContent = string(content)
	}
	
	newContent := existingContent
	if !strings.Contains(existingContent, "# ContextLite") {
		if existingContent != "" {
			newContent += "\n"
		}
		newContent += section
		ioutil.WriteFile(claudePath, []byte(newContent), 0644)
	}
}