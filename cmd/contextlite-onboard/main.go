package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"io/ioutil"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"time"
)

// secureReadInput reads user input with timeout and validation
func secureReadInput(reader *bufio.Reader, prompt string, timeout time.Duration) (string, error) {
	fmt.Print(prompt)
	
	// Create a channel to receive input
	inputChan := make(chan string, 1)
	errorChan := make(chan error, 1)
	
	go func() {
		input, err := reader.ReadString('\n')
		if err != nil {
			errorChan <- err
			return
		}
		inputChan <- input
	}()
	
	// Wait for input or timeout
	select {
	case input := <-inputChan:
		// SECURITY: Sanitize input
		sanitized := strings.TrimSpace(input)
		
		// SECURITY: Reject control characters and dangerous sequences
		controlPattern := regexp.MustCompile(`[\x00-\x1F\x7F]`)
		if controlPattern.MatchString(sanitized) {
			return "", fmt.Errorf("input contains invalid control characters")
		}
		
		// SECURITY: Length limit
		if len(sanitized) > 500 {
			sanitized = sanitized[:500]
		}
		
		return sanitized, nil
		
	case err := <-errorChan:
		return "", err
		
	case <-time.After(timeout):
		return "", fmt.Errorf("input timeout exceeded")
	}
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

// OnboardingSession manages the interactive setup process
type OnboardingSession struct {
	DiscoveredProjects []*OnboardingChoice `json:"discovered_projects"`
	UserChoices        []*OnboardingChoice `json:"user_choices"`
	GlobalSettings     *GlobalSettings     `json:"global_settings"`
	SessionStartTime   time.Time          `json:"session_start_time"`
}

// GlobalSettings for system-wide preferences
type GlobalSettings struct {
	RepositoriesPath   string `json:"repositories_path"`
	BasePort          int    `json:"base_port"`
	AutoImportInterval string `json:"auto_import_interval"` // "on_exit", "hourly", "daily"
	DefaultIntegrations struct {
		ClaudeCode bool `json:"claude_code"`
		Copilot    bool `json:"copilot"`
		VSCode     bool `json:"vscode"`
		Git        bool `json:"git"`
		MCP        bool `json:"mcp"`
	} `json:"default_integrations"`
}

func main() {
	fmt.Println("🚀 ContextLite Interactive Onboarding")
	fmt.Println("=====================================")
	fmt.Println()
	
	session := &OnboardingSession{
		SessionStartTime: time.Now(),
		GlobalSettings: &GlobalSettings{
			BasePort: 8080,
			AutoImportInterval: "on_exit",
		},
	}
	
	// Step 1: Configure global settings
	if err := configureGlobalSettings(session); err != nil {
		fmt.Printf("❌ Configuration failed: %v\n", err)
		os.Exit(1)
	}
	
	// Step 2: Auto-discover repositories
	if err := discoverRepositories(session); err != nil {
		fmt.Printf("❌ Discovery failed: %v\n", err)
		os.Exit(1)
	}
	
	// Step 3: User selection interface
	if err := userSelectionInterface(session); err != nil {
		fmt.Printf("❌ Selection failed: %v\n", err)
		os.Exit(1)
	}
	
	// Step 4: Integration choices
	if err := integrationChoicesInterface(session); err != nil {
		fmt.Printf("❌ Integration setup failed: %v\n", err)
		os.Exit(1)
	}
	
	// Step 5: Confirmation and execution
	if err := confirmAndExecute(session); err != nil {
		fmt.Printf("❌ Setup execution failed: %v\n", err)
		os.Exit(1)
	}
	
	fmt.Println("\n🎉 ContextLite onboarding complete!")
	fmt.Println("Your development intelligence platform is ready.")
}

// configureGlobalSettings handles system-wide preferences
func configureGlobalSettings(session *OnboardingSession) error {
	fmt.Println("⚙️ Global Configuration")
	fmt.Println("========================")
	
	reader := bufio.NewReader(os.Stdin)
	
	// Repository path configuration
	homeDir, _ := os.UserHomeDir()
	defaultRepoPath := filepath.Join(homeDir, "repos")
	if runtime.GOOS == "windows" {
		defaultRepoPath = `C:\Users\` + os.Getenv("USERNAME") + `\repos`
	}
	
	fmt.Printf("📁 Where are your repositories located? [%s]: ", defaultRepoPath)
	repoPath, _ := reader.ReadString('\n')
	repoPath = strings.TrimSpace(repoPath)
	if repoPath == "" {
		repoPath = defaultRepoPath
	}
	
	session.GlobalSettings.RepositoriesPath = repoPath
	
	// Base port configuration
	fmt.Print("🌐 Starting port for ContextLite instances [8080]: ")
	portInput, _ := reader.ReadString('\n')
	portInput = strings.TrimSpace(portInput)
	if portInput != "" {
		if port, err := strconv.Atoi(portInput); err == nil {
			session.GlobalSettings.BasePort = port
		}
	}
	
	// Auto-import frequency
	fmt.Println("\n📥 When should ContextLite import development logs?")
	fmt.Println("   1. On tool exit/close (recommended)")
	fmt.Println("   2. Hourly in background")
	fmt.Println("   3. Daily overnight")
	fmt.Print("Choice [1]: ")
	
	choice, _ := reader.ReadString('\n')
	choice = strings.TrimSpace(choice)
	switch choice {
	case "2":
		session.GlobalSettings.AutoImportInterval = "hourly"
	case "3":
		session.GlobalSettings.AutoImportInterval = "daily"
	default:
		session.GlobalSettings.AutoImportInterval = "on_exit"
	}
	
	fmt.Println("✅ Global settings configured")
	return nil
}

// discoverRepositories scans for Git repositories
func discoverRepositories(session *OnboardingSession) error {
	fmt.Println("\n🔍 Repository Discovery")
	fmt.Println("=======================")
	fmt.Printf("Scanning: %s\n", session.GlobalSettings.RepositoriesPath)
	
	var discovered []*OnboardingChoice
	
	err := filepath.Walk(session.GlobalSettings.RepositoriesPath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return nil // Skip errors
		}
		
		// Look for .git directories
		if info.IsDir() && info.Name() == ".git" {
			projectPath := filepath.Dir(path)
			projectName := filepath.Base(projectPath)
			
			// Skip nested .git directories
			relPath, _ := filepath.Rel(session.GlobalSettings.RepositoriesPath, projectPath)
			if strings.Contains(relPath, string(filepath.Separator)) {
				return nil
			}
			
			choice := &OnboardingChoice{
				ProjectName: projectName,
				ProjectPath: projectPath,
				Selected:    true, // Default to selected
			}
			
			// Check for existing ContextLite database
			findExistingDatabase(choice)
			
			discovered = append(discovered, choice)
			fmt.Printf("   📁 %s", projectName)
			if choice.HasDatabase {
				fmt.Printf(" (existing database: %.1fKB)", float64(choice.DatabaseSize)/1024)
			}
			fmt.Println()
		}
		
		return nil
	})
	
	if err != nil {
		return fmt.Errorf("repository scan failed: %w", err)
	}
	
	// Sort by name for consistent display
	sort.Slice(discovered, func(i, j int) bool {
		return discovered[i].ProjectName < discovered[j].ProjectName
	})
	
	session.DiscoveredProjects = discovered
	fmt.Printf("✅ Discovered %d repositories\n", len(discovered))
	return nil
}

// findExistingDatabase looks for existing ContextLite databases
func findExistingDatabase(choice *OnboardingChoice) {
	patterns := []string{
		"contextlite.db",
		"context.db",
		"contextlite_fresh.db",
		"*contextlite*.db",
	}
	
	for _, pattern := range patterns {
		matches, _ := filepath.Glob(filepath.Join(choice.ProjectPath, pattern))
		if len(matches) > 0 {
			// Use the largest database
			var bestDB string
			var bestSize int64
			
			for _, dbPath := range matches {
				if info, err := os.Stat(dbPath); err == nil {
					if info.Size() > bestSize {
						bestDB = dbPath
						bestSize = info.Size()
					}
				}
			}
			
			if bestDB != "" {
				choice.HasDatabase = true
				choice.DatabaseSize = bestSize
			}
			break
		}
	}
}

// userSelectionInterface handles project selection
func userSelectionInterface(session *OnboardingSession) error {
	fmt.Println("\n📋 Project Selection")
	fmt.Println("====================")
	fmt.Println("Select which repositories to include in ContextLite:")
	fmt.Println()
	
	reader := bufio.NewReader(os.Stdin)
	
	// Display all discovered projects with numbers
	for i, project := range session.DiscoveredProjects {
		status := "[ ]"
		if project.Selected {
			status = "[✓]"
		}
		
		fmt.Printf("  %2d. %s %-25s", i+1, status, project.ProjectName)
		if project.HasDatabase {
			fmt.Printf(" (existing: %.1fKB)", float64(project.DatabaseSize)/1024)
		}
		fmt.Println()
	}
	
	fmt.Println()
	fmt.Println("Commands:")
	fmt.Println("  1-N     : Toggle project N")
	fmt.Println("  all     : Select all projects")
	fmt.Println("  none    : Deselect all projects")
	fmt.Println("  done    : Continue with selected projects")
	fmt.Println()
	
	for {
		fmt.Print("Selection: ")
		input, _ := reader.ReadString('\n')
		input = strings.TrimSpace(input)
		
		switch input {
		case "done":
			// Count selected projects
			selectedCount := 0
			for _, project := range session.DiscoveredProjects {
				if project.Selected {
					selectedCount++
				}
			}
			
			if selectedCount == 0 {
				fmt.Println("❌ No projects selected. Please select at least one project.")
				continue
			}
			
			fmt.Printf("✅ %d projects selected for ContextLite integration\n", selectedCount)
			return nil
			
		case "all":
			for _, project := range session.DiscoveredProjects {
				project.Selected = true
			}
			fmt.Println("✅ All projects selected")
			
		case "none":
			for _, project := range session.DiscoveredProjects {
				project.Selected = false
			}
			fmt.Println("✅ All projects deselected")
			
		default:
			// Try to parse as project number
			if num, err := strconv.Atoi(input); err == nil && num >= 1 && num <= len(session.DiscoveredProjects) {
				project := session.DiscoveredProjects[num-1]
				project.Selected = !project.Selected
				
				action := "selected"
				if !project.Selected {
					action = "deselected"
				}
				fmt.Printf("✅ %s %s\n", project.ProjectName, action)
			} else {
				fmt.Println("❌ Invalid input. Use project numbers, 'all', 'none', or 'done'")
			}
		}
		
		// Redisplay current selections
		fmt.Println("\nCurrent selections:")
		for i, project := range session.DiscoveredProjects {
			if project.Selected {
				fmt.Printf("  ✓ %d. %s\n", i+1, project.ProjectName)
			}
		}
		fmt.Println()
	}
}

// integrationChoicesInterface handles integration preferences
func integrationChoicesInterface(session *OnboardingSession) error {
	fmt.Println("\n🔌 Integration Preferences")
	fmt.Println("==========================")
	fmt.Println("Configure development tool integration:")
	fmt.Println()
	
	reader := bufio.NewReader(os.Stdin)
	
	// Global defaults first
	fmt.Println("Set default integration preferences (applied to all selected projects):")
	fmt.Println()
	
	integrations := []struct {
		name        string
		description string
		field       *bool
	}{
		{"Claude Code Logs", "Import Claude Code conversation and command history", &session.GlobalSettings.DefaultIntegrations.ClaudeCode},
		{"GitHub Copilot Logs", "Import Copilot suggestions and acceptance history", &session.GlobalSettings.DefaultIntegrations.Copilot},
		{"VS Code Activity", "Import workspace activity, extensions, and debug logs", &session.GlobalSettings.DefaultIntegrations.VSCode},
		{"Git History", "Import commit messages, branch activity, and repository events", &session.GlobalSettings.DefaultIntegrations.Git},
		{"MCP Integration", "Expose project context to Claude Code via Model Context Protocol", &session.GlobalSettings.DefaultIntegrations.MCP},
	}
	
	for _, integration := range integrations {
		fmt.Printf("📊 %s\n", integration.name)
		fmt.Printf("   %s\n", integration.description)
		fmt.Print("   Enable by default? [Y/n]: ")
		
		input, _ := reader.ReadString('\n')
		input = strings.TrimSpace(strings.ToLower(input))
		*integration.field = input != "n" && input != "no"
		
		if *integration.field {
			fmt.Println("   ✅ Enabled")
		} else {
			fmt.Println("   ❌ Disabled")
		}
		fmt.Println()
	}
	
	// Apply defaults to selected projects
	for _, project := range session.DiscoveredProjects {
		if project.Selected {
			project.EnableClaudeCodeLogs = session.GlobalSettings.DefaultIntegrations.ClaudeCode
			project.EnableCopilotLogs = session.GlobalSettings.DefaultIntegrations.Copilot
			project.EnableVSCodeLogs = session.GlobalSettings.DefaultIntegrations.VSCode
			project.EnableGitLogs = session.GlobalSettings.DefaultIntegrations.Git
			project.EnableMCPIntegration = session.GlobalSettings.DefaultIntegrations.MCP
			project.EnableAutoStart = true // Default to auto-start
		}
	}
	
	// Ask if user wants to customize per-project
	fmt.Print("🎯 Customize integration settings per project? [y/N]: ")
	input, _ := reader.ReadString('\n')
	input = strings.TrimSpace(strings.ToLower(input))
	
	if input == "y" || input == "yes" {
		return customizeProjectIntegrations(session)
	}
	
	fmt.Println("✅ Using default integration settings for all projects")
	return nil
}

// customizeProjectIntegrations allows per-project customization
func customizeProjectIntegrations(session *OnboardingSession) error {
	reader := bufio.NewReader(os.Stdin)
	
	fmt.Println("\n🎨 Per-Project Customization")
	fmt.Println("=============================")
	
	for _, project := range session.DiscoveredProjects {
		if !project.Selected {
			continue
		}
		
		fmt.Printf("\n📁 Project: %s\n", project.ProjectName)
		if project.HasDatabase {
			fmt.Printf("   Existing database: %.1fKB (will be preserved)\n", float64(project.DatabaseSize)/1024)
		}
		
		fmt.Println("   Current integrations:")
		fmt.Printf("     Claude Code Logs: %v\n", project.EnableClaudeCodeLogs)
		fmt.Printf("     Copilot Logs: %v\n", project.EnableCopilotLogs)
		fmt.Printf("     VS Code Activity: %v\n", project.EnableVSCodeLogs)
		fmt.Printf("     Git History: %v\n", project.EnableGitLogs)
		fmt.Printf("     MCP Integration: %v\n", project.EnableMCPIntegration)
		
		fmt.Print("   Customize this project? [y/N]: ")
		input, _ := reader.ReadString('\n')
		input = strings.TrimSpace(strings.ToLower(input))
		
		if input == "y" || input == "yes" {
			// Allow toggling each integration
			integrations := []struct {
				name  string
				field *bool
			}{
				{"Claude Code Logs", &project.EnableClaudeCodeLogs},
				{"Copilot Logs", &project.EnableCopilotLogs},
				{"VS Code Activity", &project.EnableVSCodeLogs},
				{"Git History", &project.EnableGitLogs},
				{"MCP Integration", &project.EnableMCPIntegration},
			}
			
			for _, integration := range integrations {
				current := "disabled"
				if *integration.field {
					current = "enabled"
				}
				
				fmt.Printf("     %s (currently %s) - toggle? [y/N]: ", integration.name, current)
				input, _ := reader.ReadString('\n')
				input = strings.TrimSpace(strings.ToLower(input))
				
				if input == "y" || input == "yes" {
					*integration.field = !*integration.field
				}
			}
		}
	}
	
	return nil
}

// confirmAndExecute shows final configuration and executes setup
func confirmAndExecute(session *OnboardingSession) error {
	fmt.Println("\n📋 Setup Summary")
	fmt.Println("==================")
	
	selectedProjects := []*OnboardingChoice{}
	for _, project := range session.DiscoveredProjects {
		if project.Selected {
			selectedProjects = append(selectedProjects, project)
		}
	}
	
	fmt.Printf("Repository Path: %s\n", session.GlobalSettings.RepositoriesPath)
	fmt.Printf("Selected Projects: %d\n", len(selectedProjects))
	fmt.Printf("Port Range: %d-%d\n", session.GlobalSettings.BasePort, session.GlobalSettings.BasePort+len(selectedProjects)-1)
	fmt.Printf("Log Import: %s\n", session.GlobalSettings.AutoImportInterval)
	
	fmt.Println("\nSelected Projects:")
	currentPort := session.GlobalSettings.BasePort
	for _, project := range selectedProjects {
		project.Port = currentPort
		fmt.Printf("  📁 %-25s Port: %d", project.ProjectName, project.Port)
		
		var integrations []string
		if project.EnableClaudeCodeLogs { integrations = append(integrations, "Claude") }
		if project.EnableCopilotLogs { integrations = append(integrations, "Copilot") }
		if project.EnableVSCodeLogs { integrations = append(integrations, "VSCode") }
		if project.EnableGitLogs { integrations = append(integrations, "Git") }
		if project.EnableMCPIntegration { integrations = append(integrations, "MCP") }
		
		if len(integrations) > 0 {
			fmt.Printf(" [%s]", strings.Join(integrations, ", "))
		}
		
		if project.HasDatabase {
			fmt.Printf(" (preserving %.1fKB)", float64(project.DatabaseSize)/1024)
		}
		fmt.Println()
		currentPort++
	}
	
	session.UserChoices = selectedProjects
	
	reader := bufio.NewReader(os.Stdin)
	fmt.Print("\n🚀 Proceed with setup? [Y/n]: ")
	input, _ := reader.ReadString('\n')
	input = strings.TrimSpace(strings.ToLower(input))
	
	if input == "n" || input == "no" {
		fmt.Println("❌ Setup cancelled by user")
		return fmt.Errorf("setup cancelled")
	}
	
	fmt.Println("\n⚡ Executing setup...")
	
	// Save session for progress tracking
	if err := saveSession(session); err != nil {
		return fmt.Errorf("failed to save session: %w", err)
	}
	
	// Execute the actual setup
	return executeSetup(session)
}

// executeSetup performs the actual ContextLite configuration
func executeSetup(session *OnboardingSession) error {
	fmt.Println("🔧 Creating project configurations...")
	
	// Create .contextlite directory
	homeDir, _ := os.UserHomeDir()
	contextliteDir := filepath.Join(homeDir, ".contextlite")
	os.MkdirAll(contextliteDir, 0755)
	
	configCount := 0
	claudeCount := 0
	
	for _, project := range session.UserChoices {
		// Create project-specific config
		configPath := filepath.Join(project.ProjectPath, "contextlite-config.yaml")
		configContent := generateProjectConfig(project, session.GlobalSettings.AutoImportInterval)
		
		if err := ioutil.WriteFile(configPath, []byte(configContent), 0644); err != nil {
			fmt.Printf("   ❌ Config failed: %s\n", project.ProjectName)
			continue
		}
		configCount++
		
		// Update CLAUDE.md
		claudePath := filepath.Join(project.ProjectPath, "CLAUDE.md")
		if err := updateCLAUDEMD(project, claudePath); err != nil {
			fmt.Printf("   ❌ CLAUDE.md failed: %s\n", project.ProjectName)
			continue
		}
		claudeCount++
		
		fmt.Printf("   ✅ %s\n", project.ProjectName)
	}
	
	// Save project registry
	registryPath := filepath.Join(contextliteDir, "onboarding_registry.json")
	if err := saveProjectRegistry(session, registryPath); err != nil {
		return fmt.Errorf("failed to save registry: %w", err)
	}
	
	fmt.Printf("✅ Created %d configs, updated %d CLAUDE.md files\n", configCount, claudeCount)
	fmt.Printf("📄 Registry saved: %s\n", registryPath)
	
	return nil
}

// generateProjectConfig creates standardized config content
func generateProjectConfig(project *OnboardingChoice, autoImportInterval string) string {
	dbPath := strings.ReplaceAll(project.ProjectPath, "\\", "/") + "/contextlite.db"
	if project.HasDatabase {
		// Use existing database path (already in ProjectPath)
		dbPath = strings.ReplaceAll(project.ProjectPath, "\\", "/") + "/contextlite.db"
	}
	
	return fmt.Sprintf(`# ContextLite Configuration for %s
server:
  port: %d
  host: "127.0.0.1"
  cors_enabled: false
  
storage:
  database_path: "%s"
  cache_size_mb: 64
  
# Log ingestion settings
log_ingestion:
  claude_code: %v
  copilot: %v
  vscode: %v
  git: %v
  interval: "%s"
  
# MCP integration
mcp:
  enabled: %v
  server_name: "%s-mcp"
  
smt:
  solver_timeout_ms: 250
  max_opt_gap: 0.05
  
logging:
  level: "info"
  include_timings: true

# Project identification
project:
  name: "%s"
  path: "%s"
`,
		project.ProjectName,
		project.Port,
		dbPath,
		project.EnableClaudeCodeLogs,
		project.EnableCopilotLogs,
		project.EnableVSCodeLogs,
		project.EnableGitLogs,
		autoImportInterval,
		project.EnableMCPIntegration,
		project.ProjectName,
		project.ProjectName,
		strings.ReplaceAll(project.ProjectPath, "\\", "/"))
}

// updateCLAUDEMD adds ContextLite section to CLAUDE.md
func updateCLAUDEMD(project *OnboardingChoice, claudePath string) error {
	var existingContent string
	if content, err := ioutil.ReadFile(claudePath); err == nil {
		existingContent = string(content)
	}
	
	// Generate ContextLite section
	contextliteSection := generateContextLiteSection(project)
	
	// Remove old ContextLite section if it exists
	newContent := removeOldContextLiteSection(existingContent)
	if newContent != "" {
		newContent += "\n\n"
	}
	newContent += contextliteSection
	
	return ioutil.WriteFile(claudePath, []byte(newContent), 0644)
}

// generateContextLiteSection creates the CLAUDE.md section
func generateContextLiteSection(project *OnboardingChoice) string {
	dbStatus := "🆕 Ready for initialization"
	if project.HasDatabase {
		dbStatus = "✅ Preserved existing data"
	}
	
	var integrations []string
	if project.EnableClaudeCodeLogs { integrations = append(integrations, "Claude Code logs") }
	if project.EnableCopilotLogs { integrations = append(integrations, "Copilot logs") }
	if project.EnableVSCodeLogs { integrations = append(integrations, "VS Code activity") }
	if project.EnableGitLogs { integrations = append(integrations, "Git history") }
	if project.EnableMCPIntegration { integrations = append(integrations, "MCP integration") }
	
	integrationsText := "None configured"
	if len(integrations) > 0 {
		integrationsText = strings.Join(integrations, ", ")
	}
	
	return fmt.Sprintf(`# ContextLite Configuration

## Project Setup
- **Project**: %s
- **Port**: %d
- **Database**: %s
- **Integrations**: %s

## Quick Commands
` + "```bash" + `
# Start ContextLite for this project
contextlite --config contextlite-config.yaml

# Connect via CLI
contextlite-cli connect %s

# Query this project's context
contextlite-cli query %s "search terms"
` + "```" + `

## Integration Status
- Port assignment: ✅ Standardized
- Database: %s
- Auto-discovery: ✅ Enabled
- Log ingestion: ✅ Configured`,
		project.ProjectName,
		project.Port,
		"./contextlite.db",
		integrationsText,
		project.ProjectName,
		project.ProjectName,
		dbStatus)
}

// removeOldContextLiteSection removes existing ContextLite sections
func removeOldContextLiteSection(content string) string {
	if content == "" {
		return ""
	}
	
	lines := strings.Split(content, "\n")
	var filtered []string
	inContextLiteSection := false
	
	for _, line := range lines {
		if strings.Contains(line, "# ContextLite") || strings.Contains(line, "## ContextLite") {
			inContextLiteSection = true
			continue
		}
		
		if inContextLiteSection && strings.HasPrefix(line, "#") && !strings.Contains(line, "ContextLite") {
			inContextLiteSection = false
		}
		
		if !inContextLiteSection {
			filtered = append(filtered, line)
		}
	}
	
	return strings.TrimSpace(strings.Join(filtered, "\n"))
}

// saveSession saves onboarding session for progress tracking
func saveSession(session *OnboardingSession) error {
	homeDir, _ := os.UserHomeDir()
	sessionPath := filepath.Join(homeDir, ".contextlite", "onboarding_session.json")
	
	data, err := json.MarshalIndent(session, "", "  ")
	if err != nil {
		return err
	}
	
	return ioutil.WriteFile(sessionPath, data, 0644)
}

// saveProjectRegistry saves final project registry
func saveProjectRegistry(session *OnboardingSession, registryPath string) error {
	registry := map[string]interface{}{
		"projects":          session.UserChoices,
		"global_settings":   session.GlobalSettings,
		"setup_completed":   time.Now().Format(time.RFC3339),
		"onboarding_version": "2.0",
	}
	
	data, err := json.MarshalIndent(registry, "", "  ")
	if err != nil {
		return err
	}
	
	return ioutil.WriteFile(registryPath, data, 0644)
}