package main

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"time"
)

// ProjectConfig represents a ContextLite project configuration
type ProjectConfig struct {
	ProjectName    string `json:"project_name"`
	ProjectPath    string `json:"project_path"`
	DatabasePath   string `json:"database_path"`
	ConfigPath     string `json:"config_path"`
	Port           int    `json:"port"`
	Discovered     bool   `json:"discovered"`
	HasDatabase    bool   `json:"has_database"`
	DatabaseSize   int64  `json:"database_size_bytes"`
}

// ProjectRegistry manages all ContextLite projects
type ProjectRegistry struct {
	Projects        map[string]*ProjectConfig `json:"projects"`
	NextPort        int                       `json:"next_port"`
	LastUpdated     string                    `json:"last_updated"`
	RegistryVersion string                    `json:"registry_version"`
}

// ContextLiteSetup handles system-wide setup and standardization
type ContextLiteSetup struct {
	reposPath    string
	registryPath string
	basePort     int
	registry     *ProjectRegistry
}

// NewSetup creates a new setup manager
func NewSetup() *ContextLiteSetup {
	homeDir, _ := os.UserHomeDir()
	contextliteDir := filepath.Join(homeDir, ".contextlite")
	os.MkdirAll(contextliteDir, 0755)
	
	return &ContextLiteSetup{
		reposPath:    `C:\Users\micha\repos`,
		registryPath: filepath.Join(contextliteDir, "project_registry.json"),
		basePort:     8080,
		registry:     &ProjectRegistry{Projects: make(map[string]*ProjectConfig)},
	}
}

// DiscoverProjects finds all Git repositories and existing ContextLite databases
func (s *ContextLiteSetup) DiscoverProjects() error {
	fmt.Println("🔍 Discovering Git repositories and ContextLite databases...")
	
	err := filepath.Walk(s.reposPath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return nil // Skip errors
		}
		
		// Look for .git directories (indicates a Git repo)
		if info.IsDir() && info.Name() == ".git" {
			projectPath := filepath.Dir(path)
			projectName := filepath.Base(projectPath)
			
			// Skip nested .git directories (submodules)
			relPath, _ := filepath.Rel(s.reposPath, projectPath)
			if strings.Contains(relPath, string(filepath.Separator)) {
				return nil
			}
			
			project := &ProjectConfig{
				ProjectName: projectName,
				ProjectPath: projectPath,
				Discovered:  true,
			}
			
			// Look for existing ContextLite databases
			s.findExistingDatabase(project)
			
			s.registry.Projects[projectName] = project
			fmt.Printf("   📁 Found: %s", projectName)
			if project.HasDatabase {
				fmt.Printf(" (has database: %.1fKB)", float64(project.DatabaseSize)/1024)
			}
			fmt.Println()
		}
		
		return nil
	})
	
	if err != nil {
		return fmt.Errorf("failed to discover projects: %w", err)
	}
	
	fmt.Printf("✅ Discovered %d Git repositories\n", len(s.registry.Projects))
	return nil
}

// findExistingDatabase looks for existing ContextLite databases in a project
func (s *ContextLiteSetup) findExistingDatabase(project *ProjectConfig) {
	// Common database file patterns
	patterns := []string{
		"contextlite.db",
		"context.db", 
		"contextlite_fresh.db",
		"*contextlite*.db",
	}
	
	for _, pattern := range patterns {
		matches, _ := filepath.Glob(filepath.Join(project.ProjectPath, pattern))
		if len(matches) > 0 {
			// Use the largest/most recent database
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
				project.HasDatabase = true
				project.DatabasePath = bestDB
				project.DatabaseSize = bestSize
			}
			break
		}
	}
}

// AssignPorts assigns standardized ports to all discovered projects
func (s *ContextLiteSetup) AssignPorts() error {
	fmt.Println("🎯 Assigning standardized ports...")
	
	// Sort projects by name for consistent port assignment
	var projectNames []string
	for name := range s.registry.Projects {
		projectNames = append(projectNames, name)
	}
	sort.Strings(projectNames)
	
	currentPort := s.basePort
	for _, name := range projectNames {
		project := s.registry.Projects[name]
		project.Port = currentPort
		
		// Set standardized paths
		project.ConfigPath = filepath.Join(project.ProjectPath, "contextlite-config.yaml")
		
		// If no existing database, set standard path
		if !project.HasDatabase {
			project.DatabasePath = filepath.Join(project.ProjectPath, "contextlite.db")
		}
		
		fmt.Printf("   📍 %s → Port %d", name, currentPort)
		if project.HasDatabase {
			fmt.Printf(" (preserving existing DB)")
		}
		fmt.Println()
		
		currentPort++
	}
	
	s.registry.NextPort = currentPort
	fmt.Printf("✅ Assigned ports %d-%d to %d projects\n", s.basePort, currentPort-1, len(projectNames))
	return nil
}

// UpdateCLAUDEMD updates CLAUDE.md files across all projects
func (s *ContextLiteSetup) UpdateCLAUDEMD() error {
	fmt.Println("📝 Updating CLAUDE.md files across all projects...")
	
	updated := 0
	created := 0
	
	for _, project := range s.registry.Projects {
		claudePath := filepath.Join(project.ProjectPath, "CLAUDE.md")
		
		// Read existing content if it exists
		var existingContent string
		if content, err := ioutil.ReadFile(claudePath); err == nil {
			existingContent = string(content)
		}
		
		// Generate ContextLite configuration section
		contextliteSection := s.generateContextLiteSection(project)
		
		// Update or create CLAUDE.md
		var newContent string
		if existingContent != "" {
			// Remove old ContextLite section if it exists
			newContent = s.removeOldContextLiteSection(existingContent)
			newContent += "\n\n" + contextliteSection
			updated++
		} else {
			newContent = contextliteSection
			created++
		}
		
		// Write updated content
		if err := ioutil.WriteFile(claudePath, []byte(newContent), 0644); err != nil {
			fmt.Printf("   ❌ Failed to update %s: %v\n", project.ProjectName, err)
			continue
		}
		
		fmt.Printf("   ✅ Updated: %s\n", project.ProjectName)
	}
	
	fmt.Printf("✅ Updated %d, Created %d CLAUDE.md files\n", updated, created)
	return nil
}

// generateContextLiteSection creates the standardized ContextLite section
func (s *ContextLiteSetup) generateContextLiteSection(project *ProjectConfig) string {
	dbStatus := "🆕 Ready for initialization"
	if project.HasDatabase {
		dbStatus = "✅ Preserved existing data"
	}
	
	return fmt.Sprintf(`# ContextLite Configuration

## Project Setup
- **Project**: %s
- **Port**: %d
- **Database**: %s
- **Config**: %s

## Quick Commands
` + "```bash" + `
# Start ContextLite for this project
contextlite --config %s --port %d

# Connect via CLI
contextlite-cli connect %s

# Query this project's context
contextlite-cli query %s "your search terms"
` + "```" + `

## Integration Status
- Port assignment: ✅ Standardized
- Database: %s
- Configuration: ✅ Automated
- Discovery: ✅ Enabled`,
		project.ProjectName,
		project.Port,
		project.DatabasePath,
		project.ConfigPath,
		project.ConfigPath,
		project.Port,
		project.ProjectName,
		project.ProjectName,
		dbStatus)
}

// removeOldContextLiteSection removes existing ContextLite configuration sections
func (s *ContextLiteSetup) removeOldContextLiteSection(content string) string {
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
	
	return strings.Join(filtered, "\n")
}

// SaveRegistry saves the project registry to disk
func (s *ContextLiteSetup) SaveRegistry() error {
	s.registry.LastUpdated = os.Getenv("USER_TIMESTAMP")
	if s.registry.LastUpdated == "" {
		s.registry.LastUpdated = fmt.Sprintf("%d", time.Now().Unix())
	}
	s.registry.RegistryVersion = "2.0"
	
	data, err := json.MarshalIndent(s.registry, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal registry: %w", err)
	}
	
	return ioutil.WriteFile(s.registryPath, data, 0644)
}

// CreateProjectConfigs creates standardized config files for each project
func (s *ContextLiteSetup) CreateProjectConfigs() error {
	fmt.Println("⚙️ Creating standardized project configurations...")
	
	for _, project := range s.registry.Projects {
		configContent := s.generateProjectConfig(project)
		
		if err := ioutil.WriteFile(project.ConfigPath, []byte(configContent), 0644); err != nil {
			fmt.Printf("   ❌ Failed to create config for %s: %v\n", project.ProjectName, err)
			continue
		}
		
		fmt.Printf("   ✅ Config: %s\n", project.ProjectName)
	}
	
	return nil
}

// generateProjectConfig creates a standardized config for each project
func (s *ContextLiteSetup) generateProjectConfig(project *ProjectConfig) string {
	dbPath := strings.ReplaceAll(project.DatabasePath, "\\", "/")
	projPath := strings.ReplaceAll(project.ProjectPath, "\\", "/")
	
	return fmt.Sprintf(`# ContextLite Configuration for %s
server:
  port: %d
  host: "127.0.0.1"
  cors_enabled: false
  
storage:
  database_path: "%s"
  cache_size_mb: 64
  
smt:
  solver_timeout_ms: 250
  max_opt_gap: 0.05
  
logging:
  level: "info"
  include_timings: true

# Project-specific settings
project:
  name: "%s"
  path: "%s"
  
# Multi-workspace configuration  
cluster:
  enabled: true
  node_id: "%s-node"
  discovery:
    method: "static"
    service_name: "%s"
`,
		project.ProjectName,
		project.Port,
		dbPath,
		project.ProjectName,
		projPath,
		project.ProjectName,
		project.ProjectName)
}

func main() {
	if len(os.Args) < 2 {
		printUsage()
		return
	}
	
	setup := NewSetup()
	command := os.Args[1]
	
	switch command {
	case "discover":
		if err := setup.DiscoverProjects(); err != nil {
			fmt.Printf("❌ Discovery failed: %v\n", err)
			os.Exit(1)
		}
		
	case "assign-ports":
		if err := setup.DiscoverProjects(); err != nil {
			fmt.Printf("❌ Discovery failed: %v\n", err)
			os.Exit(1)
		}
		if err := setup.AssignPorts(); err != nil {
			fmt.Printf("❌ Port assignment failed: %v\n", err)
			os.Exit(1)
		}
		
	case "setup":
		fmt.Println("🚀 ContextLite System-Wide Setup")
		fmt.Println("=================================")
		
		// Full setup process
		if err := setup.DiscoverProjects(); err != nil {
			fmt.Printf("❌ Discovery failed: %v\n", err)
			os.Exit(1)
		}
		
		if err := setup.AssignPorts(); err != nil {
			fmt.Printf("❌ Port assignment failed: %v\n", err)
			os.Exit(1)
		}
		
		if err := setup.CreateProjectConfigs(); err != nil {
			fmt.Printf("❌ Config creation failed: %v\n", err)
			os.Exit(1)
		}
		
		if err := setup.UpdateCLAUDEMD(); err != nil {
			fmt.Printf("❌ CLAUDE.md update failed: %v\n", err)
			os.Exit(1)
		}
		
		if err := setup.SaveRegistry(); err != nil {
			fmt.Printf("❌ Registry save failed: %v\n", err)
			os.Exit(1)
		}
		
		fmt.Println("\n🎉 ContextLite setup complete!")
		fmt.Printf("   Projects: %d\n", len(setup.registry.Projects))
		fmt.Printf("   Port range: %d-%d\n", setup.basePort, setup.registry.NextPort-1)
		fmt.Printf("   Registry: %s\n", setup.registryPath)
		
	case "status":
		// Load existing registry and show current state
		setup.LoadRegistry()
		setup.ShowStatus()
		
	default:
		printUsage()
	}
}

// LoadRegistry loads existing project registry
func (s *ContextLiteSetup) LoadRegistry() error {
	if _, err := os.Stat(s.registryPath); os.IsNotExist(err) {
		return nil // No existing registry
	}
	
	data, err := ioutil.ReadFile(s.registryPath)
	if err != nil {
		return err
	}
	
	return json.Unmarshal(data, s.registry)
}

// ShowStatus displays current project status
func (s *ContextLiteSetup) ShowStatus() {
	fmt.Println("📊 ContextLite Project Status")
	fmt.Println("=============================")
	
	if len(s.registry.Projects) == 0 {
		fmt.Println("No projects configured. Run 'contextlite-setup setup' first.")
		return
	}
	
	for name, project := range s.registry.Projects {
		fmt.Printf("📁 %s\n", name)
		fmt.Printf("   Port: %d\n", project.Port)
		fmt.Printf("   Database: %s\n", project.DatabasePath)
		if project.HasDatabase {
			fmt.Printf("   Data: %.1fKB preserved\n", float64(project.DatabaseSize)/1024)
		} else {
			fmt.Printf("   Data: Ready for initialization\n")
		}
		fmt.Println()
	}
}

func printUsage() {
	fmt.Println("ContextLite System Setup Tool")
	fmt.Println("=============================")
	fmt.Println("")
	fmt.Println("Commands:")
	fmt.Println("  discover      # Discover all Git repos and databases")
	fmt.Println("  assign-ports  # Assign standardized ports") 
	fmt.Println("  setup         # Full system setup (discover + ports + configs + docs)")
	fmt.Println("  status        # Show current project status")
	fmt.Println("")
	fmt.Println("Examples:")
	fmt.Println("  contextlite-setup discover")
	fmt.Println("  contextlite-setup setup")
	fmt.Println("  contextlite-setup status")
}