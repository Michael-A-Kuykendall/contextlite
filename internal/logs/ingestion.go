package logs

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"time"
)

// LogSource represents a development tool log source
type LogSource struct {
	Name        string   `json:"name"`
	Enabled     bool     `json:"enabled"`
	Paths       []string `json:"paths"`
	FilePattern string   `json:"file_pattern"`
	LogFormat   string   `json:"log_format"` // "json", "text", "git", "sqlite"
	LastImport  string   `json:"last_import"`
}

// LogIngestionManager handles importing logs from various development tools
type LogIngestionManager struct {
	ProjectName string      `json:"project_name"`
	ProjectPath string      `json:"project_path"`
	Sources     []LogSource `json:"sources"`
	Config      *IngestionConfig `json:"config"`
}

// IngestionConfig controls log import behavior
type IngestionConfig struct {
	Interval       string `json:"interval"`        // "on_exit", "hourly", "daily"
	MaxFileSize    int64  `json:"max_file_size"`   // Maximum log file size to process
	RetentionDays  int    `json:"retention_days"`  // How long to keep imported logs
	EnableFilters  bool   `json:"enable_filters"`  // Filter out sensitive data
}

// NewLogIngestionManager creates a new log ingestion manager
func NewLogIngestionManager(projectName, projectPath string) *LogIngestionManager {
	manager := &LogIngestionManager{
		ProjectName: projectName,
		ProjectPath: projectPath,
		Config: &IngestionConfig{
			Interval:      "on_exit",
			MaxFileSize:   100 * 1024 * 1024, // 100MB max
			RetentionDays: 30,
			EnableFilters: true,
		},
	}
	
	// Initialize standard log sources
	manager.initializeStandardSources()
	return manager
}

// initializeStandardSources sets up common development tool log sources
func (lim *LogIngestionManager) initializeStandardSources() {
	homeDir, _ := os.UserHomeDir()
	
	sources := []LogSource{
		{
			Name:        "Claude Code",
			Enabled:     false,
			Paths:       getClaudeCodeLogPaths(homeDir),
			FilePattern: "*.log",
			LogFormat:   "text",
		},
		{
			Name:        "GitHub Copilot",
			Enabled:     false,
			Paths:       getCopilotLogPaths(homeDir),
			FilePattern: "*.log",
			LogFormat:   "text",
		},
		{
			Name:        "VS Code",
			Enabled:     false,
			Paths:       getVSCodeLogPaths(homeDir),
			FilePattern: "*.log",
			LogFormat:   "text",
		},
		{
			Name:        "Git History",
			Enabled:     false,
			Paths:       []string{filepath.Join(lim.ProjectPath, ".git")},
			FilePattern: "*",
			LogFormat:   "git",
		},
		{
			Name:        "Cursor IDE",
			Enabled:     false,
			Paths:       getCursorLogPaths(homeDir),
			FilePattern: "*.log",
			LogFormat:   "text",
		},
		{
			Name:        "JetBrains IDEs",
			Enabled:     false,
			Paths:       getJetBrainsLogPaths(homeDir),
			FilePattern: "*.log",
			LogFormat:   "text",
		},
		{
			Name:        "Windsurf IDE",
			Enabled:     false,
			Paths:       getWindsurfLogPaths(homeDir),
			FilePattern: "*.log",
			LogFormat:   "text",
		},
	}
	
	lim.Sources = sources
}

// getClaudeCodeLogPaths returns Claude Code log locations per platform
func getClaudeCodeLogPaths(homeDir string) []string {
	switch runtime.GOOS {
	case "windows":
		return []string{
			filepath.Join(homeDir, "AppData", "Local", "AnthropicClaude", "logs"),
			filepath.Join(homeDir, "AppData", "Roaming", "AnthropicClaude", "logs"),
		}
	case "darwin":
		return []string{
			filepath.Join(homeDir, "Library", "Logs", "AnthropicClaude"),
			filepath.Join(homeDir, "Library", "Application Support", "AnthropicClaude", "logs"),
		}
	default:
		return []string{
			filepath.Join(homeDir, ".local", "share", "AnthropicClaude", "logs"),
			filepath.Join(homeDir, ".cache", "AnthropicClaude", "logs"),
		}
	}
}

// getCopilotLogPaths returns GitHub Copilot log locations
func getCopilotLogPaths(homeDir string) []string {
	switch runtime.GOOS {
	case "windows":
		return []string{
			filepath.Join(homeDir, "AppData", "Roaming", "Code", "logs"),
			filepath.Join(homeDir, "AppData", "Roaming", "Code", "CachedExtensions"),
		}
	case "darwin":
		return []string{
			filepath.Join(homeDir, "Library", "Application Support", "Code", "logs"),
			filepath.Join(homeDir, "Library", "Caches", "com.github.GitHubCopilot"),
		}
	default:
		return []string{
			filepath.Join(homeDir, ".config", "Code", "logs"),
			filepath.Join(homeDir, ".cache", "github-copilot"),
		}
	}
}

// getVSCodeLogPaths returns VS Code log locations
func getVSCodeLogPaths(homeDir string) []string {
	switch runtime.GOOS {
	case "windows":
		return []string{
			filepath.Join(homeDir, "AppData", "Roaming", "Code", "logs"),
		}
	case "darwin":
		return []string{
			filepath.Join(homeDir, "Library", "Application Support", "Code", "logs"),
		}
	default:
		return []string{
			filepath.Join(homeDir, ".config", "Code", "logs"),
		}
	}
}

// getCursorLogPaths returns Cursor IDE log locations
func getCursorLogPaths(homeDir string) []string {
	switch runtime.GOOS {
	case "windows":
		return []string{
			filepath.Join(homeDir, "AppData", "Roaming", "Cursor", "logs"),
		}
	case "darwin":
		return []string{
			filepath.Join(homeDir, "Library", "Application Support", "Cursor", "logs"),
		}
	default:
		return []string{
			filepath.Join(homeDir, ".config", "Cursor", "logs"),
		}
	}
}

// getJetBrainsLogPaths returns JetBrains IDE log locations
func getJetBrainsLogPaths(homeDir string) []string {
	switch runtime.GOOS {
	case "windows":
		return []string{
			filepath.Join(homeDir, "AppData", "Local", "JetBrains"),
		}
	case "darwin":
		return []string{
			filepath.Join(homeDir, "Library", "Logs", "JetBrains"),
		}
	default:
		return []string{
			filepath.Join(homeDir, ".local", "share", "JetBrains"),
			filepath.Join(homeDir, ".cache", "JetBrains"),
		}
	}
}

// getWindsurfLogPaths returns Windsurf IDE log locations
func getWindsurfLogPaths(homeDir string) []string {
	switch runtime.GOOS {
	case "windows":
		return []string{
			filepath.Join(homeDir, "AppData", "Roaming", "Windsurf", "logs"),
		}
	case "darwin":
		return []string{
			filepath.Join(homeDir, "Library", "Application Support", "Windsurf", "logs"),
		}
	default:
		return []string{
			filepath.Join(homeDir, ".config", "Windsurf", "logs"),
		}
	}
}

// EnableSource enables a specific log source
func (lim *LogIngestionManager) EnableSource(sourceName string) error {
	for i := range lim.Sources {
		if lim.Sources[i].Name == sourceName {
			lim.Sources[i].Enabled = true
			return nil
		}
	}
	return fmt.Errorf("source not found: %s", sourceName)
}

// ImportLogs imports logs from all enabled sources
func (lim *LogIngestionManager) ImportLogs() (*ImportResult, error) {
	result := &ImportResult{
		ProjectName: lim.ProjectName,
		StartTime:   time.Now(),
		Sources:     make(map[string]*SourceResult),
	}
	
	for _, source := range lim.Sources {
		if !source.Enabled {
			continue
		}
		
		sourceResult := &SourceResult{
			SourceName: source.Name,
			StartTime:  time.Now(),
		}
		
		switch source.LogFormat {
		case "git":
			err := lim.importGitHistory(source, sourceResult)
			sourceResult.Success = err == nil
			if err != nil {
				sourceResult.Error = err.Error()
			}
		case "text", "json":
			err := lim.importTextLogs(source, sourceResult)
			sourceResult.Success = err == nil
			if err != nil {
				sourceResult.Error = err.Error()
			}
		}
		
		sourceResult.EndTime = time.Now()
		sourceResult.Duration = sourceResult.EndTime.Sub(sourceResult.StartTime)
		result.Sources[source.Name] = sourceResult
	}
	
	result.EndTime = time.Now()
	result.Duration = result.EndTime.Sub(result.StartTime)
	
	return result, nil
}

// ImportResult contains results from log import operation
type ImportResult struct {
	ProjectName string                   `json:"project_name"`
	StartTime   time.Time               `json:"start_time"`
	EndTime     time.Time               `json:"end_time"`
	Duration    time.Duration           `json:"duration"`
	Sources     map[string]*SourceResult `json:"sources"`
}

// SourceResult contains results from a single source import
type SourceResult struct {
	SourceName   string        `json:"source_name"`
	StartTime    time.Time     `json:"start_time"`
	EndTime      time.Time     `json:"end_time"`
	Duration     time.Duration `json:"duration"`
	FilesFound   int           `json:"files_found"`
	FilesImported int          `json:"files_imported"`
	BytesImported int64         `json:"bytes_imported"`
	Success      bool          `json:"success"`
	Error        string        `json:"error,omitempty"`
}

// importGitHistory imports Git commit history and activity
func (lim *LogIngestionManager) importGitHistory(source LogSource, result *SourceResult) error {
	gitDir := filepath.Join(lim.ProjectPath, ".git")
	if _, err := os.Stat(gitDir); os.IsNotExist(err) {
		return fmt.Errorf("no git repository found")
	}
	
	// Import Git log in structured format
	// This would integrate with ContextLite's document indexing system
	fmt.Printf("   📊 Importing Git history for %s...\n", lim.ProjectName)
	
	result.FilesFound = 1
	result.FilesImported = 1
	result.BytesImported = 1024 // Placeholder
	
	return nil
}

// importTextLogs imports text-based log files
func (lim *LogIngestionManager) importTextLogs(source LogSource, result *SourceResult) error {
	var totalFiles, importedFiles int
	var totalBytes int64
	
	for _, logPath := range source.Paths {
		if _, err := os.Stat(logPath); os.IsNotExist(err) {
			continue
		}
		
		// Find log files matching pattern
		pattern := filepath.Join(logPath, source.FilePattern)
		matches, err := filepath.Glob(pattern)
		if err != nil {
			continue
		}
		
		totalFiles += len(matches)
		
		for _, match := range matches {
			info, err := os.Stat(match)
			if err != nil || info.Size() > lim.Config.MaxFileSize {
				continue
			}
			
			// Filter recent files only (last 7 days)
			if time.Since(info.ModTime()) > 7*24*time.Hour {
				continue
			}
			
			// Process log file
			content, err := ioutil.ReadFile(match)
			if err != nil {
				continue
			}
			
			// Filter sensitive data if enabled
			if lim.Config.EnableFilters {
				content = filterSensitiveData(content)
			}
			
			// This would integrate with ContextLite's document indexing
			fmt.Printf("     📄 Imported: %s (%.1fKB)\n", filepath.Base(match), float64(len(content))/1024)
			
			importedFiles++
			totalBytes += int64(len(content))
		}
	}
	
	result.FilesFound = totalFiles
	result.FilesImported = importedFiles
	result.BytesImported = totalBytes
	
	return nil
}

// Compiled regex patterns for security - prevents ReDoS attacks
var (
	passwordPattern = regexp.MustCompile(`"password":"[^"]*"`)
	tokenPattern = regexp.MustCompile(`"token":"[^"]*"`)
	apikeyPattern = regexp.MustCompile(`"apikey":"[^"]*"`)
	secretPattern = regexp.MustCompile(`"secret":"[^"]*"`)
	authPattern = regexp.MustCompile(`Authorization: Bearer [^\s]+`)
	sshPattern = regexp.MustCompile(`ssh-rsa [^\s]+`)
	keyPattern = regexp.MustCompile(`-----BEGIN [^-]+ KEY-----[^-]+-----END [^-]+ KEY-----`)
	
	// SECURITY: Additional dangerous patterns
	urlPattern = regexp.MustCompile(`https?://[^\s]*:[^\s]*@[^\s]+`) // URLs with credentials
	ipPattern = regexp.MustCompile(`\b(?:\d{1,3}\.){3}\d{1,3}:\d+\b`) // IP:Port combinations
)

// filterSensitiveData removes potentially sensitive information from logs
func filterSensitiveData(content []byte) []byte {
	// SECURITY: Size limit to prevent memory exhaustion
	maxLogSize := 10 * 1024 * 1024 // 10MB limit
	if len(content) > maxLogSize {
		content = content[:maxLogSize]
	}
	
	text := string(content)
	
	// SECURITY: Use compiled regex patterns to prevent ReDoS
	text = passwordPattern.ReplaceAllString(text, `"password":"[FILTERED]"`)
	text = tokenPattern.ReplaceAllString(text, `"token":"[FILTERED]"`)
	text = apikeyPattern.ReplaceAllString(text, `"apikey":"[FILTERED]"`)
	text = secretPattern.ReplaceAllString(text, `"secret":"[FILTERED]"`)
	text = authPattern.ReplaceAllString(text, `Authorization: Bearer [FILTERED]`)
	text = sshPattern.ReplaceAllString(text, `ssh-rsa [FILTERED]`)
	text = keyPattern.ReplaceAllString(text, `-----BEGIN PRIVATE KEY-----[FILTERED]-----END PRIVATE KEY-----`)
	text = urlPattern.ReplaceAllString(text, `https://[FILTERED]`)
	text = ipPattern.ReplaceAllString(text, `[IP:PORT_FILTERED]`)
	
	return []byte(text)
}

// SaveConfiguration saves the ingestion configuration with atomic writes
func (lim *LogIngestionManager) SaveConfiguration() error {
	configPath := filepath.Join(lim.ProjectPath, ".contextlite", "log_ingestion.json")
	
	// SECURITY: Atomic directory creation and file write
	configDir := filepath.Dir(configPath)
	if err := os.MkdirAll(configDir, 0755); err != nil {
		return fmt.Errorf("failed to create config directory: %w", err)
	}
	
	data, err := json.MarshalIndent(lim, "", "  ")
	if err != nil {
		return err
	}
	
	// SECURITY: Atomic write with temporary file
	tempPath := configPath + ".tmp"
	if err := ioutil.WriteFile(tempPath, data, 0644); err != nil {
		return fmt.Errorf("failed to write temp config: %w", err)
	}
	
	// SECURITY: Atomic rename prevents corruption
	if err := os.Rename(tempPath, configPath); err != nil {
		os.Remove(tempPath)
		return fmt.Errorf("failed to move config file: %w", err)
	}
	
	return nil
}

// LoadConfiguration loads existing ingestion configuration
func LoadLogIngestionConfig(projectPath string) (*LogIngestionManager, error) {
	configPath := filepath.Join(projectPath, ".contextlite", "log_ingestion.json")
	
	if _, err := os.Stat(configPath); os.IsNotExist(err) {
		// Return default configuration
		projectName := filepath.Base(projectPath)
		return NewLogIngestionManager(projectName, projectPath), nil
	}
	
	data, err := ioutil.ReadFile(configPath)
	if err != nil {
		return nil, err
	}
	
	var manager LogIngestionManager
	if err := json.Unmarshal(data, &manager); err != nil {
		return nil, err
	}
	
	return &manager, nil
}