package logconsumer

import (
	"bufio"
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"strings"

	"go.uber.org/zap"
	"contextlite/pkg/types"
)

// WorkspaceLogConsumer automatically discovers and consumes workspace-specific logs
type WorkspaceLogConsumer struct {
	logger        *zap.Logger
	storage       types.StorageInterface
	projectPath   string
	workspaceID   string
	dryRun        bool
}

// LogSource represents different types of workspace logs
type LogSource struct {
	Type        string // "claude", "copilot", "cursor", etc.
	Location    string // Full path to log directory
	Pattern     string // File pattern to match
	Verified    bool   // Whether content verification passed
	FileCount   int    // Number of files found
	TotalSize   int64  // Total size in bytes
}

// NewWorkspaceLogConsumer creates a new log consumer for the current project
func NewWorkspaceLogConsumer(logger *zap.Logger, storage types.StorageInterface, projectPath string) *WorkspaceLogConsumer {
	return &WorkspaceLogConsumer{
		logger:      logger,
		storage:     storage,
		projectPath: projectPath,
		workspaceID: generateWorkspaceID(projectPath),
		dryRun:      true, // Start in dry-run mode for safety
	}
}

// generateWorkspaceID converts a project path to the workspace ID format used by tools
func generateWorkspaceID(projectPath string) string {
	// Claude uses: C--Users-micha-repos-contextlite format (single dash between components)
	// Convert /c/Users/micha/repos/contextlite -> C--Users-micha-repos-contextlite
	normalized := filepath.Clean(projectPath)
	
	// Handle Windows paths
	if runtime.GOOS == "windows" {
		normalized = strings.ReplaceAll(normalized, "\\", "/")
	}
	
	// Remove leading /c/ or C:/ and convert separators to single dash
	normalized = strings.TrimPrefix(normalized, "/c/")
	normalized = strings.TrimPrefix(normalized, "C:/")
	normalized = strings.ReplaceAll(normalized, "/", "-")
	
	// Ensure it starts with C-- (drive letter with double dash)
	if !strings.HasPrefix(normalized, "C--") {
		normalized = "C--" + normalized
	}
	
	return normalized
}

// DiscoverLogSources finds all available workspace log sources for this project
func (wlc *WorkspaceLogConsumer) DiscoverLogSources() ([]LogSource, error) {
	var sources []LogSource
	
	// Discover Claude logs
	claudeSources := wlc.discoverClaudeLogs()
	sources = append(sources, claudeSources...)
	
	// Discover Copilot logs  
	copilotSources := wlc.discoverCopilotLogs()
	sources = append(sources, copilotSources...)
	
	// Verify each source contains project-related content
	for i := range sources {
		sources[i].Verified = wlc.verifyLogContent(&sources[i])
	}
	
	wlc.logger.Info("Discovered workspace log sources",
		zap.String("workspace_id", wlc.workspaceID),
		zap.Int("total_sources", len(sources)))
	
	return sources, nil
}

// discoverClaudeLogs finds Claude workspace logs
func (wlc *WorkspaceLogConsumer) discoverClaudeLogs() []LogSource {
	var sources []LogSource
	
	// Standard Claude locations by OS
	var claudeBasePaths []string
	
	switch runtime.GOOS {
	case "windows":
		claudeBasePaths = []string{
			filepath.Join(os.Getenv("USERPROFILE"), ".claude", "projects"),
			filepath.Join(os.Getenv("APPDATA"), "Claude", "projects"),
		}
	case "darwin":
		homeDir, _ := os.UserHomeDir()
		claudeBasePaths = []string{
			filepath.Join(homeDir, ".claude", "projects"),
			filepath.Join(homeDir, "Library", "Application Support", "Claude", "projects"),
		}
	case "linux":
		homeDir, _ := os.UserHomeDir()
		claudeBasePaths = []string{
			filepath.Join(homeDir, ".claude", "projects"),
			filepath.Join(homeDir, ".config", "claude", "projects"),
		}
	}
	
	// Look for our specific workspace ID
	for _, basePath := range claudeBasePaths {
		workspacePath := filepath.Join(basePath, wlc.workspaceID)
		if stat, err := os.Stat(workspacePath); err == nil && stat.IsDir() {
			source := LogSource{
				Type:     "claude",
				Location: workspacePath,
				Pattern:  "*.jsonl",
			}
			
			// Count files and calculate size
			source.FileCount, source.TotalSize = wlc.calculateDirectoryStats(workspacePath, "*.jsonl")
			sources = append(sources, source)
			
			wlc.logger.Info("Found Claude workspace",
				zap.String("path", workspacePath),
				zap.Int("files", source.FileCount),
				zap.Int64("size_bytes", source.TotalSize))
		}
	}
	
	return sources
}

// discoverCopilotLogs finds GitHub Copilot workspace logs
func (wlc *WorkspaceLogConsumer) discoverCopilotLogs() []LogSource {
	var sources []LogSource
	
	// Copilot logs are typically in VS Code extension data
	var copilotBasePaths []string
	
	switch runtime.GOOS {
	case "windows":
		copilotBasePaths = []string{
			filepath.Join(os.Getenv("APPDATA"), "Code", "logs"),
			filepath.Join(os.Getenv("APPDATA"), "Code", "User", "workspaceStorage"),
		}
	case "darwin":
		homeDir, _ := os.UserHomeDir()
		copilotBasePaths = []string{
			filepath.Join(homeDir, "Library", "Application Support", "Code", "logs"),
			filepath.Join(homeDir, "Library", "Application Support", "Code", "User", "workspaceStorage"),
		}
	case "linux":
		homeDir, _ := os.UserHomeDir()
		copilotBasePaths = []string{
			filepath.Join(homeDir, ".config", "Code", "logs"),
			filepath.Join(homeDir, ".config", "Code", "User", "workspaceStorage"),
		}
	}
	
	// Look for workspace-specific Copilot data
	for _, basePath := range copilotBasePaths {
		if entries, err := os.ReadDir(basePath); err == nil {
			for _, entry := range entries {
				if entry.IsDir() && wlc.isProjectRelated(entry.Name()) {
					fullPath := filepath.Join(basePath, entry.Name())
					source := LogSource{
						Type:     "copilot",
						Location: fullPath,
						Pattern:  "*.log",
					}
					
					source.FileCount, source.TotalSize = wlc.calculateDirectoryStats(fullPath, "*.log")
					if source.FileCount > 0 {
						sources = append(sources, source)
					}
				}
			}
		}
	}
	
	return sources
}

// verifyLogContent performs content verification to ensure logs are project-related
func (wlc *WorkspaceLogConsumer) verifyLogContent(source *LogSource) bool {
	// Project-specific keywords to look for
	projectKeywords := []string{
		"contextlite",
		filepath.Base(wlc.projectPath),
		"github.com/Michael-A-Kuykendall/contextlite",
	}
	
	// Sample a few files from the source
	files, err := filepath.Glob(filepath.Join(source.Location, source.Pattern))
	if err != nil || len(files) == 0 {
		return false
	}
	
	// Check first few files for project-related content
	for i, file := range files {
		if i >= 3 { // Only check first 3 files
			break
		}
		
		if wlc.fileContainsProjectKeywords(file, projectKeywords) {
			wlc.logger.Debug("Verified log content",
				zap.String("file", file),
				zap.String("source_type", source.Type))
			return true
		}
	}
	
	return false
}

// fileContainsProjectKeywords checks if a file contains project-related keywords
func (wlc *WorkspaceLogConsumer) fileContainsProjectKeywords(filePath string, keywords []string) bool {
	file, err := os.Open(filePath)
	if err != nil {
		return false
	}
	defer file.Close()
	
	scanner := bufio.NewScanner(file)
	linesScanned := 0
	
	for scanner.Scan() && linesScanned < 50 { // Only scan first 50 lines
		line := strings.ToLower(scanner.Text())
		
		for _, keyword := range keywords {
			if strings.Contains(line, strings.ToLower(keyword)) {
				return true
			}
		}
		linesScanned++
	}
	
	return false
}

// isProjectRelated checks if a directory name is related to our project
func (wlc *WorkspaceLogConsumer) isProjectRelated(dirName string) bool {
	lower := strings.ToLower(dirName)
	return strings.Contains(lower, "contextlite") || 
		   strings.Contains(lower, strings.ToLower(filepath.Base(wlc.projectPath)))
}

// calculateDirectoryStats counts files and calculates total size
func (wlc *WorkspaceLogConsumer) calculateDirectoryStats(dir, pattern string) (int, int64) {
	files, err := filepath.Glob(filepath.Join(dir, pattern))
	if err != nil {
		return 0, 0
	}
	
	var totalSize int64
	for _, file := range files {
		if stat, err := os.Stat(file); err == nil {
			totalSize += stat.Size()
		}
	}
	
	return len(files), totalSize
}

// ConsumeLogSources processes and indexes all verified log sources
func (wlc *WorkspaceLogConsumer) ConsumeLogSources(sources []LogSource) error {
	if wlc.dryRun {
		wlc.logger.Info("DRY RUN MODE: Would consume log sources", 
			zap.Int("verified_sources", len(sources)))
		return nil
	}
	
	ctx := context.Background()
	
	for _, source := range sources {
		if !source.Verified {
			wlc.logger.Warn("Skipping unverified source", 
				zap.String("type", source.Type),
				zap.String("location", source.Location))
			continue
		}
		
		wlc.logger.Info("Consuming log source",
			zap.String("type", source.Type),
			zap.String("location", source.Location),
			zap.Int("files", source.FileCount))
		
		if err := wlc.consumeSource(ctx, &source); err != nil {
			wlc.logger.Error("Failed to consume source",
				zap.String("type", source.Type),
				zap.Error(err))
			continue
		}
	}
	
	return nil
}

// consumeSource processes a single log source
func (wlc *WorkspaceLogConsumer) consumeSource(ctx context.Context, source *LogSource) error {
	files, err := filepath.Glob(filepath.Join(source.Location, source.Pattern))
	if err != nil {
		return err
	}
	
	for _, file := range files {
		if err := wlc.processLogFile(ctx, file, source.Type); err != nil {
			wlc.logger.Warn("Failed to process log file",
				zap.String("file", file),
				zap.Error(err))
			continue
		}
	}
	
	return nil
}

// processLogFile processes a single log file based on its type
func (wlc *WorkspaceLogConsumer) processLogFile(ctx context.Context, filePath, sourceType string) error {
	switch sourceType {
	case "claude":
		return wlc.processClaudeJSONL(ctx, filePath)
	case "copilot":
		return wlc.processCopilotLog(ctx, filePath)
	default:
		return fmt.Errorf("unknown source type: %s", sourceType)
	}
}

// processClaudeJSONL processes Claude JSONL conversation files
func (wlc *WorkspaceLogConsumer) processClaudeJSONL(ctx context.Context, filePath string) error {
	file, err := os.Open(filePath)
	if err != nil {
		return err
	}
	defer file.Close()
	
	scanner := bufio.NewScanner(file)
	lineNum := 0
	
	for scanner.Scan() {
		lineNum++
		
		var entry map[string]interface{}
		if err := json.Unmarshal(scanner.Bytes(), &entry); err != nil {
			continue // Skip malformed JSON
		}
		
		// Extract meaningful content for indexing
		if content := wlc.extractClaudeContent(entry); content != "" {
			doc := types.Document{
				ID:      fmt.Sprintf("%s_line_%d", filepath.Base(filePath), lineNum),
				Path:    fmt.Sprintf("claude_logs/%s#L%d", filepath.Base(filePath), lineNum),
				Content: content,
				// Add additional metadata
			}
			
			if err := wlc.storage.InsertDocument(doc); err != nil {
				wlc.logger.Warn("Failed to insert Claude document",
					zap.String("id", doc.ID),
					zap.Error(err))
			}
		}
	}
	
	return nil
}

// extractClaudeContent extracts meaningful content from Claude JSONL entries
func (wlc *WorkspaceLogConsumer) extractClaudeContent(entry map[string]interface{}) string {
	// Extract user messages and assistant responses
	if msg, ok := entry["message"].(map[string]interface{}); ok {
		if content, ok := msg["content"].(string); ok && content != "" {
			return content
		}
		
		// Handle structured content arrays
		if contentArray, ok := msg["content"].([]interface{}); ok {
			var parts []string
			for _, part := range contentArray {
				if partMap, ok := part.(map[string]interface{}); ok {
					if text, ok := partMap["text"].(string); ok {
						parts = append(parts, text)
					}
				}
			}
			return strings.Join(parts, "\n")
		}
	}
	
	return ""
}

// processCopilotLog processes GitHub Copilot log files
func (wlc *WorkspaceLogConsumer) processCopilotLog(ctx context.Context, filePath string) error {
	file, err := os.Open(filePath)
	if err != nil {
		return err
	}
	defer file.Close()
	
	scanner := bufio.NewScanner(file)
	lineNum := 0
	
	for scanner.Scan() {
		lineNum++
		line := scanner.Text()
		
		// Copilot logs can have everything on one line - need careful parsing
		if wlc.isMeaningfulCopilotLine(line) {
			doc := types.Document{
				ID:      fmt.Sprintf("copilot_%s_line_%d", filepath.Base(filePath), lineNum),
				Path:    fmt.Sprintf("copilot_logs/%s#L%d", filepath.Base(filePath), lineNum),
				Content: wlc.formatCopilotContent(line),
			}
			
			if err := wlc.storage.InsertDocument(doc); err != nil {
				wlc.logger.Warn("Failed to insert Copilot document",
					zap.String("id", doc.ID),
					zap.Error(err))
			}
		}
	}
	
	return nil
}

// isMeaningfulCopilotLine determines if a Copilot log line contains meaningful content
func (wlc *WorkspaceLogConsumer) isMeaningfulCopilotLine(line string) bool {
	// Filter out noise and focus on actual interactions
	meaningful := []string{
		"completion",
		"suggestion",
		"request",
		"response",
		"contextlite",
	}
	
	lower := strings.ToLower(line)
	for _, keyword := range meaningful {
		if strings.Contains(lower, keyword) {
			return true
		}
	}
	
	return false
}

// formatCopilotContent formats Copilot log content for better readability
func (wlc *WorkspaceLogConsumer) formatCopilotContent(line string) string {
	// Handle case where entire JSON is on one line
	if strings.HasPrefix(line, "{") && strings.HasSuffix(line, "}") {
		var parsed map[string]interface{}
		if err := json.Unmarshal([]byte(line), &parsed); err == nil {
			if formatted, err := json.MarshalIndent(parsed, "", "  "); err == nil {
				return string(formatted)
			}
		}
	}
	
	return line
}

// SetDryRun enables or disables dry-run mode
func (wlc *WorkspaceLogConsumer) SetDryRun(dryRun bool) {
	wlc.dryRun = dryRun
}

// GetWorkspaceID returns the calculated workspace ID
func (wlc *WorkspaceLogConsumer) GetWorkspaceID() string {
	return wlc.workspaceID
}
