package api

import (
	"encoding/json"
	"fmt"
	"net/http"
	
	"go.uber.org/zap"
	"contextlite/internal/logconsumer"
)

// handleDiscoverWorkspaceLogs discovers available workspace logs for this project
func (s *Server) handleDiscoverWorkspaceLogs(w http.ResponseWriter, r *http.Request) {
	// Get project path from current working directory or request
	projectPath := "." // Default to current directory
	if path := r.URL.Query().Get("project_path"); path != "" {
		projectPath = path
	}
	
	// Create workspace log consumer
	consumer := logconsumer.NewWorkspaceLogConsumer(s.logger, s.storage, projectPath)
	
	// Discover available sources
	sources, err := consumer.DiscoverLogSources()
	if err != nil {
		s.logger.Error("Failed to discover log sources", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to discover log sources: "+err.Error())
		return
	}
	
	// Calculate totals
	var totalFiles int
	var totalSize int64
	var verifiedSources int
	
	for _, source := range sources {
		totalFiles += source.FileCount
		totalSize += source.TotalSize
		if source.Verified {
			verifiedSources++
		}
	}
	
	response := map[string]interface{}{
		"workspace_id":      consumer.GetWorkspaceID(),
		"project_path":      projectPath,
		"sources":           sources,
		"total_sources":     len(sources),
		"verified_sources":  verifiedSources,
		"total_files":       totalFiles,
		"total_size_bytes":  totalSize,
		"total_size_human":  formatBytes(totalSize),
		"dry_run_mode":      true, // Always start in dry-run
	}
	
	s.writeJSON(w, http.StatusOK, response)
}

// handleConsumeWorkspaceLogs consumes workspace logs into the database
func (s *Server) handleConsumeWorkspaceLogs(w http.ResponseWriter, r *http.Request) {
	var req struct {
		ProjectPath string `json:"project_path,omitempty"`
		DryRun      bool   `json:"dry_run"`
		ForceRun    bool   `json:"force_run"` // Override safety check
	}
	
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		s.writeError(w, http.StatusBadRequest, "Invalid request: "+err.Error())
		return
	}
	
	// Default to current directory
	if req.ProjectPath == "" {
		req.ProjectPath = "."
	}
	
	// Create workspace log consumer
	consumer := logconsumer.NewWorkspaceLogConsumer(s.logger, s.storage, req.ProjectPath)
	
	// Set dry-run mode (default to true for safety)
	if !req.ForceRun {
		req.DryRun = true
	}
	consumer.SetDryRun(req.DryRun)
	
	// Discover sources first
	sources, err := consumer.DiscoverLogSources()
	if err != nil {
		s.logger.Error("Failed to discover log sources", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to discover log sources: "+err.Error())
		return
	}
	
	// Filter to only verified sources
	var verifiedSources []logconsumer.LogSource
	for _, source := range sources {
		if source.Verified {
			verifiedSources = append(verifiedSources, source)
		}
	}
	
	// Safety check - require explicit force for large consumption
	var totalSize int64
	for _, source := range verifiedSources {
		totalSize += source.TotalSize
	}
	
	if totalSize > 100*1024*1024 && !req.ForceRun { // 100MB limit
		s.writeError(w, http.StatusBadRequest, 
			"Log consumption exceeds 100MB. Use force_run=true to proceed.")
		return
	}
	
	// Consume the logs
	if err := consumer.ConsumeLogSources(verifiedSources); err != nil {
		s.logger.Error("Failed to consume log sources", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to consume logs: "+err.Error())
		return
	}
	
	response := map[string]interface{}{
		"workspace_id":        consumer.GetWorkspaceID(),
		"sources_processed":   len(verifiedSources),
		"total_size_bytes":    totalSize,
		"total_size_human":    formatBytes(totalSize),
		"dry_run":            req.DryRun,
		"status":             "completed",
	}
	
	if req.DryRun {
		response["message"] = "DRY RUN: No logs were actually consumed. Use force_run=true to execute."
	} else {
		response["message"] = "Workspace logs successfully consumed and indexed."
	}
	
	s.writeJSON(w, http.StatusOK, response)
}

// formatBytes formats byte count into human-readable string
func formatBytes(bytes int64) string {
	const unit = 1024
	if bytes < unit {
		return fmt.Sprintf("%d B", bytes)
	}
	div, exp := int64(unit), 0
	for n := bytes / unit; n >= unit; n /= unit {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.1f %cB", float64(bytes)/float64(div), "KMGTPE"[exp])
}
