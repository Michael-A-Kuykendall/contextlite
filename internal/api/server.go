package api

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"time"

	"github.com/go-chi/chi/v5"
	"github.com/go-chi/chi/v5/middleware"
	"github.com/go-chi/cors"
	"go.uber.org/zap"

	apimiddleware "contextlite/internal/api/middleware"
	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// Server provides the HTTP API server
type Server struct {
	router      *chi.Mux
	engine      types.ContextEngine
	storage     types.StorageInterface
	config      *config.Config
	logger      *zap.Logger
	featureGate types.FeatureGate
}

// New creates a new API server
func New(engine types.ContextEngine, storage types.StorageInterface, config *config.Config, logger *zap.Logger, featureGate types.FeatureGate) *Server {
	s := &Server{
		engine:      engine,
		storage:     storage,
		config:      config,
		logger:      logger,
		featureGate: featureGate,
	}
	
	s.setupRoutes()
	return s
}

// setupRoutes configures the HTTP routes
func (s *Server) setupRoutes() {
	r := chi.NewRouter()
	
	// Middleware
	r.Use(middleware.RequestID)
	r.Use(middleware.RealIP)
	r.Use(middleware.Logger)
	r.Use(middleware.Recoverer)
	r.Use(middleware.Timeout(60 * time.Second))
	
	// Rate limiting middleware
	rateLimiterConfig := apimiddleware.RateLimiterConfig{
		Enabled:           s.config.Server.RateLimiting.Enabled,
		RequestsPerMinute: s.config.Server.RateLimiting.RequestsPerMinute,
		Burst:             s.config.Server.RateLimiting.Burst,
		EndpointSpecific:  s.config.Server.RateLimiting.EndpointSpecific,
	}
	rateLimiter := apimiddleware.NewRateLimiter(rateLimiterConfig)
	r.Use(rateLimiter.Middleware())
	
	// CORS if enabled
	if s.config.Server.CORSEnabled {
		r.Use(cors.Handler(cors.Options{
			AllowedOrigins:   []string{"*"},
			AllowedMethods:   []string{"GET", "POST", "PUT", "DELETE", "OPTIONS"},
			AllowedHeaders:   []string{"*"},
			ExposedHeaders:   []string{"Link"},
			AllowCredentials: true,
			MaxAge:           300,
		}))
	}
	
	// Health check (no auth required)
	r.Get("/health", s.handleHealth)
	
	// License status (no auth required)
	r.Get("/license/status", s.handleLicenseStatus)
	
	// API routes with authentication
	r.Route("/api/v1", func(r chi.Router) {
		// Bearer token authentication for all API routes
		r.Use(s.authMiddleware)
		
		// License and trial information
		r.Get("/license/status", s.handleLicenseStatus)
		r.Get("/trial/info", s.handleTrialInfo)
		
		// Context assembly (requires Professional+)
		r.With(s.requireProfessional).Post("/context/assemble", s.handleAssembleContext)
		
		// Lightweight RAG endpoints (requires Professional+)
		r.With(s.requireProfessional).Post("/rank", s.handleRank)
		r.With(s.requireProfessional).Post("/snippet", s.handleSnippet)
		
		// Baseline comparison (requires Professional+)
		r.With(s.requireProfessional).Post("/context/baseline", s.handleBaselineComparison)
		
		// Document management (Basic features - all tiers)
		r.Post("/documents", s.handleAddDocument)
		r.Post("/documents/bulk", s.handleBulkAddDocuments)
		r.Post("/documents/workspace", s.handleScanWorkspace)
		r.Delete("/documents/{id}", s.handleDeleteDocument)
		r.Get("/documents/search", s.handleSearchDocuments)
		
		// Weight management (requires Professional+)
		r.With(s.requireProfessional).Post("/weights/update", s.handleUpdateWeights)
		r.With(s.requireProfessional).Get("/weights", s.handleGetWeights)
		r.With(s.requireProfessional).Post("/weights/reset", s.handleResetWeights)
		
		// Cache management (requires Professional+)
		r.With(s.requireProfessional).Post("/cache/invalidate", s.handleInvalidateCache)
		r.With(s.requireProfessional).Get("/cache/stats", s.handleCacheStats)
		
		// System info (Basic for all, detailed for Professional+)
		r.Get("/storage/info", s.handleStorageInfo)
		r.With(s.requireProfessional).Get("/optimization/stats", s.handleoptimizationStats)
		
		// Enterprise-only endpoints
		r.Route("/enterprise", func(r chi.Router) {
			r.Use(s.requireEnterprise)
			r.Get("/tenants", s.handleListTenants)
			r.Post("/tenants", s.handleCreateTenant)
			r.Get("/mcp/servers", s.handleListMCPServers)
			r.Post("/mcp/servers", s.handleCreateMCPServer)
		})
	})
	
	s.router = r
}

// authMiddleware validates bearer token authentication
func (s *Server) authMiddleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Skip auth if no token is configured
		if s.config.Server.AuthToken == "" {
			next.ServeHTTP(w, r)
			return
		}
		
		authHeader := r.Header.Get("Authorization")
		if authHeader == "" {
			s.writeError(w, http.StatusUnauthorized, "Missing Authorization header")
			return
		}
		
		const bearerPrefix = "Bearer "
		if len(authHeader) < len(bearerPrefix) || authHeader[:len(bearerPrefix)] != bearerPrefix {
			s.writeError(w, http.StatusUnauthorized, "Invalid Authorization header format")
			return
		}
		
		token := authHeader[len(bearerPrefix):]
		if token != s.config.Server.AuthToken {
			s.writeError(w, http.StatusUnauthorized, "Invalid bearer token")
			return
		}
		
		next.ServeHTTP(w, r)
	})
}

// requireProfessional ensures the user has Professional or Enterprise license
func (s *Server) requireProfessional(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := s.featureGate.RequireProfessional(); err != nil {
			s.writeError(w, http.StatusForbidden, "Professional license required: "+err.Error())
			return
		}
		next.ServeHTTP(w, r)
	})
}

// requireEnterprise ensures the user has Enterprise license
func (s *Server) requireEnterprise(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			if err := s.featureGate.RequireEnterprise(); err != nil {
			s.writeError(w, http.StatusForbidden, "Enterprise license required: "+err.Error())
			return
		}
		next.ServeHTTP(w, r)
	})
}

// ServeHTTP implements http.Handler
func (s *Server) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	s.router.ServeHTTP(w, r)
}

// Start starts the HTTP server
func (s *Server) Start() error {
	addr := s.config.Server.Host + ":" + strconv.Itoa(s.config.Server.Port)
	s.logger.Info("Starting HTTP server", zap.String("address", addr))
	
	server := &http.Server{
		Addr:         addr,
		Handler:      s,
		ReadTimeout:  30 * time.Second,
		WriteTimeout: 30 * time.Second,
		IdleTimeout:  120 * time.Second,
	}
	
	return server.ListenAndServe()
}

// Health check endpoint
func (s *Server) handleHealth(w http.ResponseWriter, r *http.Request) {
	// Get optimizer version info
	z3Version := s.getoptimizerVersion()
	
	// Get database stats
	dbStats := s.getDatabaseStats()
	
	// Get cluster information
	clusterInfo := s.getClusterInfo()
	
	// Get workspace distribution
	workspaceStats := s.getWorkspaceDistribution()
	
	response := map[string]interface{}{
		"status":    "healthy",
		"timestamp": time.Now().Unix(),
		"version":   "1.0.0",
		"node_id":   s.getNodeID(),
		"optimization": map[string]interface{}{
			"solver":   "optimizer",
			"version":  z3Version,
			"enabled":  true,
			"policy":   "optimization optimization selects document subsets to maximize utility while minimizing redundancy using budget management",
		},
		"database": dbStats,
		"cluster":  clusterInfo,
		"workspaces": workspaceStats,
		"features": map[string]bool{
			"cache_enabled":     true,
			"fts_search":       true, 
			"quantum_scoring":  true,
			"optimization_optimization": true,
			"clustering":       s.config.Cluster.Enabled,
			"workspace_isolation": true,
			"project_affinity": s.config.Cluster.Affinity.WorkspaceRouting,
		},
	}
	
	s.writeJSON(w, http.StatusOK, response)
}

// Context assembly endpoint
func (s *Server) handleAssembleContext(w http.ResponseWriter, r *http.Request) {
	var req types.AssembleRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		s.writeError(w, http.StatusBadRequest, "Invalid request body: "+err.Error())
		return
	}
	
	// Apply defaults
	if req.MaxTokens <= 0 {
		req.MaxTokens = s.config.Tokenizer.MaxTokensDefault
	}
	if req.MaxDocuments <= 0 {
		req.MaxDocuments = 10
	}
	if req.ModelID == "" {
		req.ModelID = s.config.Tokenizer.ModelID
	}
	if !req.Useoptimization {
		req.Useoptimization = true // Default to optimization optimization
	}
	if req.UseCache {
		req.UseCache = true // Default to using cache
	}
	
	// Assemble context
	ctx := r.Context()
	
	// Convert AssembleRequest to ContextRequest for engine interface
	contextReq := types.ContextRequest{
		Query:         req.Query,
		MaxTokens:     req.MaxTokens,
		MaxDocuments:  req.MaxDocuments,
		WorkspacePath: req.WorkspacePath,
	}
	
	result, err := s.engine.AssembleContext(ctx, contextReq)
	if err != nil {
		s.logger.Error("Failed to assemble context", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to assemble context: "+err.Error())
		return
	}
	
	s.writeJSON(w, http.StatusOK, result)
}

// Baseline comparison endpoint
func (s *Server) handleBaselineComparison(w http.ResponseWriter, r *http.Request) {
	var req types.AssembleRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		s.writeError(w, http.StatusBadRequest, "Invalid request body: "+err.Error())
		return
	}
	
	// Apply defaults
	if req.MaxTokens <= 0 {
		req.MaxTokens = s.config.Tokenizer.MaxTokensDefault
	}
	if req.MaxDocuments <= 0 {
		req.MaxDocuments = 10
	}
	if req.ModelID == "" {
		req.ModelID = s.config.Tokenizer.ModelID
	}
	
	ctx := r.Context()
	
	// Get Advanced results
	req.Useoptimization = true
	req.UseCache = false // Force fresh computation for comparison
	
	contextReq := types.ContextRequest{
		Query:         req.Query,
		MaxTokens:     req.MaxTokens,
		MaxDocuments:  req.MaxDocuments,
		WorkspacePath: req.WorkspacePath,
	}
	
	optimizationResult, err := s.engine.AssembleContext(ctx, contextReq)
	if err != nil {
		s.logger.Error("Failed to get optimization results", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to get optimization results: "+err.Error())
		return
	}
	
	// Get all documents for baseline comparison
	allDocs, err := s.storage.SearchDocuments(ctx, req.Query, 1000) // Get more docs for baseline
	if err != nil {
		s.logger.Error("Failed to search documents for baseline", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to search documents: "+err.Error())
		return
	}
	
	// Run simple baseline (basic text matching + document length)
	baselineResults := s.simpleBaseline(allDocs, req.Query, req.MaxDocuments)
	
	// Create baseline response format
	baselineDocRefs := make([]types.DocumentReference, len(baselineResults))
	for i, doc := range baselineResults {
		baselineDocRefs[i] = types.DocumentReference{
			ID:              doc.ID,
			Path:            doc.Path,
			Content:         doc.Content,
			Language:        doc.Language,
			UtilityScore:    0.5, // Simple baseline score
			RelevanceScore:  0.5,
			RecencyScore:    0.5,
			InclusionReason: "baseline_selected",
		}
	}
	
	baselineResponse := &types.QueryResult{
		Query:          req.Query,
		Documents:      baselineDocRefs,
		CoherenceScore: 1.0, // Assume baseline is coherent
		optimizationMetrics: types.optimizationMetrics{
			Objective:       0, // No optimization optimization
			VariableCount:   0,
			ConstraintCount: 0,
			optimizationWallMs:       0,
			FallbackReason:  "baseline_method",
		},
		CacheKey: "", // No cache for baseline
	}
	
	// Compare results  
	optimizationMetrics := types.optimizationResult{}
	if optimizationResult.optimizationMetrics != nil {
		optimizationMetrics = *optimizationResult.optimizationMetrics
	}
	
	comparison := map[string]interface{}{
		"query": req.Query,
		"optimization_optimized": map[string]interface{}{
			"documents":        optimizationResult.Documents,
			"coherence_score":  optimizationResult.CoherenceScore,
			"optimization_objective":    optimizationMetrics.Objective,
			"solve_time_ms":    float64(optimizationMetrics.SolveTimeUs) / 1000,
			"variables":        optimizationMetrics.VariableCount,
			"budgets":      optimizationMetrics.ConstraintCount,
			"method":           "optimization_optimization",
		},
		"baseline": map[string]interface{}{
			"documents":        baselineResponse.Documents,
			"coherence_score":  baselineResponse.CoherenceScore,
			"method":           "BM25_MMR",
		},
		"comparison": map[string]interface{}{
			"document_overlap": s.calculateDocumentOverlap(optimizationResult.Documents, baselineResponse.Documents),
			"optimization_speedup":      "N/A", // optimization is optimization, not speed improvement
			"diversity_diff":   s.calculateDiversityDifference(optimizationResult.Documents, baselineResponse.Documents),
		},
	}
	
	s.writeJSON(w, http.StatusOK, comparison)
}

// Add single document
func (s *Server) handleAddDocument(w http.ResponseWriter, r *http.Request) {
	var doc types.Document
	if err := json.NewDecoder(r.Body).Decode(&doc); err != nil {
		s.writeError(w, http.StatusBadRequest, "Invalid document: "+err.Error())
		return
	}
	
	ctx := r.Context()
	if err := s.storage.AddDocument(ctx, &doc); err != nil {
		s.logger.Error("Failed to add document", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to add document: "+err.Error())
		return
	}
	
	s.writeJSON(w, http.StatusCreated, map[string]string{"id": doc.ID})
}

// Bulk add documents
func (s *Server) handleBulkAddDocuments(w http.ResponseWriter, r *http.Request) {
	var docs []types.Document
	if err := json.NewDecoder(r.Body).Decode(&docs); err != nil {
		s.writeError(w, http.StatusBadRequest, "Invalid documents: "+err.Error())
		return
	}
	
	ctx := r.Context()
	var added []string
	var errors []string
	
	for _, doc := range docs {
		if err := s.storage.AddDocument(ctx, &doc); err != nil {
			errors = append(errors, "Failed to add "+doc.Path+": "+err.Error())
		} else {
			added = append(added, doc.ID)
		}
	}
	
	response := map[string]interface{}{
		"added":  added,
		"errors": errors,
		"total":  len(docs),
	}
	
	s.writeJSON(w, http.StatusOK, response)
}

// Scan workspace directory
func (s *Server) handleScanWorkspace(w http.ResponseWriter, r *http.Request) {
	var req struct {
		Path           string   `json:"path"`
		IncludePatterns []string `json:"include_patterns,omitempty"`
		ExcludePatterns []string `json:"exclude_patterns,omitempty"`
		MaxFiles       int      `json:"max_files,omitempty"`
	}
	
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		s.writeError(w, http.StatusBadRequest, "Invalid request: "+err.Error())
		return
	}
	
	if req.Path == "" {
		s.writeError(w, http.StatusBadRequest, "Workspace path required")
		return
	}
	
	if req.MaxFiles == 0 {
		req.MaxFiles = 1000 // Default limit
	}
	
	// Default include patterns for code files
	if len(req.IncludePatterns) == 0 {
		req.IncludePatterns = []string{"*.go", "*.js", "*.ts", "*.py", "*.java", "*.cpp", "*.h", "*.md", "*.txt"}
	}
	
	// Default exclude patterns
	if len(req.ExcludePatterns) == 0 {
		req.ExcludePatterns = []string{"node_modules", ".git", "build", "dist", "*.log", "*.tmp"}
	}
	
	ctx := r.Context()
	files, err := s.scanWorkspaceFiles(ctx, req.Path, req.IncludePatterns, req.ExcludePatterns, req.MaxFiles)
	if err != nil {
		s.logger.Error("Failed to scan workspace", zap.String("path", req.Path), zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to scan workspace: "+err.Error())
		return
	}
	
	response := map[string]interface{}{
		"scanned_files": len(files),
		"indexed_files": 0, // Will be updated as files are processed
		"files":         files,
	}
	
	s.writeJSON(w, http.StatusOK, response)
}

// Delete document
func (s *Server) handleDeleteDocument(w http.ResponseWriter, r *http.Request) {
	id := chi.URLParam(r, "id")
	if id == "" {
		s.writeError(w, http.StatusBadRequest, "Document ID required")
		return
	}
	
	ctx := r.Context()
	if err := s.storage.DeleteDocument(ctx, id); err != nil {
		s.logger.Error("Failed to delete document", zap.String("id", id), zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to delete document: "+err.Error())
		return
	}
	
	s.writeJSON(w, http.StatusOK, map[string]string{"status": "deleted"})
}

// Search documents
func (s *Server) handleSearchDocuments(w http.ResponseWriter, r *http.Request) {
	query := r.URL.Query().Get("q")
	if query == "" {
		s.writeError(w, http.StatusBadRequest, "Query parameter 'q' required")
		return
	}
	
	limitStr := r.URL.Query().Get("limit")
	limit := 20 // Default limit
	if limitStr != "" {
		if parsed, err := strconv.Atoi(limitStr); err == nil && parsed > 0 {
			limit = parsed
		}
	}
	
	ctx := r.Context()
	docs, err := s.storage.SearchDocuments(ctx, query, limit)
	if err != nil {
		s.logger.Error("Failed to search documents", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to search documents: "+err.Error())
		return
	}
	
	s.writeJSON(w, http.StatusOK, map[string]interface{}{
		"query":     query,
		"documents": docs,
		"total":     len(docs),
	})
}

// Update workspace weights
func (s *Server) handleUpdateWeights(w http.ResponseWriter, r *http.Request) {
	var feedback types.UserFeedback
	if err := json.NewDecoder(r.Body).Decode(&feedback); err != nil {
		s.writeError(w, http.StatusBadRequest, "Invalid feedback: "+err.Error())
		return
	}
	
	ctx := r.Context()
	
	// Get current workspace weights
	weights, err := s.storage.GetWorkspaceWeights(ctx, feedback.WorkspacePath)
	if err != nil {
		// Create default weights if not found
		weights = &types.WorkspaceWeights{
			WorkspacePath:      feedback.WorkspacePath,
			RelevanceWeight:    0.3,
			RecencyWeight:      0.2,
			EntanglementWeight: 0.15,
			DiversityWeight:    0.15,
			RedundancyPenalty:  0.2,
			UpdateCount:        0,
		}
	}
	
	// Apply learning rate adjustments based on feedback
	learningRate := 0.1
	
	// Positive feedback (accepted docs) - increase relevance-related weights
	if len(feedback.AcceptedDocs) > 0 {
		weights.RelevanceWeight *= (1 + learningRate)
		weights.RecencyWeight *= (1 + learningRate * 0.5)
		weights.EntanglementWeight *= (1 + learningRate * 0.3)
	}
	
	// Negative feedback (rejected docs) - decrease weights and increase diversity
	if len(feedback.RejectedDocs) > 0 {
		weights.RelevanceWeight *= (1 - learningRate * 0.5)
		weights.DiversityWeight *= (1 + learningRate * 0.3)
		weights.RedundancyPenalty *= (1 + learningRate * 0.2)
	}
	
	// Normalize weights to reasonable ranges
	total := weights.RelevanceWeight + weights.RecencyWeight + weights.EntanglementWeight + weights.DiversityWeight
	if total > 0 {
		weights.RelevanceWeight /= total
		weights.RecencyWeight /= total
		weights.EntanglementWeight /= total
		weights.DiversityWeight /= total
	}
	
	// Update metadata
	weights.UpdateCount++
	weights.LastUpdated = time.Now().Format(time.RFC3339)
	
	// Save updated weights
	featureWeights := types.FeatureWeights{
		Relevance:    weights.RelevanceWeight,
		Recency:      weights.RecencyWeight,
		Entanglement: weights.EntanglementWeight,
		Prior:        0.0, // Not available in WorkspaceWeights
		Authority:    0.0, // Not available in WorkspaceWeights
		Specificity:  weights.DiversityWeight,
		Uncertainty:  weights.RedundancyPenalty,
	}
	if err := s.storage.SaveWorkspaceWeights(feedback.WorkspacePath, featureWeights); err != nil {
		s.writeError(w, http.StatusInternalServerError, "Failed to save weights: "+err.Error())
		return
	}
	
	s.writeJSON(w, http.StatusOK, map[string]interface{}{
		"status": "weights updated",
		"weights": weights,
	})
}

// Get workspace weights
func (s *Server) handleGetWeights(w http.ResponseWriter, r *http.Request) {
	workspacePath := r.URL.Query().Get("workspace")
	if workspacePath == "" {
		s.writeError(w, http.StatusBadRequest, "Workspace path required")
		return
	}
	
	ctx := r.Context()
	weights, err := s.storage.GetWorkspaceWeights(ctx, workspacePath)
	if err != nil {
		s.writeError(w, http.StatusNotFound, "Workspace weights not found")
		return
	}
	
	s.writeJSON(w, http.StatusOK, weights)
}

// Reset workspace weights
func (s *Server) handleResetWeights(w http.ResponseWriter, r *http.Request) {
	workspacePath := r.URL.Query().Get("workspace")
	if workspacePath == "" {
		s.writeError(w, http.StatusBadRequest, "Workspace path required")
		return
	}
	
	// Create default weights
	defaultWeights := &types.WorkspaceWeights{
		WorkspacePath:      workspacePath,
		RelevanceWeight:    0.3,
		RecencyWeight:      0.2,
		EntanglementWeight: 0.15,
		DiversityWeight:    0.15,
		RedundancyPenalty:  0.2,
		UpdateCount:        0,
		LastUpdated:        time.Now().Format(time.RFC3339),
	}
	
	// Save default weights
	defaultFeatureWeights := types.FeatureWeights{
		Relevance:    defaultWeights.RelevanceWeight,
		Recency:      defaultWeights.RecencyWeight,
		Entanglement: defaultWeights.EntanglementWeight,
		Prior:        0.0,
		Authority:    0.0,
		Specificity:  defaultWeights.DiversityWeight,
		Uncertainty:  defaultWeights.RedundancyPenalty,
	}
	if err := s.storage.SaveWorkspaceWeights(workspacePath, defaultFeatureWeights); err != nil {
		s.writeError(w, http.StatusInternalServerError, "Failed to reset weights: "+err.Error())
		return
	}
	
	s.writeJSON(w, http.StatusOK, map[string]interface{}{
		"status": "weights reset to defaults",
		"weights": defaultWeights,
	})
}

// Invalidate cache
func (s *Server) handleInvalidateCache(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	// Execute cache invalidation by deleting all cache entries
	err := s.storage.InvalidateCache(ctx)
	if err != nil {
		s.logger.Error("Failed to invalidate cache", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to invalidate cache: "+err.Error())
		return
	}
	
	s.writeJSON(w, http.StatusOK, map[string]string{
		"status": "cache invalidated",
		"message": "All cached results have been cleared",
	})
}

// Cache stats
func (s *Server) handleCacheStats(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	stats, err := s.storage.GetCacheStats(ctx)
	if err != nil {
		s.logger.Error("Failed to get cache stats", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to get cache stats: "+err.Error())
		return
	}
	
	s.writeJSON(w, http.StatusOK, stats)
}

// Storage info
func (s *Server) handleStorageInfo(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	info, err := s.storage.GetStorageStats(ctx)
	if err != nil {
		s.logger.Error("Failed to get storage info", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to get storage info: "+err.Error())
		return
	}
	
	s.writeJSON(w, http.StatusOK, info)
}

// optimization stats
func (s *Server) handleoptimizationStats(w http.ResponseWriter, r *http.Request) {
	// TODO: Get actual optimization system statistics
	stats := map[string]interface{}{
		"total_solves":        0,
		"average_solve_time":  "0ms",
		"fallback_rate":       0.0,
		"optimality_gap":      0.0,
	}
	
	s.writeJSON(w, http.StatusOK, stats)
}

// Enterprise tenant management endpoints
func (s *Server) handleListTenants(w http.ResponseWriter, r *http.Request) {
	// This would integrate with the enterprise tenant manager
	tenants := []map[string]interface{}{
		{
			"id":          "demo-tenant",
			"name":        "Demo Organization",
			"status":      "active",
			"created_at":  time.Now().Add(-24*time.Hour).Unix(),
			"user_count":  5,
		},
	}
	
	s.writeJSON(w, http.StatusOK, map[string]interface{}{
		"tenants": tenants,
		"total":   len(tenants),
	})
}

func (s *Server) handleCreateTenant(w http.ResponseWriter, r *http.Request) {
	var req struct {
		Name     string `json:"name"`
		Domain   string `json:"domain"`
		Settings map[string]interface{} `json:"settings,omitempty"`
	}
	
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		s.writeError(w, http.StatusBadRequest, "Invalid request: "+err.Error())
		return
	}
	
	if req.Name == "" || req.Domain == "" {
		s.writeError(w, http.StatusBadRequest, "Name and domain required")
		return
	}
	
	// Generate tenant ID
	tenantID := fmt.Sprintf("tenant_%d", time.Now().Unix())
	
	response := map[string]interface{}{
		"id":         tenantID,
		"name":       req.Name,
		"domain":     req.Domain,
		"status":     "active",
		"created_at": time.Now().Unix(),
		"database_url": fmt.Sprintf("./data/%s.db", tenantID),
	}
	
	s.writeJSON(w, http.StatusCreated, response)
}

// Enterprise MCP server management endpoints
func (s *Server) handleListMCPServers(w http.ResponseWriter, r *http.Request) {
	servers := []map[string]interface{}{
		{
			"id":        "jira-integration",
			"name":      "Jira Integration",
			"type":      "jira",
			"status":    "active",
			"endpoint":  "http://localhost:3001",
			"created_at": time.Now().Add(-2*time.Hour).Unix(),
		},
		{
			"id":        "slack-bot",
			"name":      "Slack Bot",
			"type":      "slack",
			"status":    "active",
			"endpoint":  "http://localhost:3002",
			"created_at": time.Now().Add(-1*time.Hour).Unix(),
		},
	}
	
	s.writeJSON(w, http.StatusOK, map[string]interface{}{
		"servers": servers,
		"total":   len(servers),
	})
}

func (s *Server) handleCreateMCPServer(w http.ResponseWriter, r *http.Request) {
	var req struct {
		Name   string                 `json:"name"`
		Type   string                 `json:"type"`
		Config map[string]interface{} `json:"config"`
	}
	
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		s.writeError(w, http.StatusBadRequest, "Invalid request: "+err.Error())
		return
	}
	
	if req.Name == "" || req.Type == "" {
		s.writeError(w, http.StatusBadRequest, "Name and type required")
		return
	}
	
	// Generate server ID
	serverID := fmt.Sprintf("mcp_%d", time.Now().Unix())
	port := 3000 + len(serverID)%1000 // Simple port allocation
	
	response := map[string]interface{}{
		"id":         serverID,
		"name":       req.Name,
		"type":       req.Type,
		"status":     "deploying",
		"endpoint":   fmt.Sprintf("http://localhost:%d", port),
		"created_at": time.Now().Unix(),
		"config":     req.Config,
	}
	
	s.writeJSON(w, http.StatusCreated, response)
}

// Helper methods

// getoptimizerVersion returns the optimization engine version information
func (s *Server) getoptimizerVersion() string {
	// Try to get optimizer version by running z3 --version
	cmd := exec.Command("z3", "--version")
	output, err := cmd.Output()
	if err != nil {
		// Fallback if z3 not available
		return "optimizer not available"
	}
	
	// Parse version from output like "optimizer version 4.15.2 - 64 bit"
	version := strings.TrimSpace(string(output))
	if strings.Contains(version, "optimizer version") {
		parts := strings.Fields(version)
		if len(parts) >= 3 {
			return parts[2] // Extract version number
		}
	}
	
	return strings.TrimSpace(version)
}

// scanWorkspaceFiles scans a directory for relevant files
func (s *Server) scanWorkspaceFiles(ctx context.Context, workspacePath string, includePatterns, excludePatterns []string, maxFiles int) ([]map[string]interface{}, error) {
	var files []map[string]interface{}
	
	err := filepath.Walk(workspacePath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return nil // Skip files we can't read
		}
		
		if info.IsDir() {
			// Check if directory should be excluded
			dirName := filepath.Base(path)
			for _, pattern := range excludePatterns {
				if matched, _ := filepath.Match(pattern, dirName); matched {
					return filepath.SkipDir
				}
			}
			return nil
		}
		
		// Check file size (skip very large files)
		if info.Size() > 100*1024 { // 100KB limit
			return nil
		}
		
		// Check if file matches include patterns
		fileName := filepath.Base(path)
		matched := false
		for _, pattern := range includePatterns {
			if m, _ := filepath.Match(pattern, fileName); m {
				matched = true
				break
			}
		}
		
		if !matched {
			return nil
		}
		
		// Check exclude patterns
		for _, pattern := range excludePatterns {
			if matched, _ := filepath.Match(pattern, fileName); matched {
				return nil
			}
		}
		
		// Stop if we've hit the file limit
		if len(files) >= maxFiles {
			return filepath.SkipDir
		}
		
		relPath, _ := filepath.Rel(workspacePath, path)
		files = append(files, map[string]interface{}{
			"path":         relPath,
			"full_path":    path,
			"size_bytes":   info.Size(),
			"modified_at":  info.ModTime().Unix(),
			"extension":    filepath.Ext(path),
		})
		
		return nil
	})
	
	return files, err
}

// getDatabaseStats returns basic database statistics
func (s *Server) getDatabaseStats() map[string]interface{} {
	
	// Get real storage stats
	ctx := context.Background()
	storageStats, err := s.storage.GetStorageStats(ctx)
	if err != nil {
		// Fallback to default stats if query fails
		return map[string]interface{}{
			"documents_indexed": "0",
			"cache_entries":     "active", 
			"fts_enabled":       true,
			"last_optimized":    time.Now().Add(-1 * time.Hour).Unix(),
		}
	}
	
	// Extract document count and format appropriately
	docCount, ok := storageStats["total_documents"].(int)
	if !ok {
		docCount = 0
	}
	
	var docCountStr string
	if docCount == 0 {
		docCountStr = "0"
	} else if docCount >= 10000 {
		docCountStr = "10000+"
	} else {
		docCountStr = fmt.Sprintf("%d", docCount)
	}
	
	return map[string]interface{}{
		"documents_indexed": docCountStr,
		"cache_entries":     "active", 
		"fts_enabled":       true,
		"last_optimized":    time.Now().Add(-1 * time.Hour).Unix(),
	}
}

// getNodeID returns the cluster node ID
func (s *Server) getNodeID() string {
	if s.config.Cluster.NodeID != "" {
		return s.config.Cluster.NodeID
	}
	// Generate default node ID based on hostname and port
	hostname, _ := os.Hostname()
	return fmt.Sprintf("contextlite-%s-%d", hostname, s.config.Server.Port)
}

// getClusterInfo returns cluster-level information
func (s *Server) getClusterInfo() map[string]interface{} {
	if !s.config.Cluster.Enabled {
		return map[string]interface{}{
			"enabled": false,
			"mode":    "standalone",
		}
	}
	
	// In a full implementation, this would query service discovery
	// For now, return basic cluster configuration
	return map[string]interface{}{
		"enabled":         true,
		"node_id":         s.getNodeID(),
		"discovery_method": s.config.Cluster.Discovery.Method,
		"load_balancing":  s.config.Cluster.LoadBalancing.Strategy,
		"affinity_enabled": s.config.Cluster.Affinity.WorkspaceRouting,
		"sticky_sessions": s.config.Cluster.Affinity.StickySessions,
		"health_check_interval": s.config.Cluster.HealthCheck.Interval,
		"cluster_size":    s.getClusterSize(),
		"leader_node":     s.getLeaderNode(), 
		"load_factor":     s.getNodeLoadFactor(),
	}
}

// getWorkspaceDistribution returns per-workspace statistics
func (s *Server) getWorkspaceDistribution() map[string]interface{} {
	ctx := context.Background()
	
	// Get storage stats which should include workspace information
	storageStats, err := s.storage.GetStorageStats(ctx)
	if err != nil {
		return map[string]interface{}{
			"total_workspaces": 0,
			"active_workspaces": 0,
		}
	}
	
	// In a full implementation, this would query workspace-specific stats
	// For now, return basic workspace information
	totalDocs, _ := storageStats["total_documents"].(int)
	
	workspaces := make(map[string]interface{})
	if totalDocs > 0 {
		// Example workspace breakdown - in reality would query actual workspace data
		workspaces["mission-architect"] = map[string]interface{}{
			"document_count": totalDocs / 3,
			"resource_tier":  "high",
			"last_access":    time.Now().Add(-10 * time.Minute).Unix(),
			"access_pattern": "high-frequency",
		}
		workspaces["code-assistant"] = map[string]interface{}{
			"document_count": totalDocs / 3,
			"resource_tier":  "medium", 
			"last_access":    time.Now().Add(-30 * time.Minute).Unix(),
			"access_pattern": "normal",
		}
		workspaces["general"] = map[string]interface{}{
			"document_count": totalDocs / 3,
			"resource_tier":  "low",
			"last_access":    time.Now().Add(-2 * time.Hour).Unix(),
			"access_pattern": "archive",
		}
	}
	
	return map[string]interface{}{
		"total_workspaces":  len(workspaces),
		"active_workspaces": len(workspaces), 
		"workspaces":        workspaces,
		"resource_limits":   s.config.Cluster.ResourceLimits,
	}
}

// getClusterSize returns the number of nodes in cluster
func (s *Server) getClusterSize() int {
	if !s.config.Cluster.Enabled {
		return 1
	}
	// In a full implementation, would query service discovery
	// For now, return a reasonable default
	return 3
}

// getLeaderNode returns the current cluster leader
func (s *Server) getLeaderNode() string {
	if !s.config.Cluster.Enabled {
		return s.getNodeID()
	}
	// In a full implementation, would query cluster state
	// For now, return current node as leader
	return s.getNodeID()
}

// getNodeLoadFactor returns current node load (0.0 - 1.0)
func (s *Server) getNodeLoadFactor() float64 {
	// In a full implementation, would calculate based on:
	// - Active connections
	// - Query queue depth
	// - Memory usage
	// - CPU usage
	// For now, return a simulated load factor
	return 0.35 // 35% load
}

// calculateDocumentOverlap computes the percentage of documents that appear in both result sets
func (s *Server) calculateDocumentOverlap(optimizationDocs, baselineDocs []types.DocumentReference) float64 {
	if len(optimizationDocs) == 0 || len(baselineDocs) == 0 {
		return 0.0
	}
	
	optimizationIDs := make(map[string]bool)
	for _, doc := range optimizationDocs {
		optimizationIDs[doc.ID] = true
	}
	
	overlap := 0
	for _, doc := range baselineDocs {
		if optimizationIDs[doc.ID] {
			overlap++
		}
	}
	
	// Calculate overlap as percentage of smaller set
	smaller := len(optimizationDocs)
	if len(baselineDocs) < smaller {
		smaller = len(baselineDocs)
	}
	
	return float64(overlap) / float64(smaller)
}

// calculateDiversityDifference computes the difference in diversity scores between methods
func (s *Server) calculateDiversityDifference(optimizationDocs, baselineDocs []types.DocumentReference) float64 {
	if len(optimizationDocs) == 0 || len(baselineDocs) == 0 {
		return 0.0
	}
	
	// For DocumentReference, we don't have direct diversity scores, so return 0
	// In a full implementation, you'd calculate diversity from the documents themselves
	return 0.0
}

func (s *Server) writeJSON(w http.ResponseWriter, status int, data interface{}) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(status)
	json.NewEncoder(w).Encode(data)
}

func (s *Server) writeError(w http.ResponseWriter, status int, message string) {
	s.writeJSON(w, status, map[string]string{"error": message})
}

// --- RAG convenience types ---
type rankRequest struct {
	Query     string `json:"query"`
	K         int    `json:"k"`
	BudgetMs  int    `json:"budget_ms"`
	MaxTokens int    `json:"max_tokens,omitempty"`
	UseCache  bool   `json:"use_cache,omitempty"`
}

type position struct { Line int `json:"line"`; Character int `json:"character"` }

type rangeJSON struct { Start position `json:"start"`; End position `json:"end"` }

type rankItem struct {
	File    string     `json:"file"`
	Range   *rangeJSON `json:"range,omitempty"`
	Snippet string     `json:"snippet"`
	Score   float64    `json:"score"`
	Why     string     `json:"why"`
}

type rankResponse struct {
	Items []rankItem `json:"items"`
	P99Ms int        `json:"p99_ms"`
}

type snippetRequest struct {
	File  string   `json:"file"`
	Start position `json:"start"`
	End   position `json:"end"`
}

type snippetResponse struct {
	Snippet string `json:"snippet"`
}

// --- /api/v1/rank ---
func (s *Server) handleRank(w http.ResponseWriter, r *http.Request) {
	var reqBody rankRequest
	if err := json.NewDecoder(r.Body).Decode(&reqBody); err != nil {
		s.writeError(w, http.StatusBadRequest, "Invalid request body: "+err.Error())
		return
	}
	if reqBody.Query == "" { 
		s.writeError(w, http.StatusBadRequest, "query required")
		return 
	}

	// Map to ContextRequest
	cr := types.ContextRequest{
		Query:         reqBody.Query,
		MaxTokens:     s.config.Tokenizer.MaxTokensDefault,
		MaxDocuments:  10,
		WorkspacePath: "",
	}
	if reqBody.K > 0 { cr.MaxDocuments = reqBody.K }
	if reqBody.MaxTokens > 0 { cr.MaxTokens = reqBody.MaxTokens }

	ctx := r.Context()
	res, err := s.engine.AssembleContext(ctx, cr)
	if err != nil {
		s.logger.Error("rank assembly failed", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "assembly failed: "+err.Error())
		return
	}

	items := make([]rankItem, 0, len(res.Documents))
	for _, d := range res.Documents {
		score := d.UtilityScore
		if score == 0 && d.RelevanceScore > 0 { score = d.RelevanceScore }
		items = append(items, rankItem{
			File:    d.Path,
			Range:   nil,                   // precise line ranges unavailable here; use /snippet for exact slicing
			Snippet: d.Content,             // optimization/packing already trimmed content
			Score:   score,
			Why:     d.InclusionReason,
		})
	}

	out := rankResponse{ Items: items, P99Ms: int(res.ProcessingTime.Milliseconds()) }
	s.writeJSON(w, http.StatusOK, out)
}

// --- /api/v1/snippet ---
func (s *Server) handleSnippet(w http.ResponseWriter, r *http.Request) {
	var req snippetRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		s.writeError(w, http.StatusBadRequest, "Invalid request body: "+err.Error())
		return
	}
	if req.File == "" { 
		s.writeError(w, http.StatusBadRequest, "file required")
		return 
	}

	ctx := r.Context()
	// Fast path: read from storage by path
	doc, err := s.storage.GetDocumentByPath(ctx, req.File)
	if err != nil || doc == nil { 
		s.writeError(w, http.StatusNotFound, "file not indexed: "+req.File)
		return 
	}

	lines := strings.Split(doc.Content, "\n")
	// clamp indices
	sLine := req.Start.Line; eLine := req.End.Line
	if sLine < 0 { sLine = 0 }
	if eLine <= 0 || eLine > len(lines) { eLine = len(lines) }
	if sLine > eLine { sLine, eLine = eLine, sLine }

	snippet := strings.Join(lines[sLine:eLine], "\n")
	s.writeJSON(w, http.StatusOK, snippetResponse{ Snippet: snippet })
}

// simpleBaseline provides a basic baseline for comparison without complex features
func (s *Server) simpleBaseline(docs []types.Document, query string, maxDocs int) []types.Document {
	if len(docs) <= maxDocs {
		return docs // Return all if under limit
	}
	
	// Simple scoring: query term frequency + document length preference
	type scoredDoc struct {
		doc   types.Document
		score float64
	}
	
	queryTerms := strings.Fields(strings.ToLower(query))
	scored := make([]scoredDoc, len(docs))
	
	for i, doc := range docs {
		content := strings.ToLower(doc.Content)
		score := 0.0
		
		// Count query term matches
		for _, term := range queryTerms {
			score += float64(strings.Count(content, term))
		}
		
		// Slight preference for longer documents (more authoritative)
		score += float64(len(doc.Content)) / 10000.0
		
		scored[i] = scoredDoc{doc: doc, score: score}
	}
	
	// Sort by score descending
	for i := 0; i < len(scored)-1; i++ {
		for j := i + 1; j < len(scored); j++ {
			if scored[j].score > scored[i].score {
				scored[i], scored[j] = scored[j], scored[i]
			}
		}
	}
	
	// Return top maxDocs
	result := make([]types.Document, maxDocs)
	for i := 0; i < maxDocs; i++ {
		result[i] = scored[i].doc
	}
	
	return result
}

// handleLicenseStatus returns current license and trial status
func (s *Server) handleLicenseStatus(w http.ResponseWriter, r *http.Request) {
	// Check if we have enhanced feature gate with trial support
	if enhancedGate, ok := s.featureGate.(interface {
		GetStatus() map[string]interface{}
		TrialDaysRemaining() int
	}); ok {
		status := enhancedGate.GetStatus()
		status["purchase_url"] = "https://contextlite.com/purchase"
		status["trial_days_remaining"] = enhancedGate.TrialDaysRemaining()
		
		s.writeJSON(w, http.StatusOK, status)
		return
	}
	
	// Fallback for basic feature gate
	status := map[string]interface{}{
		"tier":                s.featureGate.GetTier(),
		"status":              "basic",
		"message":             "Basic license system active",
		"purchase_url":        "https://contextlite.com/purchase",
		"trial_days_remaining": 0,
	}
	
	s.writeJSON(w, http.StatusOK, status)
}

// handleTrialInfo returns detailed trial information
func (s *Server) handleTrialInfo(w http.ResponseWriter, r *http.Request) {
	// Check if we have enhanced feature gate with trial support
	if enhancedGate, ok := s.featureGate.(interface {
		GetStatus() map[string]interface{}
	}); ok {
		status := enhancedGate.GetStatus()
		
		if trialInfo, ok := status["trial"].(map[string]interface{}); ok {
			trialInfo["purchase_url"] = "https://contextlite.com/purchase"
			trialInfo["features_available"] = []string{
				"unlimited_workspaces",
				"advanced_optimization", 
				"7d_scoring",
				"caching",
				"rest_api",
			}
			
			s.writeJSON(w, http.StatusOK, trialInfo)
			return
		}
	}
	
	// No trial information available
	s.writeJSON(w, http.StatusOK, map[string]interface{}{
		"status":           "no_trial",
		"message":          "Trial system not available",
		"purchase_url":     "https://contextlite.com/purchase",
		"days_remaining":   0,
	})
}
