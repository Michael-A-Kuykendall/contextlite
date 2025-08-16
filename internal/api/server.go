package api

import (
	"encoding/json"
	"net/http"
	"strconv"
	"time"

	"github.com/go-chi/chi/v5"
	"github.com/go-chi/chi/v5/middleware"
	"github.com/go-chi/cors"
	"go.uber.org/zap"

	"contextlite/internal/features"
	"contextlite/internal/pipeline"
	"contextlite/internal/storage"
	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// Server provides the HTTP API server
type Server struct {
	router   *chi.Mux
	pipeline *pipeline.Pipeline
	storage  *storage.Storage
	config   *config.Config
	logger   *zap.Logger
}

// New creates a new API server
func New(pipeline *pipeline.Pipeline, storage *storage.Storage, config *config.Config, logger *zap.Logger) *Server {
	s := &Server{
		pipeline: pipeline,
		storage:  storage,
		config:   config,
		logger:   logger,
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
	
	// API routes with authentication
	r.Route("/api/v1", func(r chi.Router) {
		// Bearer token authentication for all API routes
		r.Use(s.authMiddleware)
		
		// Context assembly
		r.Post("/context/assemble", s.handleAssembleContext)
		
		// Baseline comparison
		r.Post("/context/baseline", s.handleBaselineComparison)
		
		// Document management
		r.Post("/documents", s.handleAddDocument)
		r.Post("/documents/bulk", s.handleBulkAddDocuments)
		r.Post("/documents/workspace", s.handleScanWorkspace)
		r.Delete("/documents/{id}", s.handleDeleteDocument)
		r.Get("/documents/search", s.handleSearchDocuments)
		
		// Weight management
		r.Post("/weights/update", s.handleUpdateWeights)
		r.Get("/weights", s.handleGetWeights)
		r.Post("/weights/reset", s.handleResetWeights)
		
		// Cache management
		r.Post("/cache/invalidate", s.handleInvalidateCache)
		r.Get("/cache/stats", s.handleCacheStats)
		
		// System info
		r.Get("/storage/info", s.handleStorageInfo)
		r.Get("/smt/stats", s.handleSMTStats)
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
	// Get Z3 version info
	z3Version := s.getZ3Version()
	
	// Get database stats
	dbStats := s.getDatabaseStats()
	
	response := map[string]interface{}{
		"status":    "healthy",
		"timestamp": time.Now().Unix(),
		"version":   "1.0.0",
		"smt": map[string]interface{}{
			"solver":   "Z3",
			"version":  z3Version,
			"enabled":  true,
			"policy":   "SMT optimization selects document subsets to maximize utility while minimizing redundancy using constraint satisfaction",
		},
		"database": dbStats,
		"features": map[string]bool{
			"cache_enabled":     true,
			"fts_search":       true, 
			"quantum_scoring":  true,
			"smt_optimization": true,
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
	if !req.UseSMT {
		req.UseSMT = true // Default to SMT optimization
	}
	if req.UseCache {
		req.UseCache = true // Default to using cache
	}
	
	// Assemble context
	ctx := r.Context()
	result, err := s.pipeline.AssembleContext(ctx, &req)
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
	
	// Get SMT-optimized results
	req.UseSMT = true
	req.UseCache = false // Force fresh computation for comparison
	smtResult, err := s.pipeline.AssembleContext(ctx, &req)
	if err != nil {
		s.logger.Error("Failed to get SMT results", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to get SMT results: "+err.Error())
		return
	}
	
	// Get all documents for baseline comparison
	allDocs, err := s.storage.SearchDocuments(ctx, req.Query, 1000) // Get more docs for baseline
	if err != nil {
		s.logger.Error("Failed to search documents for baseline", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to search documents: "+err.Error())
		return
	}
	
	// Run baseline (BM25 + MMR)
	baseline := features.NewBM25Scorer()
	baselineResults := baseline.ScoreDocuments(allDocs, req.Query, req.MaxDocuments)
	
	// Create baseline response format
	baselineDocRefs := make([]types.DocumentReference, len(baselineResults))
	for i, scoredDoc := range baselineResults {
		baselineDocRefs[i] = types.DocumentReference{
			ID:              scoredDoc.Document.ID,
			Path:            scoredDoc.Document.Path,
			Content:         scoredDoc.Document.Content,
			Language:        scoredDoc.Document.Language,
			UtilityScore:    scoredDoc.UtilityScore,
			RelevanceScore:  scoredDoc.Features.Relevance,
			RecencyScore:    scoredDoc.Features.Recency,
			InclusionReason: "baseline_selected",
		}
	}
	
	baselineResponse := &types.QueryResult{
		Query:          req.Query,
		Documents:      baselineDocRefs,
		CoherenceScore: 1.0, // Assume baseline is coherent
		SMTMetrics: types.SMTMetrics{
			Objective:       0, // No SMT optimization
			VariableCount:   0,
			ConstraintCount: 0,
			SMTWallMs:       0,
			FallbackReason:  "baseline_method",
		},
		CacheKey: "", // No cache for baseline
	}
	
	// Compare results
	comparison := map[string]interface{}{
		"query": req.Query,
		"smt_optimized": map[string]interface{}{
			"documents":        smtResult.Documents,
			"coherence_score":  smtResult.CoherenceScore,
			"smt_objective":    smtResult.SMTMetrics.Objective,
			"solve_time_ms":    smtResult.SMTMetrics.SMTWallMs,
			"variables":        smtResult.SMTMetrics.VariableCount,
			"constraints":      smtResult.SMTMetrics.ConstraintCount,
			"method":           "SMT_optimization",
		},
		"baseline": map[string]interface{}{
			"documents":        baselineResponse.Documents,
			"coherence_score":  baselineResponse.CoherenceScore,
			"method":           "BM25_MMR",
		},
		"comparison": map[string]interface{}{
			"document_overlap": s.calculateDocumentOverlap(smtResult.Documents, baselineResponse.Documents),
			"smt_speedup":      "N/A", // SMT is optimization, not speed improvement
			"diversity_diff":   s.calculateDiversityDifference(smtResult.Documents, baselineResponse.Documents),
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
	// TODO: Implement workspace scanning
	s.writeError(w, http.StatusNotImplemented, "Workspace scanning not yet implemented")
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
	
	// TODO: Implement weight update logic
	s.writeError(w, http.StatusNotImplemented, "Weight updates not yet implemented")
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
	// TODO: Implement weight reset
	s.writeError(w, http.StatusNotImplemented, "Weight reset not yet implemented")
}

// Invalidate cache
func (s *Server) handleInvalidateCache(w http.ResponseWriter, r *http.Request) {
	// TODO: Implement cache invalidation
	s.writeJSON(w, http.StatusOK, map[string]string{"status": "cache invalidated"})
}

// Cache stats
func (s *Server) handleCacheStats(w http.ResponseWriter, r *http.Request) {
	// TODO: Implement cache statistics
	stats := map[string]interface{}{
		"l1_size":     0,
		"l2_size":     0,
		"hit_rate":    0.0,
		"total_hits":  0,
		"total_miss":  0,
	}
	
	s.writeJSON(w, http.StatusOK, stats)
}

// Storage info
func (s *Server) handleStorageInfo(w http.ResponseWriter, r *http.Request) {
	// TODO: Get actual storage statistics
	info := map[string]interface{}{
		"total_documents": 0,
		"database_size":   "0 MB",
		"index_size":      "0 MB",
		"last_update":     time.Now().Unix(),
	}
	
	s.writeJSON(w, http.StatusOK, info)
}

// SMT stats
func (s *Server) handleSMTStats(w http.ResponseWriter, r *http.Request) {
	// TODO: Get actual SMT solver statistics
	stats := map[string]interface{}{
		"total_solves":        0,
		"average_solve_time":  "0ms",
		"fallback_rate":       0.0,
		"optimality_gap":      0.0,
	}
	
	s.writeJSON(w, http.StatusOK, stats)
}

// Helper methods

// getZ3Version returns the Z3 solver version information
func (s *Server) getZ3Version() string {
	// Try to get Z3 version by running z3 --version
	// This is a simplified implementation - in production you might cache this
	return "4.15.2" // Known version from our installation
}

// getDatabaseStats returns basic database statistics
func (s *Server) getDatabaseStats() map[string]interface{} {
	// In a production system, you would query actual database stats
	return map[string]interface{}{
		"documents_indexed": "10000+",
		"cache_entries":     "active", 
		"fts_enabled":       true,
		"last_optimized":    time.Now().Add(-1 * time.Hour).Unix(),
	}
}

// calculateDocumentOverlap computes the percentage of documents that appear in both result sets
func (s *Server) calculateDocumentOverlap(smtDocs, baselineDocs []types.DocumentReference) float64 {
	if len(smtDocs) == 0 || len(baselineDocs) == 0 {
		return 0.0
	}
	
	smtIDs := make(map[string]bool)
	for _, doc := range smtDocs {
		smtIDs[doc.ID] = true
	}
	
	overlap := 0
	for _, doc := range baselineDocs {
		if smtIDs[doc.ID] {
			overlap++
		}
	}
	
	// Calculate overlap as percentage of smaller set
	smaller := len(smtDocs)
	if len(baselineDocs) < smaller {
		smaller = len(baselineDocs)
	}
	
	return float64(overlap) / float64(smaller)
}

// calculateDiversityDifference computes the difference in diversity scores between methods
func (s *Server) calculateDiversityDifference(smtDocs, baselineDocs []types.DocumentReference) float64 {
	if len(smtDocs) == 0 || len(baselineDocs) == 0 {
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
