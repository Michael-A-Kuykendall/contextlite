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
	
	// Health check
	r.Get("/health", s.handleHealth)
	
	// API routes
	r.Route("/api/v1", func(r chi.Router) {
		// Context assembly
		r.Post("/context/assemble", s.handleAssembleContext)
		
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
		r.Get("/optimization/stats", s.handleoptimizationStats)
	})
	
	s.router = r
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
	response := map[string]interface{}{
		"status":    "healthy",
		"timestamp": time.Now().Unix(),
		"version":   "1.0.0",
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
	result, err := s.pipeline.AssembleContext(ctx, &req)
	if err != nil {
		s.logger.Error("Failed to assemble context", zap.Error(err))
		s.writeError(w, http.StatusInternalServerError, "Failed to assemble context: "+err.Error())
		return
	}
	
	s.writeJSON(w, http.StatusOK, result)
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

// Helper methods

func (s *Server) writeJSON(w http.ResponseWriter, status int, data interface{}) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(status)
	json.NewEncoder(w).Encode(data)
}

func (s *Server) writeError(w http.ResponseWriter, status int, message string) {
	s.writeJSON(w, status, map[string]string{"error": message})
}
