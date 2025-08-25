package storage

import (
	"context"
	"database/sql"
	"embed"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"strings"
	"time"

	"contextlite/pkg/tokens"
	"contextlite/pkg/types"

	"crypto/sha256"
	_ "modernc.org/sqlite"
)

//go:embed schema.sql
var schemaFS embed.FS

// Storage provides SQLite storage operations
type Storage struct {
	db *sql.DB
	// Cache statistics
	cacheHits   int64
	cacheMisses int64
}

// CacheStats represents cache performance metrics
// Remove the local CacheStats type since we'll use the one from types
// type CacheStats struct {
// 	Hits     int64   `json:"hits"`
// 	Misses   int64   `json:"misses"`
// 	HitRate  float64 `json:"hit_rate"`
// 	L1Size   int     `json:"l1_size"`
// 	L2Size   int     `json:"l2_size"`
// }

// New creates a new Storage instance
func New(dbPath string) (*Storage, error) {
	// Basic path validation
	if dbPath == "" {
		return nil, fmt.Errorf("database path cannot be empty")
	}
	
	db, err := sql.Open("sqlite", dbPath)
	if err != nil {
		return nil, fmt.Errorf("failed to open database: %w", err)
	}

	// Apply performance pragmas
	pragmas := []string{
		"PRAGMA journal_mode = WAL",
		"PRAGMA synchronous = NORMAL",
		"PRAGMA cache_size = -64000",
		"PRAGMA temp_store = MEMORY",
		"PRAGMA mmap_size = 268435456",
	}

	for _, pragma := range pragmas {
		if _, err := db.Exec(pragma); err != nil {
			db.Close()
			return nil, fmt.Errorf("failed to apply pragma %s: %w", pragma, err)
		}
	}

	storage := &Storage{db: db}

	// Initialize schema
	if err := storage.initSchema(); err != nil {
		db.Close()
		return nil, fmt.Errorf("failed to initialize schema: %w", err)
	}

	// Apply migrations
	if err := storage.applyMigrations(); err != nil {
		db.Close()
		return nil, fmt.Errorf("failed to apply migrations: %w", err)
	}

	return storage, nil
}

// Close closes the database connection
func (s *Storage) Close() error {
	return s.db.Close()
}

// GetStorageStats returns real database statistics
func (s *Storage) GetStorageStats(ctx context.Context) (map[string]interface{}, error) {
	stats := make(map[string]interface{})
	
	// Get document count
	var docCount int
	err := s.db.QueryRowContext(ctx, "SELECT COUNT(*) FROM documents").Scan(&docCount)
	if err != nil {
		return nil, fmt.Errorf("failed to get document count: %w", err)
	}
	stats["total_documents"] = docCount
	
	// Get database size (in pages * page_size)
	var pageCount, pageSize int64
	err = s.db.QueryRowContext(ctx, "PRAGMA page_count").Scan(&pageCount)
	if err != nil {
		return nil, fmt.Errorf("failed to get page count: %w", err)
	}
	err = s.db.QueryRowContext(ctx, "PRAGMA page_size").Scan(&pageSize)
	if err != nil {
		return nil, fmt.Errorf("failed to get page size: %w", err)
	}
	
	dbSizeBytes := pageCount * pageSize
	stats["database_size"] = fmt.Sprintf("%.2f MB", float64(dbSizeBytes)/(1024*1024))
	
	// Get FTS index size (estimate)
	ftsPages := pageCount / 4 // Estimate FTS as 25% of total
	ftsSizeBytes := ftsPages * pageSize
	stats["index_size"] = fmt.Sprintf("%.2f MB", float64(ftsSizeBytes)/(1024*1024))
	
	// Get last update time
	var lastUpdate time.Time
	err = s.db.QueryRowContext(ctx, `
		SELECT MAX(created_at) FROM documents
	`).Scan(&lastUpdate)
	if err != nil {
		lastUpdate = time.Now()
	}
	stats["last_update"] = lastUpdate.Unix()
	
	// Additional useful stats
	var avgDocSize sql.NullFloat64
	err = s.db.QueryRowContext(ctx, `
		SELECT AVG(LENGTH(content)) FROM documents
	`).Scan(&avgDocSize)
	if err == nil && avgDocSize.Valid {
		stats["avg_document_size"] = fmt.Sprintf("%.0f chars", avgDocSize.Float64)
	}
	
	return stats, nil
}

// GetWorkspaceStats returns workspace-specific statistics
func (s *Storage) GetWorkspaceStats(workspacePath string) (*types.WorkspaceStats, error) {
	ctx := context.Background()
	
	// Count documents in this workspace
	var docCount int
	err := s.db.QueryRowContext(ctx, `
		SELECT COUNT(*) FROM documents WHERE path LIKE ?
	`, workspacePath+"%").Scan(&docCount)
	if err != nil {
		return nil, fmt.Errorf("failed to count workspace documents: %w", err)
	}
	
	// Get total tokens in workspace
	var totalTokens sql.NullInt64
	err = s.db.QueryRowContext(ctx, `
		SELECT SUM(token_count) FROM documents WHERE path LIKE ?
	`, workspacePath+"%").Scan(&totalTokens)
	if err != nil {
		totalTokens.Int64 = 0 // Default if query fails
	}
	
	// Get average file size
	var avgFileSize sql.NullFloat64
	err = s.db.QueryRowContext(ctx, `
		SELECT AVG(LENGTH(content)) FROM documents WHERE path LIKE ?
	`, workspacePath+"%").Scan(&avgFileSize)
	if err != nil {
		avgFileSize.Float64 = 0 // Default if query fails
	}
	
	// Get languages (simplified - just take first few)
	rows, err := s.db.QueryContext(ctx, `
		SELECT DISTINCT lang FROM documents WHERE path LIKE ? AND lang != '' LIMIT 10
	`, workspacePath+"%")
	languages := []string{}
	if err == nil {
		defer rows.Close()
		for rows.Next() {
			var lang string
			if err := rows.Scan(&lang); err == nil {
				languages = append(languages, lang)
			}
		}
	}
	
	// Get last indexed time (most recent document)
	var lastIndexed time.Time
	err = s.db.QueryRowContext(ctx, `
		SELECT MAX(updated_at) FROM documents WHERE path LIKE ?
	`, workspacePath+"%").Scan(&lastIndexed)
	if err != nil {
		lastIndexed = time.Now() // Default if query fails
	}
	
	return &types.WorkspaceStats{
		Path:            workspacePath,
		DocumentCount:   docCount,
		TotalTokens:     totalTokens.Int64,
		LastIndexed:     lastIndexed,
		Languages:       languages,
		AverageFileSize: int64(avgFileSize.Float64),
	}, nil
}

// GetCacheStats returns cache performance statistics
func (s *Storage) GetCacheStats(ctx context.Context) (*types.CacheStats, error) {
	// Get L2 cache size (number of cached results)
	var l2Size int
	err := s.db.QueryRowContext(ctx, "SELECT COUNT(*) FROM query_cache").Scan(&l2Size)
	if err != nil {
		return nil, fmt.Errorf("failed to get cache size: %w", err)
	}
	
	total := s.cacheHits + s.cacheMisses
	hitRate := 0.0
	if total > 0 {
		hitRate = float64(s.cacheHits) / float64(total)
	}
	
	return &types.CacheStats{
		Hits:    s.cacheHits,
		Misses:  s.cacheMisses,
		HitRate: hitRate,
		L1Size:  0, // L1 cache not implemented in this version
		L2Size:  l2Size,
	}, nil
}

// initSchema initializes the database schema
func (s *Storage) initSchema() error {
	schema, err := schemaFS.ReadFile("schema.sql")
	if err != nil {
		return fmt.Errorf("failed to read schema: %w", err)
	}

	// Split and execute each statement
	statements := strings.Split(string(schema), ";")
	for _, stmt := range statements {
		stmt = strings.TrimSpace(stmt)
		if stmt == "" {
			continue
		}
		
		// Special handling for FTS tables since IF NOT EXISTS doesn't work with them
		if strings.Contains(stmt, "CREATE VIRTUAL TABLE") && strings.Contains(stmt, "documents_fts") {
			// Check if FTS table exists
			var count int
			err := s.db.QueryRow("SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='documents_fts'").Scan(&count)
			if err != nil {
				return fmt.Errorf("failed to check FTS table existence: %w", err)
			}
			if count > 0 {
				continue // Skip creating FTS table if it already exists
			}
			// Remove IF NOT EXISTS from FTS statement
			stmt = strings.Replace(stmt, "IF NOT EXISTS ", "", 1)
		}
		
		if _, err := s.db.Exec(stmt); err != nil {
			return fmt.Errorf("failed to execute schema statement: %w", err)
		}
	}

	return nil
}

// AddDocument adds a document to the database
func (s *Storage) AddDocument(ctx context.Context, doc *types.Document) error {
	// Generate ID if not provided
	if doc.ID == "" {
		hash := sha256.Sum256([]byte(doc.Content))
		doc.ID = hex.EncodeToString(hash[:8])
	}

	// Generate content hash
	hash := sha256.Sum256([]byte(doc.Content))
	doc.ContentHash = hex.EncodeToString(hash[:])

	// Estimate token count if not provided
	if doc.TokenCount == 0 {
		tokenEstimator := tokens.NewTokenEstimator("gpt-4") // Default model
		doc.TokenCount = tokenEstimator.EstimateTokens(doc.Content)
	}

	// Set timestamps
	now := time.Now()
	doc.CreatedAt = now
	doc.UpdatedAt = now

	tx, err := s.db.BeginTx(ctx, nil)
	if err != nil {
		return fmt.Errorf("failed to begin transaction: %w", err)
	}
	defer tx.Rollback()

	// Insert document
	_, err = tx.ExecContext(ctx, `
		INSERT OR REPLACE INTO documents 
		(id, content, content_hash, path, lang, mtime, token_count, model_id, 
		 quantum_score, entanglement_map, coherence_history, created_at, updated_at)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,
		doc.ID, doc.Content, doc.ContentHash, doc.Path, doc.Language,
		doc.ModifiedTime, doc.TokenCount, doc.ModelID, doc.QuantumScore,
		doc.Entanglement, doc.Coherence, doc.CreatedAt, doc.UpdatedAt)
	if err != nil {
		return fmt.Errorf("failed to insert document: %w", err)
	}

	// Insert into FTS
	_, err = tx.ExecContext(ctx, `
		INSERT OR REPLACE INTO documents_fts(rowid, content) 
		SELECT rowid, content FROM documents WHERE id = ?`, doc.ID)
	if err != nil {
		return fmt.Errorf("failed to insert into FTS: %w", err)
	}

	return tx.Commit()
}

// InsertDocument inserts a new document (wrapper around AddDocument for interface compliance)
func (s *Storage) InsertDocument(doc types.Document) error {
	return s.AddDocument(context.Background(), &doc)
}

// UpdateDocument updates an existing document (wrapper around AddDocument for interface compliance)
func (s *Storage) UpdateDocument(doc types.Document) error {
	return s.AddDocument(context.Background(), &doc)
}

// SearchDocuments performs FTS search with LIKE fallback
func (s *Storage) SearchDocuments(ctx context.Context, query string, limit int) ([]types.Document, error) {
	// First try FTS search
	docs, err := s.searchFTS(ctx, query, limit)
	if err != nil || len(docs) == 0 {
		// Fallback to LIKE search if FTS fails or returns no results
		return s.searchLike(ctx, query, limit)
	}
	return docs, nil
}

// searchFTS performs FTS5 search
func (s *Storage) searchFTS(ctx context.Context, query string, limit int) ([]types.Document, error) {
	rows, err := s.db.QueryContext(ctx, `
		SELECT d.id, d.content, d.content_hash, d.path, d.lang, d.mtime,
		       d.token_count, d.model_id, d.quantum_score, d.entanglement_map,
		       d.coherence_history, d.created_at, d.updated_at
		FROM documents_fts fts
		JOIN documents d ON d.rowid = fts.rowid
		WHERE documents_fts MATCH ?
		ORDER BY rank
		LIMIT ?`, query, limit)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	return s.scanDocuments(rows)
}

// searchLike performs LIKE search as fallback
func (s *Storage) searchLike(ctx context.Context, query string, limit int) ([]types.Document, error) {
	likeQuery := "%" + strings.ReplaceAll(strings.ToLower(query), " ", "%") + "%"
	rows, err := s.db.QueryContext(ctx, `
		SELECT id, content, content_hash, path, lang, mtime,
		       token_count, model_id, quantum_score, entanglement_map,
		       coherence_history, created_at, updated_at
		FROM documents 
		WHERE LOWER(content) LIKE ?
		ORDER BY LENGTH(content)
		LIMIT ?`, likeQuery, limit)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	return s.scanDocuments(rows)
}

// scanDocuments scans rows into Document structs
func (s *Storage) scanDocuments(rows *sql.Rows) ([]types.Document, error) {
	var docs []types.Document
	for rows.Next() {
		var doc types.Document
		err := rows.Scan(
			&doc.ID, &doc.Content, &doc.ContentHash, &doc.Path, &doc.Language,
			&doc.ModifiedTime, &doc.TokenCount, &doc.ModelID, &doc.QuantumScore,
			&doc.Entanglement, &doc.Coherence, &doc.CreatedAt, &doc.UpdatedAt)
		if err != nil {
			return nil, err
		}
		docs = append(docs, doc)
	}
	return docs, rows.Err()
}

// GetDocument retrieves a document by ID
func (s *Storage) GetDocument(ctx context.Context, id string) (*types.Document, error) {
	var doc types.Document
	err := s.db.QueryRowContext(ctx, `
		SELECT id, content, content_hash, path, lang, mtime,
		       token_count, model_id, quantum_score, entanglement_map,
		       coherence_history, created_at, updated_at
		FROM documents WHERE id = ?`, id).Scan(
		&doc.ID, &doc.Content, &doc.ContentHash, &doc.Path, &doc.Language,
		&doc.ModifiedTime, &doc.TokenCount, &doc.ModelID, &doc.QuantumScore,
		&doc.Entanglement, &doc.Coherence, &doc.CreatedAt, &doc.UpdatedAt)
	if err != nil {
		return nil, err
	}
	return &doc, nil
}

// GetDocumentByPath retrieves a document by its file path
func (s *Storage) GetDocumentByPath(ctx context.Context, path string) (*types.Document, error) {
	var doc types.Document
	err := s.db.QueryRowContext(ctx, `
		SELECT id, content, content_hash, path, lang, mtime,
		       token_count, model_id, quantum_score, entanglement_map,
		       coherence_history, created_at, updated_at
		FROM documents WHERE path = ? LIMIT 1`, path).Scan(
		&doc.ID, &doc.Content, &doc.ContentHash, &doc.Path, &doc.Language,
		&doc.ModifiedTime, &doc.TokenCount, &doc.ModelID, &doc.QuantumScore,
		&doc.Entanglement, &doc.Coherence, &doc.CreatedAt, &doc.UpdatedAt)
	if err != nil {
		return nil, err
	}
	return &doc, nil
}

// DeleteDocument removes a document
func (s *Storage) DeleteDocument(ctx context.Context, id string) error {
	if id == "" {
		return fmt.Errorf("document ID cannot be empty")
	}
	
	tx, err := s.db.BeginTx(ctx, nil)
	if err != nil {
		return err
	}
	defer tx.Rollback()

	// Delete from documents_fts first (due to foreign key)
	_, err = tx.ExecContext(ctx, "DELETE FROM documents_fts WHERE rowid = (SELECT rowid FROM documents WHERE id = ?)", id)
	if err != nil {
		return err
	}

	// Delete from documents
	_, err = tx.ExecContext(ctx, "DELETE FROM documents WHERE id = ?", id)
	if err != nil {
		return err
	}

	return tx.Commit()
}

// GetWorkspaceWeights retrieves workspace weights
func (s *Storage) GetWorkspaceWeights(ctx context.Context, workspacePath string) (*types.WorkspaceWeights, error) {
	var weights types.WorkspaceWeights
	err := s.db.QueryRowContext(ctx, `
		SELECT workspace_path, relevance_weight, recency_weight, diversity_weight,
		       entanglement_weight, redundancy_penalty, normalization_stats,
		       update_count, last_updated
		FROM workspace_weights WHERE workspace_path = ?`, workspacePath).Scan(
		&weights.WorkspacePath, &weights.RelevanceWeight, &weights.RecencyWeight,
		&weights.DiversityWeight, &weights.EntanglementWeight, &weights.RedundancyPenalty,
		&weights.NormalizationStats, &weights.UpdateCount, &weights.LastUpdated)
	if err != nil {
		return nil, err
	}
	return &weights, nil
}

// SaveWorkspaceWeights saves workspace weights (interface-compatible version)
func (s *Storage) SaveWorkspaceWeights(workspacePath string, weights types.FeatureWeights) error {
	ctx := context.Background()
	
	// Convert FeatureWeights to WorkspaceWeights format for storage
	workspaceWeights := &types.WorkspaceWeights{
		WorkspacePath:      workspacePath,
		RelevanceWeight:    weights.Relevance,
		RecencyWeight:      weights.Recency,
		EntanglementWeight: weights.Entanglement,
		DiversityWeight:    weights.Specificity, // Map Specificity to DiversityWeight
		RedundancyPenalty:  weights.Uncertainty, // Map Uncertainty to RedundancyPenalty
		UpdateCount:        1,
		LastUpdated:        time.Now().Format(time.RFC3339),
		NormalizationStats: "", // Default empty
	}
	
	return s.saveWorkspaceWeightsInternal(ctx, workspaceWeights)
}

// saveWorkspaceWeightsInternal saves workspace weights (internal implementation)
func (s *Storage) saveWorkspaceWeightsInternal(ctx context.Context, weights *types.WorkspaceWeights) error {
	_, err := s.db.ExecContext(ctx, `
		INSERT OR REPLACE INTO workspace_weights 
		(workspace_path, relevance_weight, recency_weight, diversity_weight,
		 entanglement_weight, redundancy_penalty, normalization_stats,
		 update_count, last_updated)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)`,
		weights.WorkspacePath, weights.RelevanceWeight, weights.RecencyWeight,
		weights.DiversityWeight, weights.EntanglementWeight, weights.RedundancyPenalty,
		weights.NormalizationStats, weights.UpdateCount, weights.LastUpdated)
	return err
}

// SaveQueryCache saves a query result to cache
func (s *Storage) SaveQueryCache(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion string,
	result *types.QueryResult, expiresAt time.Time) error {
	
	resultJSON, err := json.Marshal(result.Documents)
	if err != nil {
		return err
	}
	
	metricsJSON, err := json.Marshal(result.optimizationMetrics)
	if err != nil {
		return err
	}

	_, err = s.db.ExecContext(ctx, `
		INSERT OR REPLACE INTO query_cache 
		(query_hash, corpus_hash, model_id, tokenizer_version, result_context,
		 quantum_metrics, document_scores, coherence_score, optimization_gap,
		 solve_time_ms, fallback_used, expires_at)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,
		queryHash, corpusHash, modelID, tokenizerVersion, string(resultJSON),
		string(metricsJSON), "", result.CoherenceScore, 0.0, // OptimalityGap removed
		result.optimizationMetrics.SolveTimeMs, result.optimizationMetrics.FallbackReason != "", expiresAt)
	return err
}

// GetQueryCache retrieves a cached query result
func (s *Storage) GetQueryCache(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion string) (*types.QueryResult, error) {
	var resultJSON, metricsJSON string
	var result types.QueryResult
	var tempGap float64 // Unused - OptimalityGap field removed
	
	err := s.db.QueryRowContext(ctx, `
		SELECT result_context, quantum_metrics, coherence_score, 
		       optimization_gap, solve_time_ms, fallback_used
		FROM query_cache 
		WHERE query_hash = ? AND corpus_hash = ? AND model_id = ? 
		      AND tokenizer_version = ? AND expires_at > CURRENT_TIMESTAMP`,
		queryHash, corpusHash, modelID, tokenizerVersion).Scan(
		&resultJSON, &metricsJSON, &result.CoherenceScore,
		&tempGap, &result.optimizationMetrics.SolveTimeMs, // OptimalityGap removed
		&result.optimizationMetrics.FallbackReason)
	if err != nil {
		return nil, err
	}

	if err := json.Unmarshal([]byte(resultJSON), &result.Documents); err != nil {
		return nil, err
	}
	
	if err := json.Unmarshal([]byte(metricsJSON), &result.optimizationMetrics); err != nil {
		return nil, err
	}

	result.CacheHit = true
	
	// Track cache hit
	s.cacheHits++
	
	return &result, nil
}

// GetCorpusHash computes a hash of the current document corpus
func (s *Storage) GetCorpusHash(ctx context.Context) (string, error) {
	var hash string
	err := s.db.QueryRowContext(ctx, `
		SELECT hex(sha256_agg(content_hash ORDER BY id)) 
		FROM (SELECT id, content_hash FROM documents ORDER BY id)`).Scan(&hash)
	if err != nil {
		// Fallback calculation if sha256_agg is not available
		rows, err := s.db.QueryContext(ctx, "SELECT content_hash FROM documents ORDER BY id")
		if err != nil {
			return "", err
		}
		defer rows.Close()

		h := sha256.New()
		for rows.Next() {
			var contentHash string
			if err := rows.Scan(&contentHash); err != nil {
				return "", err
			}
			h.Write([]byte(contentHash))
		}
		hash = hex.EncodeToString(h.Sum(nil))
	}
	return hash, nil
}

// applyMigrations applies database migrations for schema changes
func (s *Storage) applyMigrations() error {
	// Check if cache_key column exists in query_cache table
	rows, err := s.db.Query("PRAGMA table_info(query_cache)")
	if err != nil {
		return fmt.Errorf("failed to check table info: %w", err)
	}
	defer rows.Close()

	hasCacheKey := false
	for rows.Next() {
		var cid int
		var name, dataType string
		var notNull, pk int
		var defaultValue sql.NullString
		if err := rows.Scan(&cid, &name, &dataType, &notNull, &defaultValue, &pk); err != nil {
			return fmt.Errorf("failed to scan table info: %w", err)
		}
		if name == "cache_key" {
			hasCacheKey = true
			break
		}
	}

	// Add cache_key column if it doesn't exist
	if !hasCacheKey {
		_, err := s.db.Exec("ALTER TABLE query_cache ADD COLUMN cache_key TEXT")
		if err != nil {
			return fmt.Errorf("failed to add cache_key column: %w", err)
		}
		
		// Add index for cache_key
		_, err = s.db.Exec("CREATE INDEX IF NOT EXISTS idx_query_cache_key ON query_cache(cache_key)")
		if err != nil {
			return fmt.Errorf("failed to create cache_key index: %w", err)
		}
	}

	return nil
}

// GetCachedResultByKey retrieves cached result by cache key
func (s *Storage) GetCachedResultByKey(ctx context.Context, cacheKey string) (*types.QueryResult, error) {
	query := `
		SELECT result_context, quantum_metrics, document_scores, coherence_score, 
		       solve_time_ms, fallback_used, created_at
		FROM query_cache 
		WHERE cache_key = ? AND expires_at > ?
	`
	
	row := s.db.QueryRowContext(ctx, query, cacheKey, time.Now())
	
	var resultContext, quantumMetrics, documentScores string
	var coherenceScore float64
	var solveTimeMs sql.NullFloat64
	var fallbackUsed bool
	var createdAt time.Time
	
	err := row.Scan(&resultContext, &quantumMetrics, &documentScores, 
		&coherenceScore, &solveTimeMs, &fallbackUsed, &createdAt)
	if err != nil {
		if err == sql.ErrNoRows {
			// Track cache miss
			s.cacheMisses++
			return nil, nil // Cache miss
		}
		return nil, fmt.Errorf("failed to scan cached result: %w", err)
	}
	
	// Deserialize the cached result
	var result types.QueryResult
	if err := json.Unmarshal([]byte(resultContext), &result); err != nil {
		return nil, fmt.Errorf("failed to unmarshal cached result: %w", err)
	}
	
	return &result, nil
}

// SaveQueryCacheWithKey saves a query result to cache with cache key
func (s *Storage) SaveQueryCacheWithKey(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion, cacheKey string,
	result *types.QueryResult, expiresAt time.Time) error {
	
	resultJSON, err := json.Marshal(result)
	if err != nil {
		return err
	}
	
	metricsJSON, err := json.Marshal(result.optimizationMetrics)
	if err != nil {
		return err
	}

	// Check if cache_key column exists
	rows, err := s.db.Query("PRAGMA table_info(query_cache)")
	if err != nil {
		return fmt.Errorf("failed to check table info: %w", err)
	}
	defer rows.Close()

	hasCacheKey := false
	for rows.Next() {
		var cid int
		var name, dataType string
		var notNull, pk int
		var defaultValue sql.NullString
		if err := rows.Scan(&cid, &name, &dataType, &notNull, &defaultValue, &pk); err != nil {
			return fmt.Errorf("failed to scan table info: %w", err)
		}
		if name == "cache_key" {
			hasCacheKey = true
			break
		}
	}

	if hasCacheKey {
		_, err = s.db.ExecContext(ctx, `
			INSERT OR REPLACE INTO query_cache 
			(query_hash, corpus_hash, model_id, tokenizer_version, result_context,
			 quantum_metrics, document_scores, coherence_score, optimization_gap,
			 solve_time_ms, fallback_used, expires_at, cache_key)
			VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,
			queryHash, corpusHash, modelID, tokenizerVersion, string(resultJSON),
			string(metricsJSON), "", result.CoherenceScore, 0.0, // OptimalityGap removed
			result.optimizationMetrics.SolveTimeMs, result.optimizationMetrics.FallbackReason != "", expiresAt, cacheKey)
	} else {
		// Fallback to old method without cache_key
		_, err = s.db.ExecContext(ctx, `
			INSERT OR REPLACE INTO query_cache 
			(query_hash, corpus_hash, model_id, tokenizer_version, result_context,
			 quantum_metrics, document_scores, coherence_score, optimization_gap,
			 solve_time_ms, fallback_used, expires_at)
			VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,
			queryHash, corpusHash, modelID, tokenizerVersion, string(resultJSON),
			string(metricsJSON), "", result.CoherenceScore, 0.0, // OptimalityGap removed
			result.optimizationMetrics.SolveTimeMs, result.optimizationMetrics.FallbackReason != "", expiresAt)
	}
	return err
}

// InvalidateCache removes all cached query results
func (s *Storage) InvalidateCache(ctx context.Context) error {
	_, err := s.db.ExecContext(ctx, "DELETE FROM query_cache")
	if err != nil {
		return fmt.Errorf("failed to invalidate cache: %w", err)
	}
	
	// Reset cache statistics
	s.cacheHits = 0
	s.cacheMisses = 0
	
	return nil
}
