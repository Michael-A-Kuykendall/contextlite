package storage

import (
	"context"
	"crypto/sha256"
	"database/sql"
	"embed"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"strings"
	"time"

	"contextlite/pkg/types"

	_ "modernc.org/sqlite"
)

//go:embed schema.sql
var schemaFS embed.FS

// Storage provides SQLite storage operations
type Storage struct {
	db *sql.DB
}

// New creates a new Storage instance
func New(dbPath string) (*Storage, error) {
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
			return nil, fmt.Errorf("failed to apply pragma %s: %w", pragma, err)
		}
	}

	storage := &Storage{db: db}

	// Initialize schema
	if err := storage.initSchema(); err != nil {
		return nil, fmt.Errorf("failed to initialize schema: %w", err)
	}

	return storage, nil
}

// Close closes the database connection
func (s *Storage) Close() error {
	return s.db.Close()
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

// SearchDocuments performs FTS search
func (s *Storage) SearchDocuments(ctx context.Context, query string, limit int) ([]types.Document, error) {
	// First try FTS search
	docs, err := s.searchFTS(ctx, query, limit)
	if err != nil {
		// Fallback to LIKE search
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
	likeQuery := "%" + strings.ReplaceAll(query, " ", "%") + "%"
	rows, err := s.db.QueryContext(ctx, `
		SELECT id, content, content_hash, path, lang, mtime,
		       token_count, model_id, quantum_score, entanglement_map,
		       coherence_history, created_at, updated_at
		FROM documents 
		WHERE content LIKE ?
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

// SaveWorkspaceWeights saves workspace weights
func (s *Storage) SaveWorkspaceWeights(ctx context.Context, weights *types.WorkspaceWeights) error {
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
		string(metricsJSON), "", result.CoherenceScore, result.optimizationMetrics.OptimalityGap,
		result.optimizationMetrics.SolveTimeMs, result.optimizationMetrics.FallbackReason != "", expiresAt)
	return err
}

// GetQueryCache retrieves a cached query result
func (s *Storage) GetQueryCache(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion string) (*types.QueryResult, error) {
	var resultJSON, metricsJSON string
	var result types.QueryResult
	
	err := s.db.QueryRowContext(ctx, `
		SELECT result_context, quantum_metrics, coherence_score, 
		       optimization_gap, solve_time_ms, fallback_used
		FROM query_cache 
		WHERE query_hash = ? AND corpus_hash = ? AND model_id = ? 
		      AND tokenizer_version = ? AND expires_at > CURRENT_TIMESTAMP`,
		queryHash, corpusHash, modelID, tokenizerVersion).Scan(
		&resultJSON, &metricsJSON, &result.CoherenceScore,
		&result.optimizationMetrics.OptimalityGap, &result.optimizationMetrics.SolveTimeMs,
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
