CREATE TABLE documents (
  id TEXT PRIMARY KEY,
  content TEXT NOT NULL,
  content_hash TEXT NOT NULL,
  path TEXT,
  lang TEXT,
  mtime BIGINT,
  token_count INTEGER,
  model_id TEXT,
  quantum_score REAL DEFAULT 0,
  entanglement_map TEXT,
  coherence_history TEXT,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE VIRTUAL TABLE documents_fts USING fts5(
  content,
  content=documents,
  content_rowid=rowid,
  tokenize='porter ascii'
);

CREATE TABLE query_cache (
  query_hash TEXT PRIMARY KEY,
  corpus_hash TEXT NOT NULL,
  model_id TEXT NOT NULL,
  tokenizer_version TEXT NOT NULL,
  result_context TEXT NOT NULL,
  quantum_metrics TEXT NOT NULL,
  document_scores TEXT NOT NULL,
  coherence_score REAL NOT NULL,
  optimization_gap REAL,
  solve_time_ms INTEGER,
  fallback_used BOOLEAN DEFAULT 0,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  expires_at TIMESTAMP NOT NULL,
  access_count INTEGER DEFAULT 1
);

CREATE TABLE workspace_weights (
  workspace_path TEXT PRIMARY KEY,
  relevance_weight REAL DEFAULT 0.4,
  recency_weight REAL DEFAULT 0.2,
  diversity_weight REAL DEFAULT 0.2,
  entanglement_weight REAL DEFAULT 0.2,
  redundancy_penalty REAL DEFAULT 0.3,
  normalization_stats TEXT,
  update_count INTEGER DEFAULT 0,
  last_updated TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE concepts (
  doc_id TEXT,
  term TEXT,
  tf INTEGER,
  df INTEGER,
  PRIMARY KEY(doc_id, term)
);

CREATE TABLE meta (
  key TEXT PRIMARY KEY,
  value TEXT NOT NULL,
  updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX idx_documents_token_count ON documents(token_count);
CREATE INDEX idx_documents_mtime ON documents(mtime);
CREATE INDEX idx_concepts_term ON concepts(term);
CREATE INDEX idx_query_cache_composite ON query_cache(corpus_hash, model_id, tokenizer_version);
