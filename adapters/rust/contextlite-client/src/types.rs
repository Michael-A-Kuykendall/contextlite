//! Core types for the ContextLite Rust client.
//!
//! This module defines all data structures used for communication with the ContextLite server,
//! following the same patterns as the Go, Python, and Node.js clients for consistency.

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// A document in the ContextLite system
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Document {
    /// Unique document identifier (auto-generated if not provided)
    pub id: Option<String>,
    
    /// File path or logical path of the document
    pub path: String,
    
    /// Content of the document
    pub content: String,
    
    /// Optional metadata as key-value pairs
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<HashMap<String, String>>,
    
    /// Creation timestamp
    #[serde(skip_serializing_if = "Option::is_none")]
    pub created_at: Option<DateTime<Utc>>,
    
    /// Last update timestamp
    #[serde(skip_serializing_if = "Option::is_none")]
    pub updated_at: Option<DateTime<Utc>>,
}

impl Document {
    /// Create a new document with required fields
    pub fn new(path: impl Into<String>, content: impl Into<String>) -> Self {
        Self {
            id: None,
            path: path.into(),
            content: content.into(),
            metadata: None,
            created_at: None,
            updated_at: None,
        }
    }
    
    /// Set the document ID
    pub fn with_id(mut self, id: impl Into<String>) -> Self {
        self.id = Some(id.into());
        self
    }
    
    /// Set metadata for the document
    pub fn with_metadata(mut self, metadata: HashMap<String, String>) -> Self {
        self.metadata = Some(metadata);
        self
    }
}

/// Search query parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchQuery {
    /// The search query string
    pub q: String,
    
    /// Maximum number of results to return
    #[serde(skip_serializing_if = "Option::is_none")]
    pub limit: Option<usize>,
    
    /// Number of results to skip (for pagination)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub offset: Option<usize>,
    
    /// Additional filters as arbitrary JSON
    #[serde(skip_serializing_if = "Option::is_none")]
    pub filters: Option<serde_json::Value>,
}

impl SearchQuery {
    /// Create a new search query
    pub fn new(query: impl Into<String>) -> Self {
        Self {
            q: query.into(),
            limit: None,
            offset: None,
            filters: None,
        }
    }
    
    /// Set the result limit
    pub fn with_limit(mut self, limit: usize) -> Self {
        self.limit = Some(limit);
        self
    }
    
    /// Set the result offset for pagination
    pub fn with_offset(mut self, offset: usize) -> Self {
        self.offset = Some(offset);
        self
    }
    
    /// Add filters to the query
    pub fn with_filters(mut self, filters: serde_json::Value) -> Self {
        self.filters = Some(filters);
        self
    }
}

/// Reference to a document in search results or context
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocumentReference {
    /// Document ID
    pub id: String,
    
    /// Document path
    pub path: String,
    
    /// Document content (may be truncated)
    pub content: String,
    
    /// Relevance score for this document
    #[serde(skip_serializing_if = "Option::is_none")]
    pub score: Option<f64>,
    
    /// Additional metadata
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<HashMap<String, String>>,
}

/// Response from document search
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResponse {
    /// Search query that was executed
    pub query: String,
    
    /// Documents matching the search
    pub documents: Vec<DocumentReference>,
    
    /// Total number of results found
    pub total: usize,
    
    /// Search execution time in milliseconds
    #[serde(skip_serializing_if = "Option::is_none")]
    pub took_ms: Option<u64>,
}

/// Request for context assembly
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContextRequest {
    /// Query for context assembly
    pub q: String,
    
    /// Token budget for the assembled context
    #[serde(skip_serializing_if = "Option::is_none")]
    pub budget: Option<usize>,
    
    /// Maximum number of documents to include
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_results: Option<usize>,
    
    /// Whether to include document metadata
    #[serde(skip_serializing_if = "Option::is_none")]
    pub include_metadata: Option<bool>,
    
    /// SMT optimization parameters
    #[serde(skip_serializing_if = "Option::is_none")]
    pub smt_options: Option<serde_json::Value>,
}

impl ContextRequest {
    /// Create a new context request
    pub fn new(query: impl Into<String>) -> Self {
        Self {
            q: query.into(),
            budget: None,
            max_results: None,
            include_metadata: None,
            smt_options: None,
        }
    }
    
    /// Set the token budget
    pub fn with_budget(mut self, budget: usize) -> Self {
        self.budget = Some(budget);
        self
    }
    
    /// Set the maximum number of results
    pub fn with_max_results(mut self, max_results: usize) -> Self {
        self.max_results = Some(max_results);
        self
    }
    
    /// Include document metadata in the response
    pub fn with_metadata(mut self, include: bool) -> Self {
        self.include_metadata = Some(include);
        self
    }
}

/// Assembled context response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContextResponse {
    /// The search query used
    pub query: String,
    
    /// Documents that were included in the context
    pub documents: Option<Vec<DocumentReference>>,
    
    /// Total number of documents included
    pub total_documents: usize,
    
    /// Total token count
    pub total_tokens: usize,
    
    /// Coherence score of the assembled context
    pub coherence_score: f64,
    
    /// SMT solver metrics
    #[serde(skip_serializing_if = "Option::is_none")]
    pub smt_metrics: Option<serde_json::Value>,
    
    /// Timing information
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timings: Option<serde_json::Value>,
    
    /// Whether this was a cache hit
    pub cache_hit: bool,
    
    /// Cache key fingerprint
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cache_key_fingerprint: Option<String>,
}

/// System health status
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompleteHealthStatus {
    /// Overall system status
    pub status: String,
    
    /// System version
    pub version: String,
    
    /// Timestamp of the status check
    pub timestamp: i64,
    
    /// Database information
    pub database: DatabaseStats,
    
    /// SMT solver information
    pub smt: SmtInfo,
    
    /// Available features
    pub features: Features,
}

/// Database statistics and status
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseStats {
    /// Number of documents currently indexed
    pub documents_indexed: String,
    
    /// Number of active cache entries
    pub cache_entries: String,
    
    /// Whether FTS (Full Text Search) is enabled
    pub fts_enabled: bool,
    
    /// Last optimization timestamp
    pub last_optimized: i64,
}

/// SMT solver information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SmtInfo {
    /// Whether SMT optimization is enabled
    pub enabled: bool,
    
    /// SMT solver name
    pub solver: String,
    
    /// SMT solver version
    pub version: String,
    
    /// SMT policy description
    pub policy: String,
}

/// Available system features
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Features {
    /// Whether caching is enabled
    pub cache_enabled: bool,
    
    /// Whether FTS search is available
    pub fts_search: bool,
    
    /// Whether quantum scoring is enabled
    pub quantum_scoring: bool,
    
    /// Whether SMT optimization is available
    pub smt_optimization: bool,
}

/// Storage information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageInfo {
    /// Database file path
    pub database_path: String,
    
    /// Database size in bytes
    pub size_bytes: u64,
    
    /// Number of documents
    pub document_count: usize,
    
    /// Last vacuum timestamp
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_vacuum: Option<DateTime<Utc>>,
}

/// Client configuration
#[derive(Debug, Clone)]
pub struct ClientConfig {
    /// Base URL of the ContextLite server
    pub base_url: String,
    
    /// Authentication token
    pub auth_token: Option<String>,
    
    /// Request timeout in seconds
    pub timeout_seconds: u64,
    
    /// Maximum number of retries for failed requests
    pub max_retries: usize,
    
    /// User agent string
    pub user_agent: String,
}

impl ClientConfig {
    /// Create a new client configuration
    pub fn new(base_url: impl Into<String>) -> Self {
        Self {
            base_url: base_url.into(),
            auth_token: None,
            timeout_seconds: 30,
            max_retries: 3,
            user_agent: format!("contextlite-rust-client/{}", env!("CARGO_PKG_VERSION")),
        }
    }
    
    /// Set the authentication token
    pub fn with_auth_token(mut self, token: impl Into<String>) -> Self {
        self.auth_token = Some(token.into());
        self
    }
    
    /// Set the request timeout
    pub fn with_timeout(mut self, seconds: u64) -> Self {
        self.timeout_seconds = seconds;
        self
    }
    
    /// Set the maximum number of retries
    pub fn with_max_retries(mut self, retries: usize) -> Self {
        self.max_retries = retries;
        self
    }
    
    /// Set a custom user agent
    pub fn with_user_agent(mut self, user_agent: impl Into<String>) -> Self {
        self.user_agent = user_agent.into();
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_document_creation() {
        let mut metadata = HashMap::new();
        metadata.insert("lang".to_string(), "rust".to_string());
        
        let doc = Document::new("test.rs", "fn main() {}")
            .with_id("test-id")
            .with_metadata(metadata);
        
        assert_eq!(doc.path, "test.rs");
        assert_eq!(doc.content, "fn main() {}");
        assert_eq!(doc.id, Some("test-id".to_string()));
        assert!(doc.metadata.is_some());
    }
    
    #[test]
    fn test_search_query_builder() {
        let query = SearchQuery::new("rust async")
            .with_limit(10)
            .with_offset(5);
        
        assert_eq!(query.q, "rust async");
        assert_eq!(query.limit, Some(10));
        assert_eq!(query.offset, Some(5));
    }
    
    #[test]
    fn test_context_request_builder() {
        let request = ContextRequest::new("example query")
            .with_budget(1000)
            .with_max_results(5)
            .with_metadata(true);
        
        assert_eq!(request.q, "example query");
        assert_eq!(request.budget, Some(1000));
        assert_eq!(request.max_results, Some(5));
        assert_eq!(request.include_metadata, Some(true));
    }
    
    #[test]
    fn test_client_config_builder() {
        let config = ClientConfig::new("http://localhost:8080")
            .with_auth_token("test-token")
            .with_timeout(60)
            .with_max_retries(5);
        
        assert_eq!(config.base_url, "http://localhost:8080");
        assert_eq!(config.auth_token, Some("test-token".to_string()));
        assert_eq!(config.timeout_seconds, 60);
        assert_eq!(config.max_retries, 5);
    }
}
