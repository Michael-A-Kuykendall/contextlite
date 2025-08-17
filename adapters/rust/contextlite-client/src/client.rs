//! ContextLite HTTP client implementation.
//!
//! This module provides a high-performance async HTTP client for ContextLite,
//! with connection pooling, retry logic, and comprehensive error handling.

use crate::error::{handle_response_error, ContextLiteError, Result};
use crate::types::{
    ClientConfig, ContextRequest, ContextResponse, Document, CompleteHealthStatus, SearchQuery,
    SearchResponse, StorageInfo,
};
use reqwest::{Client as HttpClient, RequestBuilder};
use serde_json::Value;
use std::time::Duration;
use tokio::time::timeout;
use url::Url;

/// The main ContextLite client
#[derive(Debug, Clone)]
pub struct ContextLiteClient {
    config: ClientConfig,
    http_client: HttpClient,
    base_url: Url,
}

impl ContextLiteClient {
    /// Create a new ContextLite client with default configuration
    pub fn new(base_url: impl Into<String>) -> Result<Self> {
        Self::with_config(ClientConfig::new(base_url))
    }
    
    /// Create a new ContextLite client with custom configuration
    pub fn with_config(config: ClientConfig) -> Result<Self> {
        // Validate base URL
        let base_url = Url::parse(&config.base_url)
            .map_err(|e| ContextLiteError::config(format!("Invalid base URL: {}", e)))?;
        
        // Build HTTP client with connection pooling and timeouts
        let http_client = HttpClient::builder()
            .timeout(Duration::from_secs(config.timeout_seconds))
            .pool_idle_timeout(Duration::from_secs(30))
            .pool_max_idle_per_host(10) // Default connection pool size
            .user_agent(&config.user_agent)
            .build()
            .map_err(|e| ContextLiteError::config(format!("Failed to create HTTP client: {}", e)))?;
        
        Ok(Self {
            config,
            http_client,
            base_url,
        })
    }
    
    /// Build a request with common headers and authentication
    fn build_request(&self, method: reqwest::Method, path: &str) -> Result<RequestBuilder> {
        let url = self.base_url.join(path)
            .map_err(|e| ContextLiteError::config(format!("Invalid URL path '{}': {}", path, e)))?;
        
        let mut request = self.http_client.request(method, url);
        
        // Add authentication header if configured
        if let Some(ref token) = self.config.auth_token {
            request = request.header("Authorization", format!("Bearer {}", token));
        }
        
        // Add common headers
        request = request
            .header("Content-Type", "application/json")
            .header("Accept", "application/json")
            .header("User-Agent", format!("contextlite-rust/{}", env!("CARGO_PKG_VERSION")));
        
        Ok(request)
    }
    
    /// Execute a request with timeout and error handling
    async fn execute_request(&self, request: RequestBuilder) -> Result<reqwest::Response> {
        let response = timeout(
            Duration::from_secs(self.config.timeout_seconds),
            request.send(),
        )
        .await
        .map_err(|_| ContextLiteError::timeout(self.config.timeout_seconds))?
        .map_err(ContextLiteError::HttpError)?;
        
        handle_response_error(response).await
    }
    
    /// Check server health status
    pub async fn health(&self) -> Result<CompleteHealthStatus> {
        let request = self.build_request(reqwest::Method::GET, "/health")?;
        let response = self.execute_request(request).await?;
        
        let health: CompleteHealthStatus = response.json().await?;
        Ok(health)
    }
    
    /// Get storage information
    pub async fn storage_info(&self) -> Result<StorageInfo> {
        let request = self.build_request(reqwest::Method::GET, "/storage/info")?;
        let response = self.execute_request(request).await?;
        
        let info: StorageInfo = response.json().await?;
        Ok(info)
    }
    
    /// Add a document to the index
    pub async fn add_document(&self, document: &Document) -> Result<String> {
        // Validate document
        if document.path.is_empty() {
            return Err(ContextLiteError::validation("Document path cannot be empty"));
        }
        
        if document.content.is_empty() {
            return Err(ContextLiteError::validation("Document content cannot be empty"));
        }
        
        let request = self.build_request(reqwest::Method::POST, "/api/v1/documents")?
            .json(document);
        
        let response = self.execute_request(request).await?;
        
        // Parse response to get document ID
        let result: Value = response.json().await?;
        
        result
            .get("id")
            .and_then(|id| id.as_str())
            .map(|id| id.to_string())
            .ok_or_else(|| ContextLiteError::response("Missing document ID in response"))
    }
    
    /// Add multiple documents in batch
    pub async fn add_documents(&self, documents: &[Document]) -> Result<Vec<String>> {
        if documents.is_empty() {
            return Ok(Vec::new());
        }
        
        // Validate all documents
        for (i, doc) in documents.iter().enumerate() {
            if doc.path.is_empty() {
                return Err(ContextLiteError::validation(
                    format!("Document at index {} has empty path", i)
                ));
            }
            if doc.content.is_empty() {
                return Err(ContextLiteError::validation(
                    format!("Document at index {} has empty content", i)
                ));
            }
        }
        
        let request = self.build_request(reqwest::Method::POST, "/api/v1/documents/bulk")?
            .json(documents);
        
        let response = self.execute_request(request).await?;
        
        // Parse response to get document IDs
        let result: Value = response.json().await?;
        
        result
            .get("ids")
            .and_then(|ids| ids.as_array())
            .ok_or_else(|| ContextLiteError::response("Missing document IDs in response"))?
            .iter()
            .map(|id| {
                id.as_str()
                    .map(|s| s.to_string())
                    .ok_or_else(|| ContextLiteError::response("Invalid document ID format"))
            })
            .collect()
    }
    
    /// Get a document by ID
    pub async fn get_document(&self, id: &str) -> Result<Document> {
        if id.is_empty() {
            return Err(ContextLiteError::validation("Document ID cannot be empty"));
        }
        
        let path = format!("/documents/{}", urlencoding::encode(id));
        let request = self.build_request(reqwest::Method::GET, &path)?;
        
        let response = self.execute_request(request).await?;
        
        let document: Document = response.json().await?;
        Ok(document)
    }
    
    /// Update a document
    pub async fn update_document(&self, id: &str, document: &Document) -> Result<()> {
        if id.is_empty() {
            return Err(ContextLiteError::validation("Document ID cannot be empty"));
        }
        
        if document.path.is_empty() {
            return Err(ContextLiteError::validation("Document path cannot be empty"));
        }
        
        if document.content.is_empty() {
            return Err(ContextLiteError::validation("Document content cannot be empty"));
        }
        
        let path = format!("/documents/{}", urlencoding::encode(id));
        let request = self.build_request(reqwest::Method::PUT, &path)?
            .json(document);
        
        self.execute_request(request).await?;
        Ok(())
    }
    
    /// Delete a document by ID
    pub async fn delete_document(&self, id: &str) -> Result<()> {
        if id.is_empty() {
            return Err(ContextLiteError::validation("Document ID cannot be empty"));
        }
        
        let path = format!("/api/v1/documents/{}", urlencoding::encode(id));
        let request = self.build_request(reqwest::Method::DELETE, &path)?;
        
        self.execute_request(request).await?;
        Ok(())
    }
    
    /// Search for documents
    pub async fn search(&self, query: &SearchQuery) -> Result<SearchResponse> {
        if query.q.is_empty() {
            return Err(ContextLiteError::validation("Search query cannot be empty"));
        }
        
        let mut params = vec![("q", query.q.as_str())];
        let limit_str;
        let offset_str;
        
        if let Some(limit) = query.limit {
            limit_str = limit.to_string();
            params.push(("limit", &limit_str));
        }
        if let Some(offset) = query.offset {
            offset_str = offset.to_string();
            params.push(("offset", &offset_str));
        }
        
        let request = self.build_request(reqwest::Method::GET, "/api/v1/documents/search")?
            .query(&params);
        
        let response = self.execute_request(request).await?;
        
        let search_response: SearchResponse = response.json().await?;
        Ok(search_response)
    }
    
    /// Assemble context from documents
    pub async fn assemble_context(&self, request: &ContextRequest) -> Result<ContextResponse> {
        if request.q.is_empty() {
            return Err(ContextLiteError::validation("Context query cannot be empty"));
        }
        
        let http_request = self.build_request(reqwest::Method::POST, "/api/v1/context/assemble")?
            .json(request);
        
        let response = self.execute_request(http_request).await?;
        
        let context_response: ContextResponse = response.json().await?;
        Ok(context_response)
    }
    
    /// Clear all documents from the index
    pub async fn clear_documents(&self) -> Result<()> {
        let request = self.build_request(reqwest::Method::DELETE, "/documents")?;
        self.execute_request(request).await?;
        Ok(())
    }
    
    /// Get the current client configuration
    pub fn config(&self) -> &ClientConfig {
        &self.config
    }
    
    /// Check if the client is configured with authentication
    pub fn has_auth(&self) -> bool {
        self.config.auth_token.is_some()
    }
}

impl Default for ContextLiteClient {
    fn default() -> Self {
        Self::new("http://127.0.0.1:8082").expect("Failed to create default ContextLite client")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Document, SearchQuery, ContextRequest};
    
    #[test]
    fn test_client_creation() {
        let client = ContextLiteClient::new("http://127.0.0.1:8082");
        assert!(client.is_ok());
        
        let client = client.unwrap();
        assert_eq!(client.config().base_url, "http://127.0.0.1:8082");
        assert!(!client.has_auth());
    }
    
    #[test]
    fn test_client_with_config() {
        let config = ClientConfig::new("http://localhost:8083")
            .with_auth_token("test-token")
            .with_timeout(60);
        
        let client = ContextLiteClient::with_config(config);
        assert!(client.is_ok());
        
        let client = client.unwrap();
        assert_eq!(client.config().base_url, "http://localhost:8083");
        assert!(client.has_auth());
        assert_eq!(client.config().timeout_seconds, 60);
    }
    
    #[test]
    fn test_invalid_base_url() {
        let config = ClientConfig::new("invalid-url");
        let client = ContextLiteClient::with_config(config);
        assert!(client.is_err());
        assert!(matches!(client.unwrap_err(), ContextLiteError::ConfigError { .. }));
    }
    
    #[test]
    fn test_document_validation() {
        let client = ContextLiteClient::new("http://127.0.0.1:8082").unwrap();
        
        // Test empty path validation
        let doc = Document::new("", "content");
        let rt = tokio::runtime::Runtime::new().unwrap();
        let result = rt.block_on(client.add_document(&doc));
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ContextLiteError::ValidationError { .. }));
        
        // Test empty content validation
        let doc = Document::new("test.txt", "");
        let result = rt.block_on(client.add_document(&doc));
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ContextLiteError::ValidationError { .. }));
    }
    
    #[test]
    fn test_search_validation() {
        let client = ContextLiteClient::new("http://127.0.0.1:8082").unwrap();
        
        // Test empty query validation
        let query = SearchQuery::new("");
        let rt = tokio::runtime::Runtime::new().unwrap();
        let result = rt.block_on(client.search(&query));
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ContextLiteError::ValidationError { .. }));
    }
    
    #[test]
    fn test_context_validation() {
        let client = ContextLiteClient::new("http://127.0.0.1:8082").unwrap();
        
        // Test empty query validation
        let request = ContextRequest::new("");
        let rt = tokio::runtime::Runtime::new().unwrap();
        let result = rt.block_on(client.assemble_context(&request));
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ContextLiteError::ValidationError { .. }));
    }
}
