//! # ContextLite Rust Client
//! 
//! A high-performance, async Rust client for the ContextLite context engine.
//! 
//! ## Features
//! 
//! - **Async/Await Support**: Built on Tokio for high-performance async operations
//! - **Type Safety**: Comprehensive type definitions with builder patterns
//! - **Error Handling**: Rich error types with proper error chaining
//! - **Connection Pooling**: HTTP connection pooling for optimal performance
//! - **Authentication**: Bearer token authentication support
//! - **Validation**: Client-side validation for better error messages
//! - **Flexible API**: Builder patterns for easy configuration
//! 
//! ## Quick Start
//! 
//! ```rust
//! use contextlite_client::{ContextLiteClient, ClientConfig, Document, SearchQuery};
//! 
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // Create a client with default configuration
//!     let client = ContextLiteClient::new()?;
//!     
//!     // Or with custom configuration
//!     let config = ClientConfig::new("http://localhost:8083")
//!         .with_auth_token("your-token")
//!         .with_timeout(60);
//!     let client = ContextLiteClient::with_config(config)?;
//!     
//!     // Add a document
//!     let document = Document::new("example.txt", "This is an example document");
//!     let doc_id = client.add_document(&document).await?;
//!     
//!     // Search for documents
//!     let query = SearchQuery::new("example").with_limit(10);
//!     let results = client.search(&query).await?;
//!     
//!     println!("Found {} documents", results.documents.len());
//!     
//!     Ok(())
//! }
//! ```
//! 
//! ## Error Handling
//! 
//! The client provides comprehensive error handling with detailed error messages:
//! 
//! ```rust
//! use contextlite_client::{ContextLiteClient, ContextLiteError};
//! 
//! #[tokio::main]
//! async fn main() {
//!     let client = ContextLiteClient::new().unwrap();
//!     
//!     match client.health().await {
//!         Ok(health) => println!("Server is healthy: {}", health.status),
//!         Err(ContextLiteError::AuthError { message }) => {
//!             eprintln!("Authentication failed: {}", message);
//!         },
//!         Err(ContextLiteError::ServerError { status, message }) => {
//!             eprintln!("Server error {}: {}", status, message);
//!         },
//!         Err(err) => eprintln!("Error: {}", err),
//!     }
//! }
//! ```

#![deny(missing_docs)]
#![warn(clippy::all)]

pub mod client;
pub mod error;
pub mod types;

// Re-export main types for convenience
pub use client::ContextLiteClient;
pub use error::{ContextLiteError, Result};
pub use types::{
    CompleteHealthStatus, SmtInfo, DatabaseStats, Features,
    ClientConfig, ContextRequest, ContextResponse, Document, DocumentReference,
    SearchQuery, SearchResponse, StorageInfo,
};

/// Convenience alias for the main client type
pub type Client = ContextLiteClient;

#[cfg(test)]
mod integration_tests {
    use super::*;
    
    #[tokio::test]
    async fn test_client_creation_and_basic_operations() {
        // This test requires a running ContextLite server
        // Skip if server is not available
        let client = match ContextLiteClient::new() {
            Ok(client) => client,
            Err(_) => return, // Skip test if client creation fails
        };
        
        // Try to check health - this will fail if server is not running
        if client.health().await.is_err() {
            return; // Skip test if server is not available
        }
        
        // Test document operations
        let document = Document::new("test.txt", "This is a test document")
            .with_metadata(serde_json::json!({"test": true}));
        
        let doc_id = client.add_document(&document).await.unwrap();
        assert!(!doc_id.is_empty());
        
        // Test search
        let query = SearchQuery::new("test").with_limit(5);
        let results = client.search(&query).await.unwrap();
        assert!(!results.documents.is_empty());
        
        // Test context assembly
        let context_request = ContextRequest::new("test document")
            .with_budget(1000)
            .with_max_results(3);
        let context = client.assemble_context(&context_request).await.unwrap();
        assert!(!context.context.is_empty());
        
        // Clean up
        let _ = client.delete_document(&doc_id).await;
    }
}
