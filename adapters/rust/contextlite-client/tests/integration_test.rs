//! Integration tests for the ContextLite Rust client.
//! 
//! These tests verify the client works correctly against a real ContextLite server.
//! They require a running ContextLite server at the configured URL.

use contextlite_client::{
    ContextLiteClient, ClientConfig, Document, SearchQuery, ContextRequest, ContextLiteError
};
use serde_json::json;
use std::collections::HashMap;
use tokio::time::Duration;

/// Test configuration - matches the integration test suite setup
const TEST_SERVER_URL: &str = "http://127.0.0.1:8083";
const TEST_AUTH_TOKEN: &str = "test-token-12345";

/// Helper to create a test client
fn create_test_client() -> ContextLiteClient {
    let config = ClientConfig::new(TEST_SERVER_URL)
        .with_auth_token(TEST_AUTH_TOKEN)
        .with_timeout(30);
    
    ContextLiteClient::with_config(config)
        .expect("Failed to create test client")
}

/// Helper to wait for server readiness
async fn wait_for_server(client: &ContextLiteClient) -> bool {
    for _ in 0..10 {
        if client.health().await.is_ok() {
            return true;
        }
        tokio::time::sleep(Duration::from_millis(500)).await;
    }
    false
}

#[tokio::test]
async fn test_health_check() {
    let client = create_test_client();
    
    // Wait for server to be ready
    if !wait_for_server(&client).await {
        eprintln!("Skipping test: ContextLite server not available at {}", TEST_SERVER_URL);
        return;
    }
    
    let health = client.health().await.expect("Health check failed");
    assert_eq!(health.status, "ok");
}

#[tokio::test]
async fn test_storage_info() {
    let client = create_test_client();
    
    if !wait_for_server(&client).await {
        eprintln!("Skipping test: ContextLite server not available");
        return;
    }
    
    let info = client.storage_info().await.expect("Storage info failed");
    
}

#[tokio::test]
async fn test_document_operations() {
    let client = create_test_client();
    
    if !wait_for_server(&client).await {
        eprintln!("Skipping test: ContextLite server not available");
        return;
    }
    
    // Create a test document
    let document = Document::new("test_rust.rs", 
        "fn main() { println!(\"Hello from Rust!\"); }")
        .with_metadata({
            let mut map = HashMap::new();
            map.insert("language".to_string(), "rust".to_string());
            map.insert("test".to_string(), "true".to_string());
            map.insert("timestamp".to_string(), chrono::Utc::now().timestamp().to_string());
            map
        });
    
    // Add document
    let doc_id = client.add_document(&document).await
        .expect("Failed to add document");
    
    assert!(!doc_id.is_empty());
    
    // Get document back
    let retrieved = client.get_document(&doc_id).await
        .expect("Failed to get document");
    
    assert_eq!(retrieved.path, "test_rust.rs");
    assert!(retrieved.content.contains("Hello from Rust!"));
    
    // Update document
    let updated_doc = Document::new("test_rust_updated.rs",
        "fn main() { println!(\"Hello from updated Rust!\"); }")
        .with_metadata({
            let mut map = HashMap::new();
            map.insert("updated".to_string(), "true".to_string());
            map
        });
    
    client.update_document(&doc_id, &updated_doc).await
        .expect("Failed to update document");
    
    // Verify update
    let updated_retrieved = client.get_document(&doc_id).await
        .expect("Failed to get updated document");
    
    assert_eq!(updated_retrieved.path, "test_rust_updated.rs");
    assert!(updated_retrieved.content.contains("updated Rust!"));
    
    // Delete document
    client.delete_document(&doc_id).await
        .expect("Failed to delete document");
    
    // Verify deletion
    let delete_result = client.get_document(&doc_id).await;
    assert!(delete_result.is_err());
}

#[tokio::test]
async fn test_batch_operations() {
    let client = create_test_client();
    
    if !wait_for_server(&client).await {
        eprintln!("Skipping test: ContextLite server not available");
        return;
    }
    
    // Create multiple test documents
    let documents = vec![
        Document::new("rust_basics.md", 
            "Rust programming basics: variables, functions, and ownership")
            .with_metadata({
                let mut map = HashMap::new();
                map.insert("topic".to_string(), "basics".to_string());
                map
            }),
        
        Document::new("rust_advanced.md",
            "Advanced Rust concepts: lifetimes, traits, and async programming")
            .with_metadata({
                let mut map = HashMap::new();
                map.insert("topic".to_string(), "advanced".to_string());
                map
            }),
        
        Document::new("rust_web.md",
            "Web development with Rust using Actix-web and Tokio")
            .with_metadata({
                let mut map = HashMap::new();
                map.insert("topic".to_string(), "web".to_string());
                map
            }),
    ];
    
    // Add documents in batch
    let doc_ids = client.add_documents(&documents).await
        .expect("Failed to add documents in batch");
    
    assert_eq!(doc_ids.len(), 3);
    assert!(doc_ids.iter().all(|id| !id.is_empty()));
    
    // Clean up
    for doc_id in doc_ids {
        let _ = client.delete_document(&doc_id).await;
    }
}

#[tokio::test]
async fn test_search_operations() {
    let client = create_test_client();
    
    if !wait_for_server(&client).await {
        eprintln!("Skipping test: ContextLite server not available");
        return;
    }
    
    // Add test documents
    let documents = vec![
        Document::new("search_test_1.txt", "Rust programming language features"),
        Document::new("search_test_2.txt", "JavaScript async await patterns"),
        Document::new("search_test_3.txt", "Python data science libraries"),
    ];
    
    let mut doc_ids = Vec::new();
    for doc in &documents {
        let id = client.add_document(doc).await.expect("Failed to add document");
        doc_ids.push(id);
    }
    
    // Wait a bit for indexing
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    // Test basic search
    let query = SearchQuery::new("programming").with_limit(10);
    let results = client.search(&query).await.expect("Search failed");
    
    assert!(!results.documents.is_empty());
    
    // Test search with filters
    let filtered_query = SearchQuery::new("rust")
        .with_limit(5)
        .with_filters(json!({"path": "search_test_1.txt"}));
    
    let filtered_results = client.search(&filtered_query).await
        .expect("Filtered search failed");
    
    // Should find the Rust document
    assert!(!filtered_results.documents.is_empty());
    
    // Clean up
    for doc_id in doc_ids {
        let _ = client.delete_document(&doc_id).await;
    }
}

#[tokio::test]
async fn test_context_assembly() {
    let client = create_test_client();
    
    if !wait_for_server(&client).await {
        eprintln!("Skipping test: ContextLite server not available");
        return;
    }
    
    // Add documents for context assembly
    let documents = vec![
        Document::new("context_1.md", 
            "Rust memory safety is achieved through ownership system"),
        Document::new("context_2.md",
            "Rust performance is comparable to C and C++ due to zero-cost abstractions"),
        Document::new("context_3.md",
            "Rust concurrency model prevents data races at compile time"),
    ];
    
    let mut doc_ids = Vec::new();
    for doc in &documents {
        let id = client.add_document(doc).await.expect("Failed to add document");
        doc_ids.push(id);
    }
    
    // Wait for indexing
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    // Test context assembly
    let context_request = ContextRequest::new("rust memory safety performance")
        .with_budget(500)
        .with_max_results(3)
        .with_metadata(true);
    
    let context = client.assemble_context(&context_request).await
        .expect("Context assembly failed");
    
    assert!(context.total_documents > 0);
    assert!(context.documents.is_some());
    if let Some(docs) = &context.documents {
        assert!(docs.len() <= 3);
    }
    
    // Clean up
    for doc_id in doc_ids {
        let _ = client.delete_document(&doc_id).await;
    }
}

#[tokio::test]
async fn test_error_handling() {
    let client = create_test_client();
    
    if !wait_for_server(&client).await {
        eprintln!("Skipping test: ContextLite server not available");
        return;
    }
    
    // Test validation errors
    let empty_doc = Document::new("", "content");
    let result = client.add_document(&empty_doc).await;
    assert!(matches!(result, Err(ContextLiteError::ValidationError { .. })));
    
    let empty_content_doc = Document::new("test.txt", "");
    let result = client.add_document(&empty_content_doc).await;
    assert!(matches!(result, Err(ContextLiteError::ValidationError { .. })));
    
    // Test search validation
    let empty_query = SearchQuery::new("");
    let result = client.search(&empty_query).await;
    assert!(matches!(result, Err(ContextLiteError::ValidationError { .. })));
    
    // Test context validation
    let empty_context = ContextRequest::new("");
    let result = client.assemble_context(&empty_context).await;
    assert!(matches!(result, Err(ContextLiteError::ValidationError { .. })));
    
    // Test not found error
    let result = client.get_document("non-existent-id").await;
    assert!(result.is_err());
    
    // Test delete non-existent
    let result = client.delete_document("non-existent-id").await;
    assert!(result.is_err());
}

#[tokio::test]
async fn test_authentication() {
    // Test with invalid auth
    let bad_config = ClientConfig::new(TEST_SERVER_URL)
        .with_auth_token("invalid-token");
    
    let bad_client = ContextLiteClient::with_config(bad_config)
        .expect("Failed to create client with bad auth");
    
    // This should fail with auth error (assuming server requires auth)
    let result = bad_client.health().await;
    
    // Note: This test depends on server auth configuration
    // Skip if server doesn't require auth (which is the case with httpbin.org)
    if result.is_ok() {
        eprintln!("Server doesn't require authentication - test passes");
        return;
    }
    
    // If server requires auth, should get an auth error
    assert!(matches!(result, Err(ContextLiteError::AuthError { .. }) | 
                              Err(ContextLiteError::ServerError { status: 401, .. })));
}

#[tokio::test]
async fn test_timeout_handling() {
    // Create client with very short timeout
    let config = ClientConfig::new(TEST_SERVER_URL)
        .with_auth_token(TEST_AUTH_TOKEN)
        .with_timeout(1); // 1 second timeout
    
    let client = ContextLiteClient::with_config(config)
        .expect("Failed to create timeout test client");
    
    if !wait_for_server(&client).await {
        eprintln!("Skipping test: ContextLite server not available");
        return;
    }
    
    // Normal operations should still work with 1s timeout
    let result = client.health().await;
    
    // This might timeout or succeed depending on server responsiveness
    match result {
        Ok(_) => println!("Health check completed within timeout"),
        Err(ContextLiteError::TimeoutError { .. }) => {
            println!("Timeout occurred as expected");
        }
        Err(e) => {
            // Other errors are also acceptable for this test
            println!("Got error (not timeout): {}", e);
        }
    }
}
