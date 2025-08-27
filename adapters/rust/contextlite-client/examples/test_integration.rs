//! Integration test example that connects to the test server on port 8083

use contextlite_client::{ContextLiteClient, ClientConfig, Document, SearchQuery, ContextRequest};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("ContextLite Rust Client - Integration Test");
    println!("=========================================");
    
    // Create client for test server
    let config = ClientConfig::new("http://127.0.0.1:8082")
        .with_auth_token("contextlite-dev-token-2025")
        .with_timeout(30);
    
    let client = ContextLiteClient::with_config(config)?;
    
    // Check server health
    println!("\n1. Checking server health...");
    match client.health().await {
        Ok(health) => {
            println!("✓ Server is healthy: {} (v{})", health.status, health.version);
            println!("  SMT Solver: {} v{}", health.smt.solver, health.smt.version);
            println!("  Documents indexed: {}", health.database.documents_indexed);
        }
        Err(e) => {
            eprintln!("✗ Health check failed: {}", e);
            eprintln!("  Make sure ContextLite server is running on http://127.0.0.1:8082");
            return Ok(());
        }
    }
    
    // Add a test document
    println!("\n2. Adding test document...");
    let mut metadata = HashMap::new();
    metadata.insert("language".to_string(), "rust".to_string());
    metadata.insert("test".to_string(), "true".to_string());
    metadata.insert("created_by".to_string(), "integration_test".to_string());
    
    let document = Document::new("rust_test.rs", 
        "fn main() { println!(\"Hello from Rust!\"); }")
        .with_metadata(metadata);
    
    let doc_id = match client.add_document(&document).await {
        Ok(id) => {
            println!("✓ Added document: {} (ID: {})", document.path, id);
            id
        }
        Err(e) => {
            eprintln!("✗ Failed to add document: {}", e);
            return Ok(());
        }
    };
    
    // Search for the document
    println!("\n3. Searching for document...");
    let query = SearchQuery::new("rust hello").with_limit(5);
    
    match client.search(&query).await {
        Ok(results) => {
            println!("✓ Found {} documents", results.documents.len());
            
            for (i, doc_ref) in results.documents.iter().enumerate() {
                println!("  {}. {} (score: {:.3})", 
                    i + 1, 
                    doc_ref.path,
                    doc_ref.score.unwrap_or(0.0)
                );
            }
        }
        Err(e) => {
            eprintln!("✗ Search failed: {}", e);
        }
    }
    
    // Test context assembly
    println!("\n4. Testing context assembly...");
    let context_request = ContextRequest::new("rust programming")
        .with_budget(1000)
        .with_max_results(3);
    
    match client.assemble_context(&context_request).await {
        Ok(context) => {
            println!("✓ Assembled context for query: {}", context.query);
            println!("  Documents included: {}", context.total_documents);
            println!("  Total tokens: {}", context.total_tokens);
            println!("  Coherence score: {:.3}", context.coherence_score);
            println!("  Cache hit: {}", context.cache_hit);
        }
        Err(e) => {
            eprintln!("✗ Context assembly failed: {}", e);
        }
    }
    
    // Clean up
    println!("\n5. Cleaning up...");
    match client.delete_document(&doc_id).await {
        Ok(_) => println!("✓ Deleted test document"),
        Err(e) => eprintln!("✗ Failed to delete document: {}", e),
    }
    
    println!("\n✓ Integration test completed successfully!");
    
    Ok(())
}
