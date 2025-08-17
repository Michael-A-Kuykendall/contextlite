//! Basic usage example for the ContextLite Rust client.
//! 
//! This example demonstrates:
//! - Creating a client
//! - Adding documents 
//! - Searching documents
//! - Basic error handling

use contextlite_client::{ContextLiteClient, Document, SearchQuery, ContextRequest};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("ContextLite Rust Client - Basic Usage Example");
    println!("===========================================");
    
    // Create client with default configuration (http://127.0.0.1:8082)
    let client = ContextLiteClient::new()?;
    
    // Check server health
    println!("\n1. Checking server health...");
    match client.health().await {
        Ok(health) => {
            println!("✓ Server is healthy: {}", health.status);
            if let Some(version) = health.version {
                println!("  Version: {}", version);
            }
        }
        Err(e) => {
            eprintln!("✗ Health check failed: {}", e);
            eprintln!("  Make sure ContextLite server is running on http://127.0.0.1:8082");
            return Ok(());
        }
    }
    
    // Get storage info
    println!("\n2. Getting storage information...");
    match client.storage_info().await {
        Ok(info) => {
            println!("✓ Storage info:");
            println!("  Total documents: {}", info.total_documents);
            println!("  Database size: {}", info.database_size);
            println!("  Index size: {}", info.index_size);
        }
        Err(e) => {
            eprintln!("✗ Failed to get storage info: {}", e);
        }
    }
    
    // Add some sample documents
    println!("\n3. Adding sample documents...");
    
    let documents = vec![
        Document::new("rust_tutorial.md", 
            "Rust is a systems programming language that runs blazingly fast, prevents segfaults, and guarantees thread safety.")
            .with_metadata(serde_json::json!({
                "type": "tutorial",
                "language": "rust",
                "difficulty": "beginner"
            })),
        
        Document::new("async_programming.md",
            "Async programming in Rust uses futures and the async/await syntax for non-blocking operations.")
            .with_metadata(serde_json::json!({
                "type": "guide", 
                "language": "rust",
                "difficulty": "intermediate"
            })),
        
        Document::new("web_development.md",
            "Building web applications with Rust frameworks like Actix-web, Warp, and Rocket.")
            .with_metadata(serde_json::json!({
                "type": "tutorial",
                "language": "rust", 
                "difficulty": "advanced"
            })),
    ];
    
    let mut doc_ids = Vec::new();
    
    for doc in &documents {
        match client.add_document(doc).await {
            Ok(id) => {
                println!("✓ Added document: {} (ID: {})", doc.path, id);
                doc_ids.push(id);
            }
            Err(e) => {
                eprintln!("✗ Failed to add document {}: {}", doc.path, e);
            }
        }
    }
    
    // Search for documents
    println!("\n4. Searching for documents...");
    
    let search_queries = vec![
        "rust programming",
        "async await",
        "web frameworks",
    ];
    
    for query_text in search_queries {
        println!("\n  Searching for: '{}'", query_text);
        
        let query = SearchQuery::new(query_text).with_limit(5);
        
        match client.search(&query).await {
            Ok(results) => {
                println!("  ✓ Found {} documents", results.documents.len());
                
                for (i, doc_ref) in results.documents.iter().enumerate() {
                    println!("    {}. {} (score: {:.3})", 
                        i + 1, 
                        doc_ref.path,
                        doc_ref.score.unwrap_or(0.0)
                    );
                    
                    if let Some(snippet) = &doc_ref.snippet {
                        println!("       \"{}\"", snippet);
                    }
                }
            }
            Err(e) => {
                eprintln!("  ✗ Search failed: {}", e);
            }
        }
    }
    
    // Assemble context
    println!("\n5. Assembling context...");
    
    let context_request = ContextRequest::new("explain rust programming concepts")
        .with_budget(1000)
        .with_max_results(3)
        .with_metadata(true);
    
    match client.assemble_context(&context_request).await {
        Ok(context) => {
            println!("✓ Assembled context ({} chars):", context.context.len());
            println!("  Documents used: {}", context.documents.len());
            
            if let Some(token_count) = context.token_count {
                println!("  Token count: {}", token_count);
            }
            
            // Show first 200 characters of context
            let preview = if context.context.len() > 200 {
                format!("{}...", &context.context[..200])
            } else {
                context.context.clone()
            };
            
            println!("  Context preview: \"{}\"", preview);
        }
        Err(e) => {
            eprintln!("✗ Context assembly failed: {}", e);
        }
    }
    
    // Clean up - delete the documents we added
    println!("\n6. Cleaning up...");
    
    for doc_id in doc_ids {
        match client.delete_document(&doc_id).await {
            Ok(_) => println!("✓ Deleted document: {}", doc_id),
            Err(e) => eprintln!("✗ Failed to delete document {}: {}", doc_id, e),
        }
    }
    
    println!("\n✓ Example completed successfully!");
    
    Ok(())
}
