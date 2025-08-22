# ContextLite Rust Client

[![Crates.io](https://img.shields.io/crates/v/contextlite-client.svg)](https://crates.io/crates/contextlite-client)
[![Documentation](https://docs.rs/contextlite-client/badge.svg)](https://docs.rs/contextlite-client)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A high-performance, async Rust client for [ContextLite](https://contextlite.com) - the ultra-fast context engine for retrieval and AI applications.

## 🚀 Quick Start

Add this to your `Cargo.toml`:

```toml
[dependencies]
contextlite-client = "1.0"
```

Basic usage:

```rust
use contextlite_client::{ContextLiteClient, ClientConfig, Document, SearchQuery};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create a client with default configuration
    let client = ContextLiteClient::new()?;
    
    // Add a document
    let document = Document::new("example.txt", "This is an example document");
    let doc_id = client.add_document(&document).await?;
    
    // Search for documents
    let query = SearchQuery::new("example").with_limit(10);
    let results = client.search(&query).await?;
    
    println!("Found {} documents", results.documents.len());
    
    Ok(())
}
```

## ✨ Features

- **🔥 High Performance**: Built on Tokio for blazing-fast async operations
- **🛡️ Type Safety**: Comprehensive type definitions with builder patterns  
- **⚡ Connection Pooling**: HTTP connection pooling for optimal performance
- **🔧️ Error Handling**: Rich error types with proper error chaining
- **🔐 Authentication**: Bearer token authentication support
- **✅ Validation**: Client-side validation for better error messages
- **🛠️ Flexible API**: Builder patterns for easy configuration

## 📦 Supported Operations

✅ **Health Checks** - Server status and optimization system information  
✅ **Document Management** - Add, search, and delete documents  
✅ **Context Assembly** - Advanced context compilation  
✅ **Authentication** - Bearer token security  
✅ **Error Handling** - Comprehensive error types and retry logic

## 📋 Example Usage

### Document Operations

```rust
use contextlite_client::{Document, ContextLiteClient};

let client = ContextLiteClient::new()?;

// Add a document with metadata
let document = Document::new("tutorial.md", "Rust programming tutorial")
    .with_metadata(serde_json::json!({
        "type": "tutorial",
        "language": "rust",
        "difficulty": "beginner"
    }));

let doc_id = client.add_document(&document).await?;

// Update the document
let updated_doc = Document::new("tutorial.md", "Updated Rust programming tutorial");
client.update_document(&doc_id, &updated_doc).await?;

// Get the document
let retrieved = client.get_document(&doc_id).await?;

// Delete the document
client.delete_document(&doc_id).await?;
```

### Advanced Search

```rust
use contextlite_client::{SearchQuery, ContextLiteClient};

let client = ContextLiteClient::new()?;

let query = SearchQuery::new("rust programming")
    .with_limit(20)
    .with_offset(10)
    .with_filters(serde_json::json!({
        "difficulty": "beginner"
    }));

let results = client.search(&query).await?;

for doc_ref in results.documents {
    println!("{}: {:.3}", doc_ref.path, doc_ref.score.unwrap_or(0.0));
    if let Some(snippet) = doc_ref.snippet {
        println!("  \"{}\"", snippet);
    }
}
```

### Context Assembly

```rust
use contextlite_client::{ContextRequest, ContextLiteClient};

let client = ContextLiteClient::new()?;

let request = ContextRequest::new("explain rust ownership")
    .with_budget(2000)        // Token budget
    .with_max_results(5)      // Max documents
    .with_metadata(true);     // Include metadata

let context = client.assemble_context(&request).await?;

println!("Assembled context ({} tokens):", context.token_count.unwrap_or(0));
println!("{}", context.context);
```

## 🔧 Configuration

### Client Configuration

```rust
use contextlite_client::ClientConfig;

let config = ClientConfig::new("http://localhost:8083")
    .with_auth_token("your-bearer-token")
    .with_timeout(30)                      // 30 second timeout
    .with_connection_pool(true, 100);      // Enable pooling, max 100 connections

let client = ContextLiteClient::with_config(config)?;
```

### Environment Variables

The client respects these environment variables:

- `CONTEXTLITE_URL`: Default server URL
- `CONTEXTLITE_TOKEN`: Default authentication token
- `CONTEXTLITE_TIMEOUT`: Default timeout in seconds

## 🚨 Error Handling

The client provides comprehensive error handling with detailed error messages:

```rust
use contextlite_client::{ContextLiteClient, ContextLiteError};

match client.health().await {
    Ok(health) => println!("Server is healthy: {}", health.status),
    Err(ContextLiteError::AuthError { message }) => {
        eprintln!("Authentication failed: {}", message);
    },
    Err(ContextLiteError::ServerError { status, message }) => {
        eprintln!("Server error {}: {}", status, message);
    },
    Err(ContextLiteError::TimeoutError { seconds }) => {
        eprintln!("Request timed out after {} seconds", seconds);
    },
    Err(err) => eprintln!("Error: {}", err),
}
```

## 🛠️ Installation

Install ContextLite server:

```bash
# Via Cargo
cargo install contextlite

# Via Homebrew (macOS/Linux)
brew install contextlite

# Via npm
npm install -g contextlite

# Via Python pip
pip install contextlite
```

Then add the client to your project:

```bash
cargo add contextlite-client
```

## 📚 Documentation

- **Website**: [contextlite.com](https://contextlite.com)
- **API Docs**: [docs.rs/contextlite-client](https://docs.rs/contextlite-client)
- **GitHub**: [github.com/Michael-A-Kuykendall/contextlite](https://github.com/Michael-A-Kuykendall/contextlite)
- **Examples**: Check the `examples/` directory in the repository

## 🧪 Testing

Run the tests (requires a running ContextLite server):

```bash
# Start ContextLite server on port 8083
contextlite server --port 8083

# Run tests
cargo test
```

## 🚀 Performance

The Rust client is designed for high performance:

- **Connection Pooling**: Reuses HTTP connections for better throughput
- **Async I/O**: Non-blocking operations using Tokio
- **Zero-Copy**: Minimal data copying where possible
- **Efficient Serialization**: Fast JSON processing with serde

## 📄 License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch
3. Add tests for your changes
4. Ensure all tests pass
5. Submit a pull request

---

**Built with ❤️ by the ContextLite Team**
