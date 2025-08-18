# ContextLite for Node.js

A Node.js wrapper for the ContextLite semantic context search engine.

## Installation

```bash
npm install contextlite
```

The ContextLite binary will be automatically downloaded during installation.

## Quick Start

```javascript
const { query, addDocument, indexDirectory } = require('contextlite');

// Add documents
await addDocument("The quick brown fox jumps over the lazy dog");
await addDocument("Machine learning is a subset of artificial intelligence");

// Query for context
const results = await query("artificial intelligence");
console.log(results);
```

## Advanced Usage

```javascript
const { ContextLite } = require('contextlite');

// Initialize client
const client = new ContextLite();

// Add document with metadata
await client.addDocument(
  "Node.js is a JavaScript runtime built on Chrome's V8 engine",
  {
    id: "nodejs-doc-1",
    metadata: { category: "technology", language: "javascript" }
  }
);

// Query with options
const results = await client.query("JavaScript runtime", {
  maxResults: 5,
  noCache: true
});

// Index a directory
await client.indexDirectory("/path/to/documents", { recursive: true });

// Get statistics
const stats = await client.stats();
console.log(`Total documents: ${stats.total_documents}`);

// Start HTTP server
const server = client.startServer({ port: 8080 });
console.log(`Server running on port ${server.port}`);

// Stop server when done
// server.stop();
```

## Command Line Interface

```bash
# Query for context
npx contextlite query "artificial intelligence"

# Add a document
npx contextlite add "Machine learning is fascinating"

# Index a directory
npx contextlite index ./documents

# Show statistics
npx contextlite stats

# Clear cache
npx contextlite cache clear
```

## API Reference

### ContextLite Class

#### Methods

- `async version()` - Get ContextLite version
- `async addDocument(content, options)` - Add a document
  - `content` (string) - Document content
  - `options.id` (string) - Optional document ID
  - `options.metadata` (object) - Optional metadata
- `async query(queryText, options)` - Query for context
  - `queryText` (string) - Query string
  - `options.maxResults` (number) - Maximum results (default: 10)
  - `options.noCache` (boolean) - Bypass cache (default: false)
- `async indexDirectory(directory, options)` - Index directory
  - `directory` (string) - Directory path
  - `options.recursive` (boolean) - Recursive indexing (default: true)
- `async stats()` - Get database statistics
- `async clearCache()` - Clear query cache
- `startServer(options)` - Start HTTP server
  - `options.port` (number) - Server port (default: 8080)
  - Returns: `{ pid, port, stop() }`

### Convenience Functions

- `async query(queryText, options)` - Quick query
- `async addDocument(content, options)` - Quick add document
- `async indexDirectory(directory, options)` - Quick index directory

## Error Handling

```javascript
const { ContextLite, ContextLiteError } = require('contextlite');

try {
  const client = new ContextLite();
  const results = await client.query("example");
} catch (error) {
  if (error instanceof ContextLiteError) {
    console.error('ContextLite error:', error.message);
  } else {
    console.error('Unexpected error:', error);
  }
}
```

## Requirements

- Node.js 14.0.0 or higher
- Internet connection for binary download (first time only)

## Platform Support

- Linux (x64, arm64)
- macOS (x64, arm64)
- Windows (x64, arm64)

## License

MIT License - see LICENSE file for details.
