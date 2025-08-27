# ContextLite npm Package

[![npm version](https://badge.fury.io/js/contextlite.svg)](https://badge.fury.io/js/contextlite)
[![Node.js versions](https://img.shields.io/node/v/contextlite.svg)](https://www.npmjs.com/package/contextlite)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A Node.js wrapper for [ContextLite](https://contextlite.com) - an ultra-fast context engine for retrieval and AI applications.

## 🚀 Quick Start

### Installation

```bash
# Install globally for CLI access
npm install -g contextlite

# Or install locally for programmatic use
npm install contextlite
```

### CLI Usage

```bash
# Start ContextLite server
contextlite --port 8080

# Get help
contextlite --help

# Use with npx (no global install needed)
npx contextlite --port 9090
```

### Programmatic Usage

```typescript
import { ContextLiteClient } from 'contextlite';

// Auto-start server and add documents
const client = new ContextLiteClient();

try {
    // Add some documents
    await client.addDocument("The quick brown fox jumps over the lazy dog.", "doc1");
    await client.addDocument("Node.js is a great runtime for server applications.", "doc2");
    await client.addDocument("TypeScript adds type safety to JavaScript development.", "doc3");
    
    // Query for relevant content
    const results = await client.query("server applications");
    console.log(`Found ${results.documents.length} relevant documents`);
    
    for (const doc of results.documents) {
        console.log(`Score: ${doc.score.toFixed(3)} - ${doc.content.slice(0, 50)}...`);
    }
} finally {
    await client.close();
}
```

### With Auto-cleanup

```typescript
import { withContextLiteClient } from 'contextlite';

await withContextLiteClient({ port: 8080 }, async (client) => {
    await client.addDocument("Hello from Node.js!");
    const results = await client.query("hello");
    console.log(results);
    // Client automatically closed when function exits
});
```

## 📋 Features

- **🔥 Ultra-Fast**: Native Go binary performance with Node.js convenience
- **🛠️ Auto-Management**: Automatically detects, downloads, and manages ContextLite binary
- **🔌 Easy Integration**: Simple async/await API with TypeScript support
- **🌍 Cross-Platform**: Works on Windows, macOS, and Linux (x64 and ARM64)
- **📦 Zero Config**: Works out of the box with automatic binary detection
- **🎯 CLI Ready**: Global installation provides `contextlite` command

## 🏗️ Architecture

This npm package provides Node.js bindings for the high-performance ContextLite engine:

1. **Binary Management**: Automatically manages ContextLite binary
2. **Easy Integration**: Downloads and configures ContextLite for your platform
3. **Server Management**: Handles ContextLite server lifecycle
4. **TypeScript API**: Provides fully-typed Node.js interface

## 📖 API Reference

### ContextLiteClient

The main interface for interacting with ContextLite from Node.js.

#### Constructor

```typescript
interface ClientOptions {
    host?: string;          // Server host (default: 'localhost')
    port?: number;          // Server port (default: 8080)
    autoStart?: boolean;    // Auto-start server if not running (default: true)
    databasePath?: string;  // Optional database file path
    timeout?: number;       // Request timeout in milliseconds (default: 30000)
}

const client = new ContextLiteClient(options);
```

#### Methods

- **`addDocument(content, documentId?, metadata?)`** - Add a document
- **`query(query, options?)`** - Search for documents  
- **`getDocument(documentId)`** - Retrieve specific document
- **`deleteDocument(documentId)`** - Delete a document
- **`getStats()`** - Get server statistics
- **`isServerRunning()`** - Check if server is responsive
- **`close()`** - Stop managed server and cleanup

### Types

```typescript
interface QueryOptions {
    maxResults?: number;
    minScore?: number;
}

interface QueryResult {
    documents: Array<{
        id: string;
        content: string;
        score: number;
        metadata?: Record<string, any>;
    }>;
    totalResults: number;
    queryTime: number;
}

interface Document {
    id: string;
    content: string;
    metadata?: Record<string, any>;
}
```

### Error Handling

```typescript
import { 
    ContextLiteClient,
    ContextLiteError,
    BinaryNotFoundError,
    ServerError
} from 'contextlite';

try {
    const client = new ContextLiteClient();
    await client.query("test");
} catch (error) {
    if (error instanceof BinaryNotFoundError) {
        console.error('ContextLite binary not found');
    } else if (error instanceof ServerError) {
        console.error('Server error:', error.message);
    } else if (error instanceof ContextLiteError) {
        console.error('ContextLite error:', error.message);
    }
}
```

## 🌐 Examples

## ⚙️ Dependency Note

We currently pin `node-fetch` to version 2.x to keep the distributed wrapper CommonJS-compatible. Version 3 of `node-fetch` is pure ESM and causes runtime errors (`ERR_REQUIRE_ESM`) when required from the transpiled `lib/` output that uses CommonJS. A future update will provide dual ESM/CJS builds; at that point this pin can be lifted.

### Document Management

```typescript
import { ContextLiteClient } from 'contextlite';

const client = new ContextLiteClient();

// Add documents with metadata
await client.addDocument(
    "Advanced TypeScript patterns for scalable applications.",
    "ts-patterns-guide",
    {
        category: "programming",
        difficulty: "advanced",
        tags: ["typescript", "patterns", "scalability"]
    }
);

// Query with options
const results = await client.query(
    "typescript patterns",
    { maxResults: 5, minScore: 0.7 }
);

for (const doc of results.documents) {
    console.log(`Document: ${doc.id}`);
    console.log(`Score: ${doc.score.toFixed(3)}`);
    console.log(`Content: ${doc.content.slice(0, 100)}...`);
    console.log(`Metadata:`, doc.metadata);
    console.log('-'.repeat(50));
}

await client.close();
```

### Batch Operations

```typescript
import { ContextLiteClient } from 'contextlite';

const documents = [
    "React makes building user interfaces simple and declarative.",
    "Vue.js provides an approachable, versatile framework.",
    "Angular offers a comprehensive platform for web applications.",
    "Svelte compiles to vanilla JavaScript for optimal performance."
];

const client = new ContextLiteClient();

// Batch add documents
for (const [index, content] of documents.entries()) {
    await client.addDocument(content, `framework-${index}`);
}

// Search across all documents
const results = await client.query("web framework");

console.log(`Found ${results.documents.length} relevant documents`);
results.documents.forEach(doc => {
    console.log(`• ${doc.content} (Score: ${doc.score.toFixed(3)})`);
});

await client.close();
```

### Custom Configuration

```typescript
import { ContextLiteClient } from 'contextlite';

// Connect to existing server
const remoteClient = new ContextLiteClient({
    host: 'my-server.com',
    port: 9090,
    autoStart: false  // Don't try to start server
});

// Use custom database location
const localClient = new ContextLiteClient({
    databasePath: '/path/to/my/database.db',
    port: 8081
});

// Custom timeout and options
const client = new ContextLiteClient({
    timeout: 60000,  // 60 second timeout
    autoStart: true
});
```

### Express.js Integration

```typescript
import express from 'express';
import { ContextLiteClient } from 'contextlite';

const app = express();
const client = new ContextLiteClient({ port: 8081 });

app.use(express.json());

app.post('/documents', async (req, res) => {
    try {
        const { content, metadata } = req.body;
        const result = await client.addDocument(content, undefined, metadata);
        res.json(result);
    } catch (error) {
        res.status(500).json({ error: error.message });
    }
});

app.get('/search', async (req, res) => {
    try {
        const { q, max_results, min_score } = req.query;
        const results = await client.query(q as string, {
            maxResults: max_results ? parseInt(max_results as string) : undefined,
            minScore: min_score ? parseFloat(min_score as string) : undefined
        });
        res.json(results);
    } catch (error) {
        res.status(500).json({ error: error.message });
    }
});

const server = app.listen(3000, () => {
    console.log('Server running on port 3000');
});

// Cleanup on shutdown
process.on('SIGTERM', async () => {
    await client.close();
    server.close();
});
```

## 🛠️ Development

### Local Development

```bash
# Clone the repository
git clone https://github.com/Michael-A-Kuykendall/contextlite.git
cd contextlite/npm-wrapper

# Install dependencies
npm install

# Build TypeScript
npm run build

# Run tests
npm test

# Link for local testing
npm link

# Test global command
contextlite --help
```

### Testing

```bash
# Install jest globally if needed
npm install -g jest

# Run tests with coverage
npm test -- --coverage

# Run specific test file
npm test -- binary-manager.test.ts
```

### Building and Publishing

```bash
# Build TypeScript to JavaScript
npm run build

# Check package contents
npm pack

# Publish to npm (requires npm login)
npm publish
```

## 🔧 Binary Management

The package handles ContextLite setup automatically:

### Installation Process

1. **Platform Detection**: Detects your system and architecture
2. **Binary Setup**: Downloads and configures ContextLite
3. **Ready to Use**: Makes ContextLite available for your application

### Manual Installation

You can also install ContextLite binary manually:

```bash
# Download from GitHub releases
curl -L https://github.com/Michael-A-Kuykendall/contextlite/releases/latest/download/contextlite_linux_amd64 -o contextlite
chmod +x contextlite
sudo mv contextlite /usr/local/bin/

# Or using npm global install
npm install -g contextlite
```

## 📝 Requirements

- **Node.js**: 14.0.0+
- **Platform**: Windows, macOS, Linux (x64/ARM64)
- **Dependencies**: `node-fetch`, `tar`
- **ContextLite Binary**: Auto-downloaded or manually installed

## 🚨 Troubleshooting

### Binary Not Found

```bash
# Manually download and install
npm run postinstall

# Or set NODE_ENV to avoid automatic download
NODE_ENV=development npm install
```

### Permission Issues

```bash
# On Unix systems, ensure binary is executable
chmod +x /path/to/contextlite

# Check PATH variable
echo $PATH
```

### Port Conflicts

```typescript
// Use a different port
const client = new ContextLiteClient({ port: 9090 });

// Or check if port is in use
netstat -tlnp | grep :8080
```

## 📄 License

This npm package is released under the MIT License. The ContextLite binary may have different licensing terms.

## 🔗 Links

- **Homepage**: https://contextlite.com
- **Documentation**: https://docs.contextlite.com
- **GitHub**: https://github.com/Michael-A-Kuykendall/contextlite
- **npm**: https://www.npmjs.com/package/contextlite
- **Issues**: https://github.com/Michael-A-Kuykendall/contextlite/issues

## 💬 Support

- **GitHub Issues**: For bug reports and feature requests
- **Documentation**: Comprehensive guides and API reference
- **npm Community**: Package-specific discussions

---

Built with ❤️ by the ContextLite team. Perfect for Node.js developers who need blazing-fast context retrieval.
