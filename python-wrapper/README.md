# ContextLite Python Package

[![PyPI version](https://badge.fury.io/py/contextlite.svg)](https://badge.fury.io/py/contextlite)
[![Python versions](https://img.shields.io/pypi/pyversions/contextlite.svg)](https://pypi.org/project/contextlite/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A Python wrapper for [ContextLite](https://contextlite.com) - an ultra-fast context engine for retrieval and AI applications.

## 🚀 Quick Start

### Installation

```bash
pip install contextlite
```

### Basic Usage

```python
from contextlite import ContextLiteClient

# Auto-start server and add documents
with ContextLiteClient() as client:
    # Add some documents
    client.add_document("The quick brown fox jumps over the lazy dog.", doc_id="doc1")
    client.add_document("Python is a great programming language.", doc_id="doc2")
    client.add_document("Machine learning is transforming software development.", doc_id="doc3")
    
    # Query for relevant content
    results = client.query("programming language")
    print(f"Found {len(results['documents'])} relevant documents")
    
    for doc in results['documents']:
        print(f"Score: {doc['score']:.3f} - {doc['content'][:50]}...")
```

### Command Line Usage

The package also installs a `contextlite` command that acts as a wrapper for the native binary:

```bash
# Start ContextLite server
contextlite --port 8080

# Get help
contextlite --help
```

## 📋 Features

- **🔥 Ultra-Fast**: Native Go binary performance with Python convenience
- **🛠️ Auto-Management**: Automatically detects, downloads, and manages ContextLite binary
- **🔌 Easy Integration**: Simple Python API with context manager support
- **🌍 Cross-Platform**: Works on Windows, macOS, and Linux (x64 and ARM64)
- **⚡ Zero Dependencies**: Core functionality requires only standard library (requests for auto-download)

## 🏗️ Architecture

This Python package is a "shim" that provides Python bindings for the high-performance ContextLite binary:

1. **Binary Detection**: Automatically finds ContextLite binary in PATH or common install locations
2. **Auto-Download**: Downloads appropriate binary for your platform if not found
3. **Server Management**: Optionally manages ContextLite server lifecycle  
4. **Python API**: Provides convenient Python interface over REST API

## 📖 API Reference

### ContextLiteClient

The main interface for interacting with ContextLite.

#### Constructor

```python
ContextLiteClient(
    host="localhost",           # Server host
    port=8080,                 # Server port  
    auto_start=True,           # Auto-start server if not running
    database_path=None,        # Optional database file path
    timeout=30.0               # Request timeout in seconds
)
```

#### Methods

- **`add_document(content, document_id=None, metadata=None)`** - Add a document
- **`query(query, max_results=None, min_score=None)`** - Search for documents
- **`get_document(document_id)`** - Retrieve specific document
- **`delete_document(document_id)`** - Delete a document
- **`get_stats()`** - Get server statistics
- **`is_server_running()`** - Check if server is responsive

### Context Manager

```python
from contextlite import contextlite_client

with contextlite_client(port=8080) as client:
    client.add_document("Hello world!")
    results = client.query("hello")
```

## 🔧 Binary Management

The package handles ContextLite binary management automatically:

### Detection Strategy

1. **PATH**: Checks if `contextlite` is in system PATH
2. **System Locations**: Common install directories (`/usr/local/bin`, Program Files, etc.)
3. **User Data**: User-specific data directory
4. **Package Data**: Bundled with package (if available)

### Auto-Download

If no binary is found, the package will:

1. Detect your platform and architecture
2. Download the appropriate binary from GitHub releases
3. Store it in user data directory
4. Make it executable and ready to use

### Manual Installation

You can also install ContextLite binary manually:

```bash
# Download from GitHub releases
curl -L https://github.com/Michael-A-Kuykendall/contextlite/releases/latest/download/contextlite_linux_amd64 -o contextlite
chmod +x contextlite
sudo mv contextlite /usr/local/bin/
```

## 🌐 Examples

### Document Management

```python
from contextlite import ContextLiteClient

client = ContextLiteClient()

# Add documents with metadata
client.add_document(
    content="Advanced machine learning techniques for natural language processing.",
    document_id="ml-nlp-guide",
    metadata={
        "category": "machine-learning",
        "difficulty": "advanced",
        "tags": ["nlp", "deep-learning", "transformers"]
    }
)

# Query with filters
results = client.query(
    query="natural language processing",
    max_results=5,
    min_score=0.7
)

for doc in results['documents']:
    print(f"Document: {doc['id']}")
    print(f"Score: {doc['score']:.3f}")
    print(f"Content: {doc['content'][:100]}...")
    print(f"Metadata: {doc.get('metadata', {})}")
    print("-" * 50)
```

### Batch Operations

```python
from contextlite import ContextLiteClient

# Process multiple documents
documents = [
    "Python is a versatile programming language.",
    "JavaScript powers modern web development.", 
    "Go offers excellent performance for backend services.",
    "Rust provides memory safety without garbage collection."
]

with ContextLiteClient() as client:
    # Batch add documents
    for i, content in enumerate(documents):
        client.add_document(content, document_id=f"lang-{i}")
    
    # Search across all documents
    results = client.query("backend programming")
    
    print(f"Found {len(results['documents'])} relevant documents")
    for doc in results['documents']:
        print(f"• {doc['content']} (Score: {doc['score']:.3f})")
```

### Custom Server Configuration

```python
from contextlite import ContextLiteClient

# Connect to existing server
client = ContextLiteClient(
    host="remote-server.com",
    port=9090,
    auto_start=False  # Don't try to start server
)

# Use custom database location
local_client = ContextLiteClient(
    database_path="/path/to/my/database.db",
    port=8081
)
```

## 🚨 Error Handling

```python
from contextlite import (
    ContextLiteClient, 
    BinaryNotFoundError, 
    ServerError,
    ContextLiteError
)

try:
    with ContextLiteClient() as client:
        results = client.query("test query")
        
except BinaryNotFoundError:
    print("ContextLite binary not found. Please install it manually.")
    
except ServerError as e:
    print(f"Server error: {e}")
    
except ContextLiteError as e:
    print(f"ContextLite error: {e}")
```

## 🛠️ Development

### Local Development

```bash
# Clone the repository
git clone https://github.com/Michael-A-Kuykendall/contextlite.git
cd contextlite/python-wrapper

# Install in development mode
pip install -e .

# Install development dependencies
pip install -e .[dev]

# Run tests
pytest

# Format code
black contextlite/
isort contextlite/

# Type checking
mypy contextlite/
```

### Testing

```python
import pytest
from contextlite import ContextLiteClient

def test_basic_operations():
    with ContextLiteClient() as client:
        # Add document
        response = client.add_document("Test content", doc_id="test1")
        assert response['success'] == True
        
        # Query
        results = client.query("test")
        assert len(results['documents']) > 0
        
        # Cleanup
        client.delete_document("test1")
```

## 📝 Requirements

- **Python**: 3.8+ 
- **Platform**: Windows, macOS, Linux (x64/ARM64)
- **Dependencies**: `requests`, `platformdirs`
- **ContextLite Binary**: Auto-downloaded or manually installed

## 📄 License

This Python package is released under the MIT License. The ContextLite binary may have different licensing terms.

## 🔗 Links

- **Homepage**: https://contextlite.com
- **Documentation**: https://docs.contextlite.com  
- **GitHub**: https://github.com/Michael-A-Kuykendall/contextlite
- **PyPI**: https://pypi.org/project/contextlite/
- **Issues**: https://github.com/Michael-A-Kuykendall/contextlite/issues

## 💬 Support

- **GitHub Issues**: For bug reports and feature requests
- **Documentation**: Comprehensive guides and API reference
- **Community**: Join our Discord server for discussions

---

Built with ❤️ by the ContextLite team. Made for developers who need blazing-fast context retrieval.
