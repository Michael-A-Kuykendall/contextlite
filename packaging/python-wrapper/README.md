# ContextLite Python Wrapper

A Python wrapper for the ContextLite semantic context search engine.

## Installation

```bash
pip install contextlite
```

## Quick Start

```python
import contextlite

# Add documents
contextlite.add_document("The quick brown fox jumps over the lazy dog")
contextlite.add_document("Machine learning is a subset of artificial intelligence")

# Query for context
results = contextlite.query("artificial intelligence")
print(results)
```

## Advanced Usage

```python
from contextlite import ContextLite

# Initialize with custom binary path
client = ContextLite(binary_path="/custom/path/to/contextlite")

# Add document with metadata
client.add_document(
    content="Python is a high-level programming language",
    doc_id="python-doc-1",
    metadata={"category": "programming", "language": "python"}
)

# Query with options
results = client.query(
    "programming language",
    max_results=5,
    no_cache=True
)

# Index a directory
client.index_directory("/path/to/documents", recursive=True)

# Get statistics
stats = client.stats()
print(f"Total documents: {stats['total_documents']}")
```

## Binary Installation

The ContextLite binary will be automatically downloaded on first use. You can also manually download it:

```python
from contextlite import ContextLite
client = ContextLite(auto_download=True)
```

Or from the command line:
```bash
python -m contextlite --download
```

## Requirements

- Python 3.7+
- Internet connection for binary download (first time only)

## License

MIT License - see LICENSE file for details.
