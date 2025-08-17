# ContextLite LlamaIndex Adapter

Drop-in LlamaIndex retriever for ContextLite's SMT-optimized context selection.

## Installation

```bash
pip install -e adapters/python/contextlite_llamaindex
```

## Usage

```python
from contextlite_llamaindex import ContextLiteRetriever

# Create retriever (assumes ContextLite server running on localhost:8080)
retriever = ContextLiteRetriever(base_url="http://localhost:8080", k=6)

# Get relevant documents
nodes = retriever.retrieve("explain payment capture flow")
for node_with_score in nodes:
    print(f"File: {node_with_score.node.metadata['file']}")
    print(f"Score: {node_with_score.score}")
    print(f"Content: {node_with_score.node.text[:200]}...")
```

## Configuration

- `base_url`: ContextLite server URL (default: "http://localhost:8080")
- `k`: Number of documents to retrieve (default: 6)  
- `budget_ms`: Time budget for retrieval in milliseconds (default: 80)
- `token`: Authentication token (reads from CONTEXTLITE_TOKEN env var)

## Integration with LlamaIndex

```python
from llama_index.core import VectorStoreIndex
from llama_index.core.query_engine import RetrieverQueryEngine

retriever = ContextLiteRetriever()
query_engine = RetrieverQueryEngine.from_args(retriever=retriever)

response = query_engine.query("How does payment capture work?")
print(response)
```
