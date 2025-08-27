# ContextLite LangChain Adapter

Drop-in LangChain retriever for ContextLite's SMT-optimized context selection.

## Installation

```bash
pip install -e adapters/python/contextlite_langchain
```

## Usage

```python
from contextlite_langchain import ContextLiteRetriever

# Create retriever (assumes ContextLite server running on localhost:8080)
retriever = ContextLiteRetriever(base_url="http://localhost:8080", k=6)

# Get relevant documents
docs = retriever.get_relevant_documents("explain payment capture flow")
for doc in docs:
    print(f"File: {doc.metadata['file']}")
    print(f"Score: {doc.metadata['score']}")
    print(f"Content: {doc.page_content[:200]}...")
```

## Configuration

- `base_url`: ContextLite server URL (default: "http://localhost:8080")
- `k`: Number of documents to retrieve (default: 6)
- `budget_ms`: Time budget for retrieval in milliseconds (default: 80)
- `token`: Authentication token (reads from CONTEXTLITE_TOKEN env var)

## Integration with LangChain Chains

```python
from langchain.chains import RetrievalQA
from langchain.llms import OpenAI

llm = OpenAI()
retriever = ContextLiteRetriever()
qa_chain = RetrievalQA.from_chain_type(llm=llm, retriever=retriever)

result = qa_chain.run("How does payment capture work?")
```
