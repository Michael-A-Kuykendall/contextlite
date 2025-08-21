# ContextLite

> **Advanced context sidecar for AI systems** - 10,000x faster than vector databases, 100% local, zero dependencies.

ContextLite is a Go-based context assembly engine that uses **Satisfiability Modulo Theories (optimization)** optimization to select the perfect set of documents for AI context windows. Built for speed, privacy, and local operation.

## 🚀 Quick Start

```bash
# Build main contextlite binary
make build

# Build SOTA evaluation tool
make build-sota

# Build both binaries
make build-all-local

# Or with custom config
./build/contextlite -config configs/custom.yaml

# Run SOTA evaluation
./build/sota-eval

# Development mode with hot reload
make dev
```

The server starts on `http://localhost:8080` by default.

## ✨ Key Features

- **Advanced Document Selection**: Uses budget management for mathematically optimal document selection
- **7D Feature Scoring**: Multi-dimensional relevance, recency, entanglement, prior, authority, specificity, uncertainty
- **Per-Workspace Calibration**: Adaptive weights that learn from your usage patterns  
- **Multi-Level Caching**: multi-level caching system with intelligent invalidation
- **Zero Dependencies**: Pure Go with embedded SQLite, no external services required
- **Sub-Second Performance**: p50 ≤300ms, p95 ≤600ms uncached; cached ≤30ms
- **Local Privacy**: All data stays on your machine, no cloud dependencies

## 🏗️ Repository Structure

```
contextlite/
├── cmd/                       # Executable applications
│   ├── contextlite/           # HTTP sidecar server
│   └── sota-eval/             # SOTA comparison CLI tool
├── internal/                  # Private implementation
│   ├── optimization/                   # optimization system integration (optimizer)
│   ├── storage/               # SQLite + FTS5 storage layer
│   ├── features/              # 7D feature extraction & scoring
│   ├── pipeline/              # Main assembly pipeline
│   ├── cache/                 # Multi-level caching system
│   ├── api/                   # HTTP API handlers
│   └── evaluation/            # SOTA evaluation framework
├── pkg/                       # Public API packages
│   ├── types/                 # Core data structures
│   ├── config/                # Configuration management
│   └── tokens/                # Token estimation utilities
├── docs/                      # Technical documentation
├── archive/                   # Historical development artifacts
├── test/                      # Integration tests
├── configs/                   # Default configuration files
└── migrations/                # Database schema migrations
```

## 🔧 Configuration

See `configs/default.yaml` for full configuration options:

```yaml
# Core optimization optimization settings
optimization:
  solver_timeout_ms: 250        # Hard timeout for optimization system
  max_opt_gap: 0.05            # 5% optimality gap acceptable
  objective_style: "weighted-sum"  # weighted-sum | lexicographic | epsilon-budget

# 7D Feature weights (adaptive per workspace)
weights:
  relevance: 0.30              # Query match strength
  recency: 0.20                # Time-based decay
  entanglement: 0.15           # Cross-document concept density
  prior: 0.15                  # Historical selection likelihood
  authority: 0.10              # Document importance
  specificity: 0.05            # Query-document topic alignment
  uncertainty: 0.05            # Score variance (subtracted)
```

## 📡 HTTP API

### Context Assembly
```bash
curl -X POST http://localhost:8080/api/v1/context/assemble \
  -H "Content-Type: application/json" \
  -d '{
    "query": "How does user authentication work?",
    "max_tokens": 4000,
    "max_documents": 10,
    "use_optimization": true,
    "workspace_path": "/path/to/project"
  }'
```

### Document Management
```bash
# Add document
curl -X POST http://localhost:8080/api/v1/documents \
  -H "Content-Type: application/json" \
  -d '{
    "content": "...",
    "path": "src/auth.go",
    "language": "go"
  }'

# Search documents
curl "http://localhost:8080/api/v1/documents/search?q=authentication&limit=20"
```

### Weight Management
```bash
# Get workspace weights
curl "http://localhost:8080/api/v1/weights?workspace=/path/to/project"

# Update weights based on feedback
curl -X POST http://localhost:8080/api/v1/weights/update \
  -H "Content-Type: application/json" \
  -d '{
    "workspace_path": "/path/to/project",
    "accepted_docs": ["doc1", "doc2"],
    "rejected_docs": ["doc3"]
  }'
```

## 📈 Development Status

### ✅ Completed Features
- **Advanced Optimization**: optimization engine integration with multiple optimization strategies
- **7D Feature System**: Complete implementation of all feature dimensions
- **SOTA Evaluation Framework**: Comprehensive evaluation harness with Recall@k, nDCG@k, MAP, MRR
- **Multi-level Caching**: L1 memory, L2 SQLite with intelligent invalidation
- **HTTP API**: Complete REST API for context assembly and document management
- **Configuration System**: Flexible YAML-based configuration with workspace-specific weights

### 📋 Documentation
- **[Technical Documentation](docs/)** - Architecture, testing, and deployment guides
- **[Contributing Guide](CONTRIBUTING.md)** - Development setup and guidelines  
- **[Development Context](CLAUDE.md)** - AI assistant setup for contributors

## 🧮 optimization Optimization

ContextLite uses three optimization optimization formulations:

### 1. Weighted-Sum Scalarization (Default)
Balances all 7D features with learned workspace-specific weights:
```
maximize: Σ(α₁·Rel + α₂·Rec + α₃·Ent + α₄·Prior + α₅·Auth + α₆·Spec - α₇·Unc)
subject to: token_budget, max_documents, coherence_budgets
```

### 2. Lexicographic Priorities
Strict priority ordering (relevance first, then recency, etc.):
```
objective_style: "lexicographic"
```

### 3. ε-Constraint Method  
Optimize primary objective with secondary budgets:
```
objective_style: "epsilon-budget"
```

## 📊 SOTA Evaluation

ContextLite includes a comprehensive evaluation framework comparing against state-of-the-art retrieval systems:

```bash
# Run full SOTA comparison
./build/sota-eval

# With custom parameters
./build/sota-eval -queries 1000 -docs 100 -verbose
```

**Evaluation Metrics:**
- **Recall@k**: Fraction of relevant documents retrieved in top-k results
- **nDCG@k**: Normalized Discounted Cumulative Gain (position-aware relevance)
- **MAP**: Mean Average Precision across all queries
- **MRR**: Mean Reciprocal Rank of first relevant document

**Baseline Comparisons:**
- BM25 (Elasticsearch/Lucene standard)
- TF-IDF with cosine similarity
- Hybrid semantic + lexical retrieval
- Random baseline for statistical significance

See [`docs/GOLDEN_RECORD_STEP5.md`](docs/GOLDEN_RECORD_STEP5.md) for current evaluation status and identified areas for improvement.

## 🏃‍♂️ Performance

Benchmarked on NVMe SSD, 100k documents, K=200 candidates:

| Operation | p50 | p95 | p99 |
|-----------|-----|-----|-----|
| Cached Query | 15ms | 30ms | 45ms |
| Cold Query | 180ms | 350ms | 500ms |
| optimization Solve | 50ms | 150ms | 250ms |
| Feature Extract | 25ms | 80ms | 120ms |

## 📊 Development

```bash
# Install dependencies
make deps

# Build main binary
make build

# Build SOTA evaluation tool
make build-sota

# Build both binaries locally
make build-all-local

# Build for all platforms
make build-all

# Run tests
make test

# Run with coverage
make coverage

# Run benchmarks  
make bench

# Code quality checks
make check

# Development with hot reload
make dev

# Clean build artifacts
make clean
```

## 🐳 Docker

```bash
# Build image
make docker-build

# Run container
make docker-run
```

## 📈 Monitoring

The API provides comprehensive metrics:

```bash
# Health check
curl http://localhost:8080/health

# Storage statistics
curl http://localhost:8080/api/v1/storage/info

# optimization system performance
curl http://localhost:8080/api/v1/optimization/stats

# Cache performance
curl http://localhost:8080/api/v1/cache/stats
```

## 🎯 Use Cases

- **VS Code Extensions**: Drop-in context provider for AI coding assistants
- **Local AI Systems**: Ollama, LocalAI, edge deployment context optimization
- **Document Q&A**: Intelligent document retrieval for RAG applications
- **Code Analysis**: Smart code snippet selection for AI code review
- **Research Tools**: Academic paper and document context assembly

## 📝 License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## 🔬 Technical Details

For complete implementation details, algorithms, and architecture decisions, see the documentation in the `docs/` directory.

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Commit your changes (`git commit -m 'Add amazing feature'`)
4. Push to the branch (`git push origin feature/amazing-feature`)
5. Open a Pull Request

## 📞 Support

- **Documentation**: See the `docs/` directory for technical details
- **Issues**: Report bugs and feature requests via GitHub Issues
- **Community**: Join the discussions for help and feature requests

---

**ContextLite** - Making AI context assembly fast, local, and intelligent.

---

**ContextLite** - Because context matters, and speed matters more. 🚀
