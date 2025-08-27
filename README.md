# ContextLite

> **High-performance context engine with workspace clustering** - Multi-project AI context management, 100% local, zero dependencies.

ContextLite is a Go-based context assembly engine with advanced SMT optimization and **enterprise-grade workspace clustering**. Perfect for managing multiple AI projects with isolated resource management and intelligent load balancing.

## 🆕 **NEW: Workspace Clustering & Multi-Project Support**

✨ **Just Released**: Professional workspace isolation, resource management, and load balancing for multi-project AI development.

📚 **[Documentation](./docs/)** | 🏘️ **[Clustering Guide](./docs/CLUSTERING_GUIDE.md)** | 📡 **[API Reference](./docs/API_REFERENCE.md)**

## 🏢 **Enterprise Workspace Clustering**

Manage multiple AI projects with professional-grade isolation and resource management:

```bash
# Enable clustering in your config
cluster:
  enabled: true
  workspace_routing: true
  resource_limits:
    "mission-architect":
      max_concurrent_requests: 10
      max_memory_mb: 512
      priority: 8

# Use workspace-specific requests
curl -H "X-Workspace-ID: mission-architect" \
     -X POST http://localhost:8080/api/v1/assemble \
     -d '{"query": "AI enforcement patterns"}'
```

**Key Benefits:**
- 🏘️ **Workspace Isolation**: Complete separation of projects and resources
- ⚖️ **Resource Management**: Per-workspace limits and priority scheduling  
- 🎯 **Affinity Routing**: Smart request routing and sticky sessions
- 📊 **Usage Analytics**: Detailed monitoring and access pattern detection
- 🔄 **Load Balancing**: Distribute requests across multiple instances

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

## 🔄 Automatic Port Management

ContextLite now supports **automatic port discovery** for applications that need to connect to running instances without hardcoded port numbers:

```go
// No more port configuration drift!
client := NewAutoDiscoveryClient()
if err := client.AutoDiscover(); err != nil {
    log.Fatal("No ContextLite instances found")
}

// Automatically connects to healthy instance
result, err := client.Query("your query here", 10)
```

**Key Benefits:**
- ✅ **Zero Configuration**: Automatically discovers running instances
- ✅ **Port Conflict Resolution**: Works with multiple concurrent instances  
- ✅ **Automatic Failover**: Switches between healthy instances seamlessly
- ✅ **Development Friendly**: No more "port already in use" errors
- ✅ **Production Ready**: Built-in health monitoring and redundancy

**Example Usage:**
```bash
# Start multiple instances on different ports
./contextlite --config configs/workspace1.yaml &  # Starts on 8080
./contextlite --config configs/workspace2.yaml &  # Auto-finds 8081
./contextlite --config configs/workspace3.yaml &  # Auto-finds 8082

# Your application automatically discovers and connects to all instances
go run examples/automatic_port_management.go
```

See [`examples/automatic_port_management.go`](examples/automatic_port_management.go) for a complete integration example.

## ✨ Key Features

- **SMT-Optimized Selection**: Uses constraint satisfaction for mathematically optimal document selection
- **Advanced Feature Scoring**: Multi-dimensional relevance analysis with machine learning optimization
- **Workspace Clustering**: Multi-project support with resource isolation and affinity routing
- **Per-Workspace Calibration**: Adaptive weights that learn from your usage patterns  
- **Multi-Level Caching**: L1 memory, L2 SQLite, L3 quantum snapshots with intelligent invalidation
- **Zero Dependencies**: Pure Go with embedded SQLite, no external services required
- **Sub-Second Performance**: p50 ≤300ms, p95 ≤600ms uncached; cached ≤30ms
- **Local Privacy**: All data stays on your machine, no cloud dependencies

## 📖 Documentation

- **[Documentation](./docs/)** - Architecture guides and API reference
- **[Clustering Guide](./docs/CLUSTERING_GUIDE.md)** - Multi-project and workspace management
- **[Contributing Guide](CONTRIBUTING.md)** - Development setup and guidelines  
- **[License](LICENSE)** - MIT License terms

## 🏗️ Repository Structure

```
contextlite/
├── cmd/                       # Executable applications
│   ├── contextlite/           # HTTP sidecar server
│   └── sota-eval/             # SOTA comparison CLI tool
├── internal/                  # Private implementation
│   ├── optimization/          # Advanced optimization engine
│   ├── storage/               # SQLite + FTS5 storage layer
│   ├── features/              # Multi-dimensional feature extraction & scoring
│   ├── pipeline/              # Main assembly pipeline
│   ├── cache/                 # Multi-level caching system
│   ├── api/                   # HTTP API handlers
│   └── evaluation/            # Performance evaluation framework
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
# Core SMT optimization settings
smt:
  solver_timeout_ms: 250        # Hard timeout for SMT solver
  max_opt_gap: 0.05            # 5% optimality gap acceptable
  objective_style: "weighted-sum"  # weighted-sum | lexicographic | epsilon-constraint

# Feature weights (adaptive per workspace)
weights:
  # Weights are automatically tuned based on usage patterns
  # See documentation for configuration options
```

## 🏘️ Workspace Clustering

ContextLite supports clustering for managing multiple projects and workspaces:

```yaml
# Enable clustering in configs/cluster.yaml
cluster:
  enabled: true
  node_id: "contextlite-node-1"
  
  affinity:
    workspace_routing: true
    sticky_sessions: true
    rules:
      "mission-architect":
        preferred_nodes: ["node-1"]
        resource_tier: "high"
        
  resource_limits:
    "mission-architect":
      max_concurrent_requests: 10
      max_tokens_per_minute: 50000
      max_memory_mb: 512
```

**Workspace-aware requests:**
```bash
curl -H "X-Workspace-ID: mission-architect" \
     -X POST http://localhost:8080/api/v1/assemble \
     -d '{"query": "AI enforcement patterns"}'
```

See the [Clustering Guide](./docs/CLUSTERING_GUIDE.md) for complete setup instructions.

## 📡 HTTP API

### Context Assembly
```bash
curl -X POST http://localhost:8080/api/v1/context/assemble \
  -H "Content-Type: application/json" \
  -d '{
    "query": "How does user authentication work?",
    "max_tokens": 4000,
    "max_documents": 10,
    "use_smt": true,
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
- **SMT Integration**: Z3 solver integration with multiple optimization strategies
- **7D Feature System**: Complete implementation of all feature dimensions
- **SOTA Evaluation Framework**: Comprehensive evaluation harness with Recall@k, nDCG@k, MAP, MRR
- **Multi-level Caching**: L1 memory, L2 SQLite with intelligent invalidation
- **HTTP API**: Complete REST API for context assembly and document management
- **Configuration System**: Flexible YAML-based configuration with workspace-specific weights

### 📋 Documentation
- **[Technical Documentation](docs/)** - Architecture, testing, and deployment guides
- **[Contributing Guide](CONTRIBUTING.md)** - Development setup and guidelines  
- **[Development Context](CLAUDE.md)** - AI assistant setup for contributors

## 🧮 Advanced Optimization

ContextLite uses sophisticated mathematical optimization for document selection:

- **Weighted Optimization**: Balances multiple relevance factors
- **Priority-based Selection**: Configurable ranking strategies  
- **Constraint Satisfaction**: Respects token budgets and document limits

See documentation for configuration options.

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
| SMT Solve | 50ms | 150ms | 250ms |
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

# SMT solver performance
curl http://localhost:8080/api/v1/smt/stats

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
