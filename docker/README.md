# ContextLite Docker Image

[![Docker Hub](https://img.shields.io/docker/v/makuykendall/contextlite?label=Docker%20Hub)](https://hub.docker.com/r/makuykendall/contextlite)
[![Docker Pulls](https://img.shields.io/docker/pulls/makuykendall/contextlite)](https://hub.docker.com/r/makuykendall/contextlite)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

Ultra-fast context engine for retrieval and AI applications with SMT-powered optimization. Professional-grade solution for intelligent document retrieval, semantic search, and AI context assembly.

## 🚀 Quick Start

```bash
# Run ContextLite server
docker run -p 8080:8080 makuykendall/contextlite

# Run with custom configuration
docker run -p 8080:8080 -e CONTEXTLITE_PORT=8080 makuykendall/contextlite

# Run with persistent storage
docker run -p 8080:8080 -v $(pwd)/data:/app/data makuykendall/contextlite
```

## ✨ Features

- **🔥 Ultra-Fast Performance**: Native Go binary optimized for speed
- **🧠 SMT-Powered**: Uses Satisfiability Modulo Theories for intelligent optimization
- **🔍 Semantic Search**: Advanced document retrieval with relevance scoring
- **⚡ Real-time Processing**: Sub-millisecond response times
- **🛡️ Production Ready**: Battle-tested with enterprise security
- **📦 Zero Dependencies**: Self-contained Docker image

## 🛠️ Configuration

### Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `CONTEXTLITE_PORT` | `8080` | Server port |
| `CONTEXTLITE_HOST` | `0.0.0.0` | Server host |
| `CONTEXTLITE_DB_PATH` | `/app/data/contextlite.db` | Database file path |
| `CONTEXTLITE_LOG_LEVEL` | `info` | Log level (debug, info, warn, error) |
| `CONTEXTLITE_AUTH_TOKEN` | - | Optional authentication token |

### Docker Compose

```yaml
version: '3.8'
services:
  contextlite:
    image: makuykendall/contextlite:latest
    ports:
      - "8080:8080"
    volumes:
      - ./data:/app/data
    environment:
      - CONTEXTLITE_PORT=8080
      - CONTEXTLITE_LOG_LEVEL=info
    restart: unless-stopped
```

## 📋 Usage Examples

### Basic Health Check

```bash
curl http://localhost:8080/health
```

### Add Documents

```bash
curl -X POST http://localhost:8080/api/v1/documents \
  -H "Content-Type: application/json" \
  -d '{
    "path": "example.txt",
    "content": "This is an example document for indexing."
  }'
```

### Search Documents

```bash
curl "http://localhost:8080/api/v1/search?q=example&limit=10"
```

### Context Assembly

```bash
curl -X POST http://localhost:8080/api/v1/context \
  -H "Content-Type: application/json" \
  -d '{
    "query": "example content",
    "budget": 2000,
    "max_results": 5
  }'
```

## 🔗 Integration

### With Client Libraries

```bash
# Python
pip install contextlite

# Rust
cargo add contextlite-client

# Node.js
npm install contextlite

# Docker as a service
docker run -d --name contextlite -p 8080:8080 makuykendall/contextlite
```

### Client Code Examples

**Python:**
```python
from contextlite import ContextLiteClient

with ContextLiteClient("http://localhost:8080") as client:
    client.add_document("Hello, World!", doc_id="doc1")
    results = client.query("hello")
    print(f"Found {len(results['documents'])} documents")
```

**JavaScript:**
```javascript
import { ContextLiteClient } from 'contextlite';

const client = new ContextLiteClient('http://localhost:8080');
await client.addDocument('Hello, World!', 'doc1');
const results = await client.query('hello');
console.log(`Found ${results.documents.length} documents`);
```

## 🚀 Performance

- **Response Time**: < 0.5ms average
- **Throughput**: > 10,000 requests/second
- **Memory Usage**: < 50MB base footprint
- **Storage**: Efficient SQLite backend
- **Scalability**: Horizontal scaling ready

## 📊 Monitoring

### Health Endpoints

- `GET /health` - Basic health check
- `GET /metrics` - Prometheus metrics
- `GET /debug/stats` - Performance statistics

### Logging

Structured JSON logs with configurable levels:

```bash
docker logs contextlite
```

## 🔐 Security

- Optional bearer token authentication
- CORS support for web applications
- Request rate limiting (configurable)
- Input validation and sanitization
- No external network dependencies

## 🛠️ Development

### Build from Source

```bash
git clone https://github.com/Michael-A-Kuykendall/contextlite.git
cd contextlite
docker build -t contextlite .
```

### Custom Configuration

```bash
# Override default command
docker run makuykendall/contextlite --help

# Custom configuration file
docker run -v $(pwd)/config.yaml:/app/config.yaml makuykendall/contextlite --config /app/config.yaml
```

## 📚 Documentation

- **Website**: [contextlite.com](https://contextlite.com)
- **API Documentation**: [docs.contextlite.com](https://docs.contextlite.com)
- **GitHub**: [github.com/Michael-A-Kuykendall/contextlite](https://github.com/Michael-A-Kuykendall/contextlite)
- **Docker Hub**: [hub.docker.com/r/makuykendall/contextlite](https://hub.docker.com/r/makuykendall/contextlite)

## 📄 License

This project is licensed under the MIT License - see the [LICENSE](https://github.com/Michael-A-Kuykendall/contextlite/blob/main/LICENSE) file for details.

---

**Built with ❤️ by the ContextLite Team**
