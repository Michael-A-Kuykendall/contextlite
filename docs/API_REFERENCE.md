# ContextLite API Reference

## Overview

ContextLite provides a RESTful HTTP API for document management, context assembly, and cluster operations. All endpoints support JSON request/response formats and include comprehensive workspace isolation and clustering features.

## Base URL

```
http://localhost:8080/api/v1
```

## Authentication

Currently, ContextLite uses simple token-based authentication via the `Authorization` header:

```http
Authorization: Bearer your-auth-token
```

Set the token in your configuration or via environment variable `CONTEXTLITE_AUTH_TOKEN`.

## Workspace Headers

All requests support workspace isolation via HTTP headers:

```http
X-Workspace-ID: mission-architect
X-Resource-Tier: high
X-Node-Preference: node-1
```

## Context Assembly

### POST /assemble

Assembles the most relevant context for a given query using SMT optimization.

**Request:**
```http
POST /api/v1/assemble
Content-Type: application/json
X-Workspace-ID: mission-architect

{
  "query": "How does user authentication work?",
  "max_tokens": 4000,
  "max_documents": 10,
  "use_smt": true,
  "use_cache": true,
  "workspace_path": "/path/to/project",
  "model_id": "gpt-4"
}
```

**Response:**
```json
{
  "context": "Combined context from selected documents...",
  "documents": [
    {
      "id": "doc123",
      "path": "/src/auth.go",
      "content": "Authentication implementation...",
      "language": "go",
      "utility_score": 0.95,
      "relevance_score": 0.92,
      "recency_score": 0.87,
      "inclusion_reason": "smt-optimal"
    }
  ],
  "total_tokens": 3847,
  "processing_time": "245ms",
  "cache_hit": false,
  "message": "Selected 8 documents using SMT optimization",
  "workspace_info": {
    "id": "mission-architect",
    "resource_tier": "high",
    "affinity_applied": true
  }
}
```

### POST /baseline-comparison

Compare SMT optimization against baseline heuristics.

**Request:**
```json
{
  "query": "authentication implementation",
  "max_tokens": 4000,
  "max_documents": 10,
  "workspace_path": "/path/to/project"
}
```

**Response:**
```json
{
  "smt_result": { /* ContextResult */ },
  "baseline_result": { /* ContextResult */ },
  "comparison": {
    "document_overlap": 0.73,
    "processing_time_ratio": 1.25,
    "utility_improvement": 0.18,
    "diversity_difference": 0.05
  }
}
```

## Document Management

### POST /documents

Add a new document to the knowledge base.

**Request:**
```json
{
  "id": "optional-custom-id",
  "content": "Document content here...",
  "path": "/src/auth.go",
  "language": "go",
  "metadata": {
    "author": "developer",
    "tags": ["authentication", "security"]
  },
  "workspace_id": "mission-architect",
  "resource_tier": "high",
  "project_tags": ["backend", "security"]
}
```

**Response:**
```json
{
  "id": "doc123",
  "created_at": "2025-01-20T10:30:00Z",
  "token_count": 1250,
  "quantum_score": 0.78,
  "workspace_id": "mission-architect",
  "status": "indexed"
}
```

### GET /documents/search

Search for documents using full-text search.

**Request:**
```http
GET /api/v1/documents/search?q=authentication&limit=20&workspace=mission-architect
```

**Response:**
```json
{
  "documents": [
    {
      "id": "doc123",
      "path": "/src/auth.go",
      "content": "Authentication implementation...",
      "language": "go",
      "relevance_score": 0.92,
      "workspace_id": "mission-architect"
    }
  ],
  "total_count": 45,
  "query_time": "12ms",
  "workspace_filtered": true
}
```

### GET /documents/{id}

Retrieve a specific document.

**Response:**
```json
{
  "id": "doc123",
  "content": "Full document content...",
  "path": "/src/auth.go",
  "language": "go",
  "created_at": "2025-01-20T10:30:00Z",
  "updated_at": "2025-01-20T15:45:00Z",
  "token_count": 1250,
  "metadata": {},
  "workspace_id": "mission-architect",
  "resource_tier": "high"
}
```

### DELETE /documents/{id}

Remove a document from the knowledge base.

**Response:**
```json
{
  "success": true,
  "message": "Document deleted successfully"
}
```

## Weight Management

### GET /weights

Get current workspace-specific feature weights.

**Request:**
```http
GET /api/v1/weights?workspace=/path/to/project
```

**Response:**
```json
{
  "workspace_path": "/path/to/project",
  "weights": {
    "relevance": 0.30,
    "recency": 0.20,
    "entanglement": 0.15,
    "prior": 0.15,
    "authority": 0.10,
    "specificity": 0.05,
    "uncertainty": 0.05
  },
  "last_updated": "2025-01-20T14:30:00Z",
  "calibration_samples": 127
}
```

### POST /weights/update

Update weights based on user feedback.

**Request:**
```json
{
  "workspace_path": "/path/to/project",
  "accepted_docs": ["doc123", "doc456"],
  "rejected_docs": ["doc789"],
  "query": "authentication implementation",
  "learning_rate": 0.1
}
```

**Response:**
```json
{
  "success": true,
  "updated_weights": {
    "relevance": 0.32,
    "recency": 0.18,
    "entanglement": 0.16,
    "prior": 0.14,
    "authority": 0.11,
    "specificity": 0.05,
    "uncertainty": 0.04
  },
  "improvement_score": 0.12
}
```

## Cluster Management

### GET /health

Get comprehensive system and cluster health information.

**Response:**
```json
{
  "status": "healthy",
  "timestamp": 1645123456,
  "version": "1.0.0",
  "node_id": "contextlite-node-1",
  "smt": {
    "solver": "Z3",
    "version": "4.12.0",
    "enabled": true,
    "policy": "SMT optimization selects document subsets to maximize utility while minimizing redundancy using constraint satisfaction"
  },
  "database": {
    "total_documents": 1247,
    "total_size_mb": 45.7,
    "last_vacuum": "2025-01-20T08:00:00Z"
  },
  "cluster": {
    "enabled": true,
    "node_id": "contextlite-node-1",
    "cluster_size": 3,
    "leader_node": "contextlite-node-1",
    "load_factor": 0.35,
    "discovery_method": "static",
    "load_balancing": "workspace_hash",
    "affinity_enabled": true,
    "sticky_sessions": true
  },
  "workspaces": {
    "total_workspaces": 5,
    "active_workspaces": 3,
    "workspaces": {
      "mission-architect": {
        "document_count": 247,
        "resource_tier": "high",
        "last_access": 1645123400,
        "access_pattern": "high-frequency",
        "active_requests": 2,
        "avg_response_time": 185.5
      }
    }
  },
  "features": {
    "cache_enabled": true,
    "fts_search": true,
    "quantum_scoring": true,
    "smt_optimization": true,
    "clustering": true,
    "workspace_isolation": true,
    "project_affinity": true
  }
}
```

### GET /health/cluster

Get cluster-specific health information.

**Response:**
```json
{
  "cluster_status": "healthy",
  "nodes": [
    {
      "id": "contextlite-node-1",
      "address": "192.168.1.100",
      "port": 8080,
      "status": "healthy",
      "load_factor": 0.35,
      "workspaces": ["mission-architect", "frontend"],
      "last_heartbeat": 1645123456
    },
    {
      "id": "contextlite-node-2", 
      "address": "192.168.1.101",
      "port": 8080,
      "status": "healthy",
      "load_factor": 0.42,
      "workspaces": ["backend", "api"],
      "last_heartbeat": 1645123455
    }
  ],
  "discovery": {
    "method": "static",
    "healthy_nodes": 2,
    "total_nodes": 3,
    "last_discovery": 1645123450
  },
  "load_balancing": {
    "strategy": "workspace_hash",
    "requests_per_minute": 1247,
    "error_rate": 0.002
  }
}
```

## RAG Integration Endpoints

### POST /rank

Rank documents for RAG applications (langchain/llamaindex integration).

**Request:**
```json
{
  "query": "user authentication patterns",
  "k": 10,
  "budget_ms": 500,
  "max_tokens": 4000,
  "use_cache": true
}
```

**Response:**
```json
{
  "items": [
    {
      "file": "/src/auth.go",
      "range": {
        "start": {"line": 45, "character": 0},
        "end": {"line": 78, "character": 42}
      },
      "snippet": "func AuthenticateUser(token string) (*User, error) {...",
      "score": 0.95,
      "why": "smt-optimal: high relevance + authority"
    }
  ],
  "p99_ms": 245
}
```

### POST /snippet

Get precise code snippets by file and line range.

**Request:**
```json
{
  "file": "/src/auth.go", 
  "start": {"line": 45, "character": 0},
  "end": {"line": 78, "character": 42}
}
```

**Response:**
```json
{
  "snippet": "func AuthenticateUser(token string) (*User, error) {\n    // Implementation...\n}"
}
```

## License and Trial Management

### GET /license/status

Get current license and trial status.

**Response:**
```json
{
  "tier": "trial",
  "status": "active",
  "trial_days_remaining": 27,
  "features_enabled": [
    "unlimited_workspaces",
    "advanced_smt",
    "7d_scoring", 
    "caching",
    "clustering"
  ],
  "purchase_url": "https://contextlite.com/purchase"
}
```

### GET /license/trial

Get detailed trial information.

**Response:**
```json
{
  "trial_active": true,
  "days_remaining": 27,
  "started_at": "2025-01-01T00:00:00Z",
  "expires_at": "2025-02-01T00:00:00Z",
  "usage": {
    "queries_today": 247,
    "documents_indexed": 1247,
    "workspaces_created": 5
  },
  "features_available": [
    "unlimited_workspaces",
    "advanced_smt",
    "7d_scoring",
    "caching", 
    "clustering"
  ],
  "purchase_url": "https://contextlite.com/purchase"
}
```

## Error Handling

All endpoints return consistent error responses:

```json
{
  "error": "Workspace resource limits exceeded",
  "code": "RESOURCE_LIMIT_EXCEEDED",
  "details": {
    "workspace_id": "mission-architect",
    "limit_type": "concurrent_requests",
    "current": 10,
    "maximum": 10
  },
  "timestamp": 1645123456
}
```

## Common HTTP Status Codes

- `200 OK` - Success
- `201 Created` - Resource created successfully  
- `400 Bad Request` - Invalid request format or parameters
- `401 Unauthorized` - Missing or invalid authentication
- `403 Forbidden` - Request not allowed (license/feature restrictions)
- `404 Not Found` - Resource not found
- `429 Too Many Requests` - Rate limit or resource limit exceeded
- `500 Internal Server Error` - Server error
- `503 Service Unavailable` - Service temporarily unavailable

## Workspace-Specific Routing

ContextLite supports multiple methods for workspace identification:

### 1. HTTP Headers (Recommended)
```http
X-Workspace-ID: mission-architect
X-Resource-Tier: high
X-Node-Preference: node-1
```

### 2. Query Parameters
```http
GET /api/v1/documents/search?workspace=mission-architect&q=auth
```

### 3. Path-based Routing
```http
POST /workspace/mission-architect/api/v1/assemble
```

### 4. Request Body
```json
{
  "query": "authentication",
  "workspace_path": "/projects/mission-architect"
}
```

## Performance Considerations

### Caching
- L1 cache: In-memory (30ms response time)
- L2 cache: SQLite-based (100ms response time)
- Cache headers: `Cache-Control`, `ETag` supported

### Rate Limiting
- Per-workspace limits configurable
- Global rate limiting available
- Respects `X-RateLimit-*` headers

### SMT Optimization
- Budget processing time with `budget_ms` parameter
- Fallback to heuristics if SMT timeout exceeded
- `use_smt=false` for faster heuristic-only processing

### Clustering Performance
- Workspace affinity reduces latency
- Sticky sessions maintain cache locality
- Load balancing distributes requests efficiently

## Examples

### TypeScript/JavaScript Client

```typescript
import fetch from 'node-fetch';

class ContextLiteClient {
  constructor(private baseUrl: string, private workspaceId: string) {}

  async assembleContext(query: string, options: AssembleOptions = {}) {
    const response = await fetch(`${this.baseUrl}/api/v1/assemble`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'X-Workspace-ID': this.workspaceId,
        'X-Resource-Tier': options.resourceTier || 'medium',
      },
      body: JSON.stringify({
        query,
        max_tokens: options.maxTokens || 4000,
        max_documents: options.maxDocuments || 10,
        use_smt: options.useSMT !== false,
        use_cache: options.useCache !== false,
      }),
    });

    if (!response.ok) {
      throw new Error(`ContextLite API error: ${response.status}`);
    }

    return response.json();
  }

  async addDocument(document: Document) {
    const response = await fetch(`${this.baseUrl}/api/v1/documents`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'X-Workspace-ID': this.workspaceId,
      },
      body: JSON.stringify(document),
    });

    return response.json();
  }
}
```

### Python Client

```python
import requests
import json

class ContextLiteClient:
    def __init__(self, base_url, workspace_id, auth_token=None):
        self.base_url = base_url
        self.workspace_id = workspace_id
        self.headers = {
            'Content-Type': 'application/json',
            'X-Workspace-ID': workspace_id,
        }
        if auth_token:
            self.headers['Authorization'] = f'Bearer {auth_token}'

    def assemble_context(self, query, max_tokens=4000, max_documents=10):
        payload = {
            'query': query,
            'max_tokens': max_tokens,
            'max_documents': max_documents,
            'use_smt': True,
            'use_cache': True,
        }
        
        response = requests.post(
            f'{self.base_url}/api/v1/assemble',
            headers=self.headers,
            json=payload,
        )
        
        response.raise_for_status()
        return response.json()

    def add_document(self, content, path, language='text'):
        document = {
            'content': content,
            'path': path,
            'language': language,
        }
        
        response = requests.post(
            f'{self.base_url}/api/v1/documents',
            headers=self.headers,
            json=document,
        )
        
        return response.json()
```

### cURL Examples

```bash
# Add document
curl -X POST http://localhost:8080/api/v1/documents \
  -H "Content-Type: application/json" \
  -H "X-Workspace-ID: mission-architect" \
  -d '{
    "content": "Authentication implementation using JWT tokens...",
    "path": "/src/auth.go",
    "language": "go"
  }'

# Assemble context  
curl -X POST http://localhost:8080/api/v1/assemble \
  -H "Content-Type: application/json" \
  -H "X-Workspace-ID: mission-architect" \
  -H "X-Resource-Tier: high" \
  -d '{
    "query": "How does JWT authentication work?",
    "max_tokens": 4000,
    "max_documents": 10,
    "use_smt": true
  }'

# Check cluster health
curl http://localhost:8080/health \
  -H "X-Workspace-ID: mission-architect"

# Search documents
curl "http://localhost:8080/api/v1/documents/search?q=authentication&limit=20" \
  -H "X-Workspace-ID: mission-architect"
```

This API provides comprehensive context assembly capabilities with advanced clustering, workspace isolation, and SMT optimization features for AI applications.