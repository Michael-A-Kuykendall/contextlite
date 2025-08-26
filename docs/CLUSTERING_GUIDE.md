# ContextLite Clustering Guide

## Overview

ContextLite supports clustering for managing multiple projects and workspaces across local development environments. This guide covers configuration, deployment patterns, and best practices for clustering ContextLite instances.

## Architecture Approaches

### 1. Mono-Instance Multi-Project (Recommended for Local Development)

Single ContextLite instance serving multiple projects with workspace isolation:

```
┌─────────────────────────────────────────────────┐
│             ContextLite Instance                │
│                 (Port 8080)                     │
├─────────────────────────────────────────────────┤
│  Workspace: mission-architect                   │
│  • High priority, 512MB RAM                     │
│  • Dedicated document collections               │
│  • Sticky sessions enabled                      │
├─────────────────────────────────────────────────┤
│  Workspace: code-assistant                      │
│  • Medium priority, 256MB RAM                   │
│  • General purpose documents                    │
│  • Load balanced requests                       │
├─────────────────────────────────────────────────┤
│  Workspace: archive                            │
│  • Low priority, 128MB RAM                      │
│  • Long-term document storage                   │
│  • Background processing                        │
└─────────────────────────────────────────────────┘
```

### 2. Distributed Multi-Instance (For High-Load Environments)

Multiple ContextLite instances with load balancing and affinity routing:

```
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│  ContextLite    │    │  ContextLite    │    │  ContextLite    │
│  Node 1:8080    │    │  Node 2:8081    │    │  Node 3:8082    │
│                 │    │                 │    │                 │
│ mission-architect│    │ code-assistant  │    │    archive      │
│ (high priority) │    │ (medium priority)│    │ (low priority)  │
└─────────────────┘    └─────────────────┘    └─────────────────┘
         │                       │                       │
         └───────────────────────┼───────────────────────┘
                                 │
                    ┌─────────────────────┐
                    │   Load Balancer     │
                    │   (workspace hash)  │
                    └─────────────────────┘
```

## Configuration

### Basic Cluster Configuration

Create `configs/cluster.yaml`:

```yaml
cluster:
  enabled: true
  node_id: "contextlite-node-1"
  
  discovery:
    method: "static"
    endpoints:
      - "localhost:8080"
      - "localhost:8081"
      - "localhost:8082"
    
  affinity:
    workspace_routing: true
    sticky_sessions: true
    default_tier: "medium"
    rules:
      "mission-architect":
        preferred_nodes: ["contextlite-node-1"]
        resource_tier: "high"
        sticky_session: true
      "archive":
        resource_tier: "low"
        avoid_nodes: ["contextlite-node-1"]
  
  load_balancing:
    strategy: "workspace_hash"
    health_check_interval: 30
    max_load_factor: 0.85
    
  resource_limits:
    "mission-architect":
      max_concurrent_requests: 10
      max_tokens_per_minute: 50000
      max_memory_mb: 512
      priority: 8
    "development":
      max_concurrent_requests: 5
      max_tokens_per_minute: 20000
      max_memory_mb: 256
      priority: 5
```

### Environment Variables

```bash
# Basic configuration
export CONTEXTLITE_PORT=8080
export CONTEXTLITE_HOST=0.0.0.0
export CONTEXTLITE_DB_PATH=./data/contextlite.db

# Cluster configuration
export CONTEXTLITE_CLUSTER_ENABLED=true
export CONTEXTLITE_NODE_ID=contextlite-node-1
export CONTEXTLITE_DISCOVERY_METHOD=static
```

## Deployment Patterns

### Local Development Setup

#### Single Instance Multi-Project

```bash
# Start ContextLite with clustering enabled
./contextlite --config configs/cluster.yaml --port 8080

# Connect from different projects
curl -H "X-Workspace-ID: mission-architect" \
     -X POST http://localhost:8080/api/v1/assemble \
     -d '{"query": "AI enforcement patterns"}'

curl -H "X-Workspace-ID: code-assistant" \
     -X POST http://localhost:8080/api/v1/assemble \
     -d '{"query": "React component patterns"}'
```

#### Multi-Instance Setup

```bash
# Start multiple instances
./contextlite --config configs/cluster.yaml --port 8080 --node-id node-1 &
./contextlite --config configs/cluster.yaml --port 8081 --node-id node-2 &
./contextlite --config configs/cluster.yaml --port 8082 --node-id node-3 &

# Use automatic port discovery in Mission Architect
# ContextLiteClient will find available instances automatically
```

### Docker Deployment

#### Docker Compose for Multi-Instance

```yaml
# docker-compose.cluster.yml
version: '3.8'

services:
  contextlite-node-1:
    image: contextlite:latest
    ports:
      - "8080:8080"
    environment:
      - CONTEXTLITE_NODE_ID=node-1
      - CONTEXTLITE_CLUSTER_ENABLED=true
    volumes:
      - ./data/node-1:/app/data
      - ./configs:/app/configs
    command: ["--config", "configs/cluster.yaml", "--port", "8080"]

  contextlite-node-2:
    image: contextlite:latest
    ports:
      - "8081:8080"
    environment:
      - CONTEXTLITE_NODE_ID=node-2
      - CONTEXTLITE_CLUSTER_ENABLED=true
    volumes:
      - ./data/node-2:/app/data
      - ./configs:/app/configs
    command: ["--config", "configs/cluster.yaml", "--port", "8080"]

  contextlite-node-3:
    image: contextlite:latest
    ports:
      - "8082:8080"
    environment:
      - CONTEXTLITE_NODE_ID=node-3
      - CONTEXTLITE_CLUSTER_ENABLED=true
    volumes:
      - ./data/node-3:/app/data
      - ./configs:/app/configs
    command: ["--config", "configs/cluster.yaml", "--port", "8080"]

  nginx-lb:
    image: nginx:alpine
    ports:
      - "8000:80"
    volumes:
      - ./nginx.conf:/etc/nginx/nginx.conf
    depends_on:
      - contextlite-node-1
      - contextlite-node-2
      - contextlite-node-3
```

#### Nginx Load Balancer Configuration

```nginx
# nginx.conf
upstream contextlite_cluster {
    hash $http_x_workspace_id consistent;
    
    server contextlite-node-1:8080 weight=3;  # High-priority node
    server contextlite-node-2:8080 weight=2;  # Medium-priority node  
    server contextlite-node-3:8080 weight=1;  # Archive node
}

server {
    listen 80;
    
    location / {
        proxy_pass http://contextlite_cluster;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
    }
    
    location /health {
        # Health check endpoint for all nodes
        proxy_pass http://contextlite_cluster;
    }
}
```

## Workspace Management

### Workspace Identification

ContextLite supports multiple methods for workspace identification:

1. **HTTP Header**: `X-Workspace-ID: mission-architect`
2. **Query Parameter**: `?workspace=mission-architect`
3. **Request Path**: `/workspace/mission-architect/api/v1/assemble`
4. **User-Agent Detection**: Automatic detection from client identifier
5. **Request Body**: Extracted from `workspace_path` field

### Resource Isolation

Each workspace gets isolated resources:

```yaml
resource_limits:
  "mission-architect":
    max_concurrent_requests: 10    # Concurrent API calls
    max_tokens_per_minute: 50000   # Rate limiting
    max_documents_per_query: 20    # Context window size
    max_memory_mb: 512             # Memory allocation
    max_storage_mb: 2048           # Disk usage
    priority: 8                    # Scheduling priority (1-10)
```

### Affinity Rules

Route workspaces to specific nodes:

```yaml
affinity:
  workspace_routing: true
  sticky_sessions: true
  rules:
    "mission-architect":
      preferred_nodes: ["node-1", "node-2"]  # Prefer high-performance nodes
      avoid_nodes: ["node-3"]                # Avoid archive node
      resource_tier: "high"                  # High priority scheduling
      locality: "same-rack"                  # Prefer co-located nodes
```

## Monitoring and Health Checks

### Cluster Health Endpoint

```bash
curl http://localhost:8080/health
```

Response includes cluster-wide information:

```json
{
  "status": "healthy",
  "node_id": "contextlite-node-1",
  "cluster": {
    "enabled": true,
    "node_id": "contextlite-node-1",
    "cluster_size": 3,
    "leader_node": "contextlite-node-1",
    "load_factor": 0.35,
    "discovery_method": "static",
    "load_balancing": "workspace_hash"
  },
  "workspaces": {
    "total_workspaces": 3,
    "active_workspaces": 2,
    "workspaces": {
      "mission-architect": {
        "document_count": 150,
        "resource_tier": "high",
        "last_access": 1635724800,
        "access_pattern": "high-frequency"
      }
    }
  }
}
```

### Workspace-Specific Health

```bash
curl -H "X-Workspace-ID: mission-architect" http://localhost:8080/health
```

### Metrics Collection

Monitor key metrics per workspace:
- **Active Requests**: Current concurrent requests
- **Query Count**: Total queries processed  
- **Response Time**: Average response latency
- **Memory Usage**: Current memory consumption
- **Document Count**: Documents indexed per workspace
- **Access Pattern**: Usage classification (high-frequency, normal, archive)

## Load Balancing Strategies

### 1. Workspace Hash (Recommended)

Routes requests based on workspace ID hash for consistent routing:

```yaml
load_balancing:
  strategy: "workspace_hash"
```

**Benefits**:
- Consistent routing for workspace affinity
- Automatic load distribution
- Cache locality for workspace data

### 2. Resource-Based

Routes based on current node load and resource availability:

```yaml
load_balancing:
  strategy: "resource_based"
  max_load_factor: 0.85
```

**Benefits**:
- Dynamic load balancing
- Prevents resource exhaustion
- Adapts to varying workloads

### 3. Least Connections

Routes to node with fewest active connections:

```yaml
load_balancing:
  strategy: "least_connections"
```

**Benefits**:
- Even request distribution
- Good for uniform request types
- Simple implementation

## Best Practices

### Local Development

1. **Use Mono-Instance**: Single ContextLite with workspace isolation
2. **Port Range**: Use automatic port discovery (8080-8090)
3. **Resource Limits**: Set conservative limits for development
4. **Sticky Sessions**: Enable for consistent workspace experience

```yaml
# Development configuration
cluster:
  enabled: true
  affinity:
    workspace_routing: true
    sticky_sessions: true
  resource_limits:
    default:
      max_concurrent_requests: 3
      max_tokens_per_minute: 10000
      max_memory_mb: 128
```

### Production Environment

1. **Multi-Instance**: Deploy 3+ nodes for high availability
2. **Resource Tiers**: Use tiered resource allocation
3. **Health Monitoring**: Implement comprehensive health checks
4. **Load Balancing**: Use workspace-hash strategy

```yaml
# Production configuration
cluster:
  enabled: true
  discovery:
    method: "consul"  # Use service discovery
    endpoints: ["consul:8500"]
  load_balancing:
    strategy: "workspace_hash"
    health_check_interval: 30
    enable_circuit_breaker: true
  resource_limits:
    production:
      max_concurrent_requests: 50
      max_tokens_per_minute: 100000
      max_memory_mb: 2048
```

### Performance Optimization

1. **Cache Strategy**: Enable L1/L2 caching per workspace
2. **SMT Optimization**: Use appropriate solver timeouts per tier
3. **Document Partitioning**: Distribute documents based on access patterns
4. **Connection Pooling**: Reuse connections between cluster nodes

## Troubleshooting

### Common Issues

#### 1. Port Conflicts

```bash
# Check port availability
netstat -tulpn | grep :8080

# Use automatic port discovery
export CONTEXTLITE_AUTO_PORT=true
```

#### 2. Workspace Routing Issues

```bash
# Verify workspace header
curl -v -H "X-Workspace-ID: test" http://localhost:8080/health

# Check affinity rules
grep -A 10 "affinity:" configs/cluster.yaml
```

#### 3. Resource Limit Violations

```bash
# Check current limits
curl http://localhost:8080/health | jq '.workspaces'

# Monitor active requests
watch -n 1 'curl -s http://localhost:8080/health | jq ".workspaces.workspaces.\"mission-architect\".active_requests"'
```

#### 4. Discovery Issues

```bash
# Verify node discovery
curl http://localhost:8080/health | jq '.cluster'

# Test direct node access  
curl http://localhost:8081/health
curl http://localhost:8082/health
```

### Debug Commands

```bash
# Enable debug logging
export CONTEXTLITE_LOG_LEVEL=debug

# Check cluster configuration
./contextlite --config configs/cluster.yaml --validate

# Test workspace isolation
curl -H "X-Workspace-ID: test1" -X POST localhost:8080/api/v1/assemble -d '{"query":"test"}'
curl -H "X-Workspace-ID: test2" -X POST localhost:8080/api/v1/assemble -d '{"query":"test"}'
```

## Integration Examples

### Mission Architect Integration

```typescript
// ContextLiteClient with clustering support
const client = new ContextLiteClient({
  autoDiscover: true,
  portRange: [8080, 8090],
  workspaceId: 'mission-architect',
  affinityRules: {
    preferredNodes: ['node-1'],
    resourceTier: 'high',
    stickySession: true
  }
});

// Automatic failover and load balancing
const result = await client.search('AI enforcement patterns', {
  maxResults: 10,
  useWorkspaceAffinity: true
});
```

### Direct API Usage

```bash
# High-priority workspace
curl -H "X-Workspace-ID: mission-architect" \
     -H "X-Resource-Tier: high" \
     -X POST http://localhost:8080/api/v1/assemble \
     -d '{
       "query": "AI safety enforcement patterns",
       "max_tokens": 8000,
       "max_documents": 15,
       "workspace_path": "/projects/mission-architect"
     }'

# Archive workspace  
curl -H "X-Workspace-ID: archive" \
     -H "X-Resource-Tier: low" \
     -X POST http://localhost:8080/api/v1/assemble \
     -d '{
       "query": "historical documentation",
       "max_tokens": 2000,
       "max_documents": 5
     }'
```

## Future Enhancements

1. **Service Discovery**: Full Consul/etcd integration
2. **Auto-Scaling**: Dynamic node provisioning
3. **Cross-Region**: Multi-datacenter clustering
4. **Advanced Metrics**: Prometheus integration
5. **Security**: mTLS between cluster nodes
6. **Storage Replication**: Document synchronization across nodes

---

This clustering implementation provides a solid foundation for scaling ContextLite across multiple projects and environments while maintaining workspace isolation and resource management.