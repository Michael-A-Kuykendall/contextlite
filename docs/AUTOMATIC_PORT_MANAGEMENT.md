# Automatic Port Management

> **Eliminate port configuration drift with automatic discovery and failover**

ContextLite v1.1+ includes comprehensive automatic port management that eliminates the need for hardcoded port numbers and enables seamless concurrent instance management.

## 🚀 Quick Start

### Basic Auto-Discovery
```go
// Instead of hardcoding ports
client := contextlite.New("http://localhost:8080") // ❌ Old way

// Use automatic discovery
client := contextlite.NewAutoDiscovery() // ✅ New way
if err := client.Discover(); err != nil {
    log.Fatal("No ContextLite instances found")
}
// Client automatically connects to healthy instance
```

### Multiple Instance Discovery
```go
instances := client.DiscoverAll()
fmt.Printf("Found %d ContextLite instances\n", len(instances))
for _, instance := range instances {
    fmt.Printf("Port %d: %s\n", instance.Port, instance.Status)
}
```

## 🎯 Problem Solved: Port Configuration Drift

### The Old Problem
```bash
# Developer 1
./contextlite --config dev1.yaml  # Uses port 8080

# Developer 2 (later)
./contextlite --config dev2.yaml  # Port 8080 conflict!
# Error: "bind: address already in use"

# Application code
client := contextlite.New("http://localhost:8080") // Which instance?
```

### The New Solution
```bash
# Developer 1
./contextlite --config dev1.yaml  # Auto-allocates port 8080

# Developer 2 (concurrent)
./contextlite --config dev2.yaml  # Auto-allocates port 8081

# Application code
client := contextlite.NewAutoDiscovery()
client.Discover() // Finds both instances, uses healthiest one
```

## 🔧 Implementation Patterns

### Pattern 1: Single Instance Auto-Discovery
Perfect for simple applications that need one ContextLite instance:

```go
func connectToContextLite() *contextlite.Client {
    client := contextlite.NewAutoDiscovery()
    
    if err := client.Discover(); err != nil {
        // Fallback: start ContextLite if none found
        if err := startContextLiteInstance(); err != nil {
            log.Fatal("Failed to start ContextLite:", err)
        }
        
        // Retry discovery
        if err := client.Discover(); err != nil {
            log.Fatal("Failed to connect after starting ContextLite:", err)
        }
    }
    
    fmt.Printf("✅ Connected to ContextLite on port %d\n", client.GetPort())
    return client
}
```

### Pattern 2: Multi-Instance Load Balancing
For high-performance applications that need multiple instances:

```go
func setupLoadBalancedContextLite() *contextlite.LoadBalancer {
    // Discover all instances
    instances, err := contextlite.DiscoverAll()
    if err != nil {
        log.Fatal("Discovery failed:", err)
    }
    
    if len(instances) == 0 {
        // Start multiple instances if none found
        for i := 0; i < 3; i++ {
            go startContextLiteInstance(fmt.Sprintf("workspace-%d", i+1))
        }
        
        // Wait for instances to start
        time.Sleep(5 * time.Second)
        
        // Re-discover
        instances, _ = contextlite.DiscoverAll()
    }
    
    return contextlite.NewLoadBalancer(instances)
}
```

### Pattern 3: Workspace-Specific Instances
For development environments with isolated workspaces:

```go
type WorkspaceManager struct {
    clients map[string]*contextlite.Client
}

func (w *WorkspaceManager) GetClient(workspace string) *contextlite.Client {
    if client, exists := w.clients[workspace]; exists {
        if client.IsHealthy() {
            return client
        }
    }
    
    // Auto-discover instance for this workspace
    client := contextlite.NewAutoDiscovery()
    client.SetWorkspaceFilter(workspace)
    
    if err := client.Discover(); err != nil {
        // Start workspace-specific instance
        startWorkspaceInstance(workspace)
        client.Discover() // Retry
    }
    
    w.clients[workspace] = client
    return client
}
```

### Pattern 4: Environment-Specific Configuration
```go
func getContextLiteClient() *contextlite.Client {
    switch os.Getenv("ENV") {
    case "development":
        // Local auto-discovery (ports 8080-8090)
        client := contextlite.NewAutoDiscovery()
        client.SetPortRange(8080, 8090)
        client.Discover()
        return client
        
    case "staging":
        // Staging cluster (ports 9080-9090)
        client := contextlite.NewAutoDiscovery()
        client.SetPortRange(9080, 9090)
        client.Discover()
        return client
        
    case "production":
        // Production load-balanced cluster
        return contextlite.NewClusterClient(os.Getenv("CONTEXTLITE_CLUSTER_URL"))
        
    default:
        log.Fatal("Unknown environment:", os.Getenv("ENV"))
    }
}
```

## 🔄 Automatic Failover

The auto-discovery system includes built-in failover:

```go
client := contextlite.NewAutoDiscovery()
client.Discover()

// This query will automatically failover if the primary instance fails
result, err := client.Query("your query", 10)
if err != nil {
    // All instances failed
    log.Printf("All ContextLite instances unavailable: %v", err)
} else {
    fmt.Printf("✅ Query successful on port %d\n", client.GetActivePort())
}
```

### Health Monitoring
```go
// Enable continuous health monitoring
client.EnableHealthMonitoring(30 * time.Second) // Check every 30s

// Register health change callbacks
client.OnHealthChange(func(port int, healthy bool) {
    if healthy {
        fmt.Printf("✅ Instance %d recovered\n", port)
    } else {
        fmt.Printf("❌ Instance %d unhealthy, initiating failover\n", port)
    }
})
```

## 🏗️ Integration Examples

### With Popular Frameworks

#### **Gin Web Framework**
```go
func main() {
    // Auto-discover ContextLite
    contextClient := contextlite.NewAutoDiscovery()
    contextClient.Discover()
    
    r := gin.Default()
    r.POST("/api/search", func(c *gin.Context) {
        query := c.PostForm("query")
        
        // Automatic failover included
        results, err := contextClient.Query(query, 10)
        if err != nil {
            c.JSON(500, gin.H{"error": "Context service unavailable"})
            return
        }
        
        c.JSON(200, results)
    })
    
    r.Run(":3000")
}
```

#### **gRPC Service**
```go
type SearchService struct {
    contextClient *contextlite.Client
    pb.UnimplementedSearchServiceServer
}

func NewSearchService() *SearchService {
    client := contextlite.NewAutoDiscovery()
    if err := client.Discover(); err != nil {
        log.Fatal("Failed to discover ContextLite:", err)
    }
    
    return &SearchService{contextClient: client}
}

func (s *SearchService) Search(ctx context.Context, req *pb.SearchRequest) (*pb.SearchResponse, error) {
    // Automatic port management and failover
    results, err := s.contextClient.Query(req.Query, int(req.MaxResults))
    if err != nil {
        return nil, status.Errorf(codes.Unavailable, "Context service error: %v", err)
    }
    
    return convertResults(results), nil
}
```

#### **CLI Applications**
```go
func main() {
    app := &cli.App{
        Name: "myapp",
        Before: func(c *cli.Context) error {
            // Auto-discover ContextLite before any command
            client := contextlite.NewAutoDiscovery()
            if err := client.Discover(); err != nil {
                return fmt.Errorf("ContextLite not available: %w", err)
            }
            
            c.App.Metadata["contextlite"] = client
            return nil
        },
        Commands: []*cli.Command{
            {
                Name: "search",
                Action: func(c *cli.Context) error {
                    client := c.App.Metadata["contextlite"].(*contextlite.Client)
                    results, err := client.Query(c.Args().First(), 5)
                    // ... handle results
                    return nil
                },
            },
        },
    }
    
    app.Run(os.Args)
}
```

## 📊 Monitoring and Observability

### Metrics Collection
```go
client := contextlite.NewAutoDiscovery()
client.Discover()

// Get discovery metrics
metrics := client.GetDiscoveryMetrics()
fmt.Printf("Instances discovered: %d\n", metrics.InstancesFound)
fmt.Printf("Active failovers: %d\n", metrics.FailoverCount)
fmt.Printf("Average response time: %v\n", metrics.AvgResponseTime)
```

### Logging Integration
```go
import "github.com/sirupsen/logrus"

logger := logrus.New()
client := contextlite.NewAutoDiscovery()
client.SetLogger(logger)

client.Discover() // Logs discovery process
```

### Prometheus Metrics
```go
import "github.com/prometheus/client_golang/prometheus"

// Register ContextLite metrics
contextliteMetrics := contextlite.NewPrometheusMetrics()
prometheus.MustRegister(contextliteMetrics)

client := contextlite.NewAutoDiscovery()
client.SetMetricsCollector(contextliteMetrics)
```

## ⚙️ Configuration

### Environment Variables
```bash
# Port range for discovery
export CONTEXTLITE_PORT_MIN=8080
export CONTEXTLITE_PORT_MAX=8090

# Discovery timeout
export CONTEXTLITE_DISCOVERY_TIMEOUT=10s

# Health check interval
export CONTEXTLITE_HEALTH_INTERVAL=30s

# Enable debug logging
export CONTEXTLITE_DEBUG=true
```

### Programmatic Configuration
```go
config := &contextlite.DiscoveryConfig{
    PortRange:      contextlite.PortRange{Min: 8080, Max: 8090},
    DiscoveryTimeout: 10 * time.Second,
    HealthInterval:  30 * time.Second,
    MaxRetries:      3,
    RetryBackoff:    time.Second,
}

client := contextlite.NewAutoDiscoveryWithConfig(config)
```

## 🧪 Testing

### Unit Tests
```go
func TestAutoDiscovery(t *testing.T) {
    // Start test ContextLite instance
    testInstance := contextlite.NewTestInstance(t)
    defer testInstance.Close()
    
    // Test auto-discovery
    client := contextlite.NewAutoDiscovery()
    err := client.Discover()
    
    assert.NoError(t, err)
    assert.Equal(t, testInstance.Port(), client.GetPort())
}
```

### Integration Tests
```go
func TestFailover(t *testing.T) {
    // Start multiple test instances
    instance1 := contextlite.NewTestInstance(t)
    instance2 := contextlite.NewTestInstance(t)
    defer instance1.Close()
    defer instance2.Close()
    
    client := contextlite.NewAutoDiscovery()
    client.Discover()
    
    initialPort := client.GetPort()
    
    // Stop primary instance
    if initialPort == instance1.Port() {
        instance1.Stop()
    } else {
        instance2.Stop()
    }
    
    // Test failover
    _, err := client.Query("test query", 1)
    assert.NoError(t, err)
    assert.NotEqual(t, initialPort, client.GetPort())
}
```

## 🚀 Migration Guide

### From Fixed Ports to Auto-Discovery

#### Before (Fixed Port)
```go
client := contextlite.New("http://localhost:8080")
```

#### After (Auto-Discovery)
```go
client := contextlite.NewAutoDiscovery()
if err := client.Discover(); err != nil {
    log.Fatal("ContextLite discovery failed:", err)
}
```

### Gradual Migration
You can migrate gradually by supporting both approaches:

```go
func createContextLiteClient() *contextlite.Client {
    if url := os.Getenv("CONTEXTLITE_URL"); url != "" {
        // Legacy mode: use fixed URL
        return contextlite.New(url)
    }
    
    // New mode: auto-discovery
    client := contextlite.NewAutoDiscovery()
    if err := client.Discover(); err != nil {
        log.Fatal("ContextLite discovery failed:", err)
    }
    return client
}
```

## 🛡️ Production Considerations

### Security
- Auto-discovery only works on localhost by default
- Use authentication tokens for production deployments
- Configure firewall rules for production cluster discovery

### Performance
- Discovery adds ~100ms startup time
- Health checks use minimal bandwidth (~1KB every 30s)
- Failover typically completes in <500ms

### Monitoring
- Monitor instance discovery success rates
- Alert on repeated failover events
- Track response time degradation during failover

## 🔧 Troubleshooting

### Common Issues

#### "No instances found"
```bash
# Check if ContextLite is running
ps aux | grep contextlite

# Check port availability
netstat -tlnp | grep 808

# Test manual connection
curl http://localhost:8080/health
```

#### "Discovery timeout"
```go
// Increase discovery timeout
config := &contextlite.DiscoveryConfig{
    DiscoveryTimeout: 30 * time.Second,
}
client := contextlite.NewAutoDiscoveryWithConfig(config)
```

#### "Frequent failovers"
```bash
# Check instance health
curl http://localhost:8080/health
curl http://localhost:8081/health

# Check system resources
top
df -h

# Check ContextLite logs
tail -f contextlite.log
```

## 📈 Future Roadmap

- **Service Discovery Integration**: Consul, etcd, Kubernetes
- **Advanced Load Balancing**: Weighted round-robin, least connections
- **Circuit Breaker Pattern**: Automatic instance isolation
- **Cross-Machine Discovery**: Docker, Kubernetes cluster support
- **Performance Metrics**: Detailed latency and throughput tracking

---

## Summary

Automatic port management in ContextLite eliminates configuration drift and enables:

✅ **Zero-configuration setup** - No hardcoded ports needed  
✅ **Concurrent development** - Multiple instances without conflicts  
✅ **Automatic failover** - Built-in redundancy and health monitoring  
✅ **Production ready** - Suitable for high-availability deployments  
✅ **Easy migration** - Backward compatible with existing applications  

Get started today by updating your ContextLite integration to use `NewAutoDiscovery()`!