# Background Daemon Interval Research - Industry Standards

## 🔍 Research Findings: Production System Intervals

### **System Administration Standards**
- **systemd service health checks**: 10-30 seconds typical
- **Docker health checks**: 30 seconds default (Docker official)
- **Kubernetes pod probes**: 10 seconds default (can go as low as 1 second)
- **AWS ELB health checks**: 30 seconds default
- **Nginx health checks**: 5-10 seconds typical

### **Database Connection Pools**
- **PostgreSQL connection validation**: 30-300 seconds
- **MySQL connection timeout**: 28800 seconds (8 hours!) 
- **Redis connection idle timeout**: 0 (disabled) or 300+ seconds
- **MongoDB connection max idle**: 600 seconds (10 minutes)

### **Background Process Standards**
- **cron minimum interval**: 60 seconds (1 minute)
- **systemd timer minimum**: 1 second (but 60s+ recommended)
- **Log rotation daemons**: 3600 seconds (1 hour) to 86400 seconds (24 hours)
- **Package managers (apt, yum)**: Daily (86400s) or weekly
- **File system cleanup**: 300-900 seconds (5-15 minutes)

### **Port Management Specific Research**
- **Docker port mapping checks**: Only on container start/stop events
- **Kubernetes service discovery**: Event-driven (not polling)
- **systemd socket activation**: Event-driven (not polling)
- **nginx upstream health**: 10-30 seconds when enabled

### **Memory Management Findings**
- **Process scanning**: Can be expensive if done frequently
- **File I/O for registry**: Should be minimized
- **Cross-platform process detection**: Varies in cost by OS

## 🎯 Optimized Recommendations

### **For Port Registry (Our Use Case)**
Port management is typically **event-driven**, not time-based polling:

1. **Registry Updates**: Only when processes start/stop
2. **Health Checks**: Only when needed for allocation
3. **Cleanup**: Infrequent, maybe 10-15 minutes
4. **Process Detection**: On-demand only

### **Industry Best Practices for Lightweight Systems**
- **No background polling** unless absolutely necessary
- **Event-driven** architecture preferred
- **Lazy cleanup** - only clean when needed
- **Backoff strategies** - increase intervals if no activity

### **Recommended Intervals (Based on Industry)**
- **Audit Cleanup**: 10-15 minutes (600-900 seconds)
- **Health Checks**: On-demand only (no background polling)
- **Registry Writes**: Only on actual changes
- **Process Detection**: Only during allocation/release

### **Memory-Friendly Approach**
- **No persistent goroutines** if possible
- **Cleanup only when allocating** new ports
- **No continuous scanning** of processes
- **Minimal file I/O** - batch operations

## 🚨 Red Flags We Were Hitting
- **45 seconds health checks**: Too frequent for port management
- **3 minutes cleanup**: Too frequent for our use case
- **Continuous background processes**: Unnecessary for port coordination
- **Regular process scanning**: Expensive and unnecessary

## ✅ Better Architecture: Event-Driven
Instead of time-based polling, use:
1. **Cleanup on allocation** - clean stale entries when someone requests a port
2. **No background daemons** - everything on-demand
3. **Smart detection** - only check if processes are alive when needed
4. **Lazy cleanup** - only clean up when registry is accessed

This aligns with Docker, Kubernetes, and other modern systems that use event-driven port management rather than polling.
