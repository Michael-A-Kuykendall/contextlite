# ContextLite Port Management & Multi-Project Performance Tasks

## 🔧 CRITICAL: Per-Project Port Range Expansion

### **Current Limitation Analysis**
- **Current Range**: 8080-8090 (Only 10 ports available)
- **Real-World Need**: 50+ active projects simultaneously
- **Performance Impact**: Port conflicts causing service failures
- **User Experience**: Frustrating "port already in use" errors

### **Immediate Fixes Required**

#### 1. **Expand Port Range Configuration** ✅ COMPLETED
- [x] Updated per-project-setup.yaml to use 8080-8200 (120 ports)
- [x] Added structured endpoint ranges for better organization
- [x] Configured dynamic port discovery algorithm

#### 2. **Port Management Service Enhancement**
- [ ] Implement intelligent port allocation algorithm
- [ ] Add port conflict detection and resolution
- [ ] Create port usage monitoring dashboard
- [ ] Build automatic port cleanup for dead processes

#### 3. **Multi-Project Performance Optimization**
- [ ] Design resource sharing between project instances
- [ ] Implement connection pooling for common resources
- [ ] Add project-specific memory management
- [ ] Create smart background process management

### **Technical Implementation Tasks**

#### A. **Enhanced Port Discovery System**
```yaml
discovery:
  method: "intelligent_auto"
  port_ranges:
    primary: [8080, 8120]      # 40 ports for active projects
    secondary: [8150, 8200]    # 50 ports for overflow
    development: [8300, 8350]  # 50 ports for dev/testing
  allocation_strategy: "round_robin_with_affinity"
  cleanup_inactive_after: "30 minutes"
```

#### B. **Resource Management Improvements**
- [ ] Per-project memory limits with intelligent sharing
- [ ] Database connection pooling across projects
- [ ] Shared cache for common code patterns
- [ ] Background indexing coordination

#### C. **Performance Monitoring**
- [ ] Real-time port usage dashboard
- [ ] Project resource consumption metrics
- [ ] Performance bottleneck identification
- [ ] Automatic scaling recommendations

### **Advanced Multi-Project Architecture**

#### 1. **Project Instance Manager**
- [ ] Master service to coordinate all project instances
- [ ] Health checking and automatic restart
- [ ] Load balancing between project instances
- [ ] Inter-project communication bus

#### 2. **Resource Sharing Optimization**
- [ ] Shared SMT solver instances for better performance
- [ ] Common vector embedding cache
- [ ] Shared file system monitoring
- [ ] Centralized license/trial management

#### 3. **Developer Experience Improvements**
- [ ] VS Code extension auto-detects all project instances
- [ ] Single configuration for multiple projects
- [ ] Project switching without restart
- [ ] Unified logging and debugging

### **Configuration Examples**

#### Enhanced per-project-setup.yaml Structure:
```yaml
cluster:
  enabled: true
  manager_port: 8079  # Master coordinator service
  
  # Multi-project port allocation
  discovery:
    allocation_strategy: "smart_distribute"
    port_ranges:
      - name: "primary_development"
        start: 8080
        end: 8120
        max_projects: 40
      - name: "testing_overflow" 
        start: 8150
        end: 8200
        max_projects: 50
      - name: "experimental"
        start: 8300
        end: 8350
        max_projects: 50
    
  # Resource sharing between projects
  shared_resources:
    smt_solver_pool: true
    embedding_cache: true
    file_watcher_service: true
    license_manager: true
```

### **Implementation Priority**

#### Phase 1: Critical Fixes (This Week)
- [x] Expand port range configuration
- [ ] Implement basic port conflict detection
- [ ] Test with 20+ simultaneous projects
- [ ] Document new configuration options

#### Phase 2: Performance Optimization (Next 2 Weeks)
- [ ] Build project instance manager service
- [ ] Implement resource sharing
- [ ] Create monitoring dashboard
- [ ] Performance testing with 50+ projects

#### Phase 3: Advanced Features (Next Month)
- [ ] Intelligent load balancing
- [ ] Auto-scaling based on resource usage
- [ ] Advanced project lifecycle management
- [ ] Integration with Docker/containers

### **Success Criteria**
- [ ] Support 100+ simultaneous projects without conflicts
- [ ] Sub-second project switching/discovery
- [ ] < 5% resource overhead per additional project
- [ ] Zero "port already in use" errors
- [ ] Seamless VS Code Copilot integration across all projects

### **Testing Scenarios**
1. **Heavy Load Test**: 50+ projects active simultaneously
2. **Rapid Switching**: Frequent project changes in VS Code
3. **Resource Exhaustion**: Test behavior at port/memory limits
4. **Crash Recovery**: Automatic cleanup of dead instances
5. **Cross-Project Isolation**: Ensure no data leakage

**Priority**: 🚨 **URGENT** - Performance bottleneck affecting developer productivity
**Impact**: High - Enables professional development workflows with many projects
**Timeline**: Phase 1 complete this week, Phase 2 within 2 weeks
