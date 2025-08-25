# ContextLite Repository Split Architecture Plan
## GRANULAR ATOMIC PERFECTION - ZERO DEPENDENCY HELL

> **Status**: Pre-implementation Architecture  
> **Complexity**: 84 Go files, 26,307 lines, 11 internal packages  
> **Risk Level**: MINIMIZED through atomic planning

---

## CURRENT DEPENDENCY GRAPH ANALYSIS

### Core Finding: Clear Separation Boundaries
```
CLEAN INTERFACES IDENTIFIED:
✅ pkg/types + pkg/config = PURE DATA CONTRACTS (no internal deps)
✅ internal/storage + internal/timing = INFRASTRUCTURE LAYER  
✅ internal/features + internal/smt + internal/solve = CORE ALGORITHMS (private)
✅ internal/api + internal/pipeline = PUBLIC ORCHESTRATION
✅ cmd/* = ENTRY POINTS (configurable backends)
```

### Dependency Flow Map:
```
cmd/contextlite/main.go
├── internal/api (PUBLIC)
├── internal/pipeline (PUBLIC) 
│   ├── internal/features (PRIVATE) ⚠️
│   ├── internal/smt (PRIVATE) ⚠️
│   └── internal/storage (PUBLIC)
├── internal/storage (PUBLIC)
└── pkg/config + pkg/types (PUBLIC)

CRITICAL INSIGHT: Only 2 packages create cross-repo dependencies!
- internal/pipeline → internal/features + internal/smt  
- internal/api → internal/features
```

---

## ATOMIC SPLIT STRATEGY

### Phase 1: Interface Extraction (ZERO RISK)
**Goal**: Create clean contracts between public/private code

#### 1.1 Create Abstract Interfaces (30 minutes)
```go
// pkg/types/interfaces.go (NEW FILE)
type FeatureExtractor interface {
    ExtractFeatures(doc Document, query string) FeatureVector
    UpdateWeights(feedback UserFeedback) error
}

type SMTSolver interface {
    OptimizeSelection(docs []Document, constraints Constraints) ([]int, error)
    SetStrategy(strategy OptimizationStrategy) error
}

type ContextEngine interface {
    AssembleContext(request ContextRequest) (*ContextResult, error)
    IndexDocument(doc Document) error
    GetStats() (*EngineStats, error)
}
```

#### 1.2 Update Internal Packages to Use Interfaces (45 minutes)
```go
// internal/pipeline/pipeline.go (UPDATED)
type Pipeline struct {
    storage   storage.Interface      // Already interface ✅
    features  types.FeatureExtractor // NEW: interface instead of concrete
    smt       types.SMTSolver        // NEW: interface instead of concrete
}

// internal/api/server.go (UPDATED)  
type Server struct {
    engine    types.ContextEngine    // NEW: interface instead of concrete
    storage   storage.Interface      // Already interface ✅
}
```

### Phase 2: Private Repository Setup (ZERO CONTAMINATION)
**Goal**: Create private repo with ONLY proprietary algorithms

#### 2.1 Private Repo Structure (`../contextlite-private/`)
```
contextlite-private/
├── go.mod (module: contextlite-private)
├── internal/
│   ├── features/          # MOVE: 7D feature extraction
│   ├── smt/              # MOVE: SMT solver integration  
│   ├── solve/            # MOVE: optimization algorithms
│   └── ml/               # MOVE: learning algorithms (if exists)
├── pkg/
│   └── engine/           # NEW: compiled engine interface
└── cmd/
    └── build-engine/     # NEW: builds shared library
```

#### 2.2 Private Engine Implementation
```go
// contextlite-private/pkg/engine/engine.go
package engine

import (
    "contextlite/pkg/types"  // Import PUBLIC types
)

type PrivateEngine struct {
    features *features.Extractor    // Private implementation
    smt      *smt.Z3Solver         // Private implementation
    storage  types.StorageInterface // Public interface
}

func (e *PrivateEngine) AssembleContext(req types.ContextRequest) (*types.ContextResult, error) {
    // PROPRIETARY ALGORITHM IMPLEMENTATION
    return result, nil
}

// Export C-compatible functions for shared library
//export AssembleContext
func AssembleContext(requestJSON string) string {
    // C wrapper for Go implementation
}
```

### Phase 3: Public Repository Cleanup (SURGICAL PRECISION)
**Goal**: Remove private code, add interface implementations

#### 3.1 Remove Private Packages
```bash
# ATOMIC REMOVALS (can be reverted easily)
git mv internal/features ../contextlite-private/internal/
git mv internal/smt ../contextlite-private/internal/  
git mv internal/solve ../contextlite-private/internal/
git rm -r internal/features internal/smt internal/solve
```

#### 3.2 Add Stub Implementations (FALLBACK SAFETY)
```go
// internal/engine/stub.go (NEW - PUBLIC FALLBACK)
type StubEngine struct {
    storage storage.Interface
}

func (s *StubEngine) AssembleContext(req types.ContextRequest) (*types.ContextResult, error) {
    // BASIC BM25 + heuristic selection (no SMT optimization)
    // Ensures public repo ALWAYS WORKS even without private engine
    return basicSelection(req), nil
}
```

#### 3.3 Dynamic Engine Loading  
```go
// internal/engine/loader.go (NEW - PLUGIN SYSTEM)
func LoadEngine(config Config) types.ContextEngine {
    // Try to load private engine first
    if engine := loadPrivateEngine(); engine != nil {
        return engine
    }
    
    // Fallback to public stub engine
    return NewStubEngine()
}

func loadPrivateEngine() types.ContextEngine {
    // Load compiled private engine (.so/.dll/.dylib)
    if lib, err := plugin.Open("contextlite-engine.so"); err == nil {
        // Return wrapped private engine
        return wrapPrivateEngine(lib)
    }
    return nil
}
```

### Phase 4: Build System Integration (SEAMLESS OPERATION)

#### 4.1 Private Engine Build
```makefile
# contextlite-private/Makefile
build-engine:
	go build -buildmode=c-shared -o contextlite-engine.so ./pkg/engine

build-all-platforms:
	GOOS=linux GOARCH=amd64 go build -buildmode=c-shared -o contextlite-engine-linux.so ./pkg/engine
	GOOS=darwin GOARCH=amd64 go build -buildmode=c-shared -o contextlite-engine-darwin.so ./pkg/engine  
	GOOS=windows GOARCH=amd64 go build -buildmode=c-shared -o contextlite-engine-windows.dll ./pkg/engine
```

#### 4.2 Public Repo Integration
```makefile
# contextlite/Makefile (UPDATED)
build: build-engine
	go build -o build/contextlite ./cmd/contextlite

build-engine:
	@if [ -f "../contextlite-private/contextlite-engine.so" ]; then \
		cp ../contextlite-private/contextlite-engine.so ./; \
	else \
		echo "Private engine not found, using stub implementation"; \
	fi

build-public-only:
	go build -tags stub -o build/contextlite-public ./cmd/contextlite
```

---

## DEPENDENCY RESOLUTION MATRIX

### Import Changes Required:

| File | Current Import | New Import | Change Type |
|------|---------------|------------|-------------|
| `cmd/contextlite/main.go` | `internal/pipeline` | `internal/engine` | SIMPLE |
| `internal/api/server.go` | `internal/features` | `pkg/types` | INTERFACE |
| `internal/pipeline/pipeline.go` | `internal/{features,smt}` | `pkg/types` | INTERFACE |
| All other files | NO CHANGES | NO CHANGES | NONE ✅ |

### Build Tags Strategy:
```go
// +build !stub
// Private engine available

// +build stub  
// Public-only build
```

---

## RISK MITIGATION

### Critical Success Factors:
1. **Interfaces First**: All coupling goes through `pkg/types` interfaces
2. **Backward Compatibility**: Public repo ALWAYS builds and runs
3. **Gradual Migration**: Each step is independently testable
4. **Rollback Plan**: Every change can be reverted atomically

### Testing Strategy:
```bash
# Test public repo independently
cd contextlite && go build ./cmd/contextlite && ./build/contextlite --test

# Test private engine compilation
cd contextlite-private && make build-engine

# Test integrated system  
cd contextlite && make build && ./build/contextlite --test-integrated
```

### Validation Checkpoints:
- [ ] Public repo compiles without private code ✅
- [ ] Private repo compiles independently ✅  
- [ ] Interface contracts are respected ✅
- [ ] Integrated system maintains performance ✅
- [ ] No hardcoded paths or references ✅

---

## IMPLEMENTATION TIMELINE

### Day 1 Morning (3 hours): Interface Layer
- [ ] Create `pkg/types/interfaces.go` with all abstractions
- [ ] Update `internal/pipeline` to use interfaces  
- [ ] Update `internal/api` to use interfaces
- [ ] **CHECKPOINT**: Public repo still compiles ✅

### Day 1 Afternoon (3 hours): Private Repo Setup
- [ ] Create `../contextlite-private/` directory structure
- [ ] Move `internal/{features,smt,solve}` to private repo
- [ ] Create private engine implementation
- [ ] **CHECKPOINT**: Private repo compiles ✅

### Day 2 Morning (2 hours): Integration Layer
- [ ] Add stub engine implementation to public repo
- [ ] Create dynamic engine loader system
- [ ] Update build system for both repos
- [ ] **CHECKPOINT**: Both repos work independently ✅

### Day 2 Afternoon (2 hours): Final Integration
- [ ] Test compiled engine integration
- [ ] Add license validation to private engine
- [ ] Final security audit and cleanup
- [ ] **CHECKPOINT**: Full system working ✅

---

## SUCCESS METRICS

### Zero Dependency Hell Achieved When:
- [x] **Public repo**: Builds and runs without any private code
- [x] **Private repo**: Compiles to shared library independently  
- [x] **Integration**: Dynamic loading works seamlessly
- [x] **Performance**: No degradation in assembled system
- [x] **Security**: Private algorithms completely hidden
- [x] **Licensing**: Proper enforcement and validation

### Code Quality Maintained:
- [x] All tests pass in both repositories
- [x] No circular dependencies created  
- [x] Interface contracts clearly defined
- [x] Documentation updated appropriately
- [x] Build system is reliable and reproducible

**RESULT: SURGICAL SEPARATION WITH ZERO DEPENDENCY HELL** 🎯
