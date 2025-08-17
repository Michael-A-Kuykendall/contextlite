# ContextLite: Technical Foundation & Complete Specification

## Mission
Create a Go-based, zero-dependency, quantum-inspired context sidecar (ContextLite) for AI systems. This document distills all key code, algorithms, and architectural innovations from AI State Pilot™ and the previous ContextLite attempt, so a new AI can fully understand and rebuild the system for maximum speed, privacy, and local operation.

---

## 1. System Overview
- **Language:** Go (1.21+)
- **Storage:** SQLite (FTS5, WAL, MMAP, optimized pragmas)
- **API:** HTTP/REST (sidecar model)
- **Core Innovations:**
  - **Advanced context selection** (budget management for perfect chunking)
  - Multi-dimensional scoring (7D features) with per-workspace calibration
  - Multi-level caching with corpus versioning and invalidation
  - Token budget enforcement inside optimization system with QoS fallback
  - All data local, no cloud dependencies, local optimization system runtime

**The optimization Advantage:** Traditional context selection is heuristic. ContextLite uses optimization (Satisfiability Modulo Theories) budget management to guarantee the *optimal* set of documents within token budgets and coherence requirements, with deterministic fallback when solver times out.

---

## 2. optimization Context Assembly: 7D Multi-Objective Optimization

### 2.1 Seven-Dimensional Feature Vector
```go
// Each document i has normalized 7D feature vector f_i ∈ [0,1]^7
// CRITICAL: Features must be SET-INDEPENDENT for optimization correctness
type FeatureVector struct {
    Relevance   float64  // Query match (BM25, semantic similarity)
    Recency     float64  // Time decay (exponential with 7-day half-life)
    Entanglement float64 // Cross-doc concept density (PMI over n-grams)
    Prior       float64  // Historical selection likelihood (path frequency, recent use)
    Uncertainty float64  // Score variance across estimators (BM25, TF-IDF, PMI)
    Authority   float64  // Document importance (file size, commit frequency, imports)
    Specificity float64  // Query-doc topic alignment (prevents generic matches)
}

// SET-DEPENDENT features handled via pairwise terms y_ij:
// - Coherence: how well docs fit together (similarity bonuses)
// - Diversity: anti-redundancy (similarity penalties)

// Per-workspace z-score normalization to [0,1]
// Persisted in workspace_weights.normalization_stats
```

### 2.2 optimization Multi-Objective Formulations

**Option A: Weighted-Sum Scalarization (Default)**
```go
// optimization Boolean variables
x_i ∈ {0,1}     // Select document i
y_ij ∈ {0,1}    // Co-selection indicator for top-M pairs

// Per-document utility (SET-INDEPENDENT features only)
v_i = α₁*Rel_i + α₂*Rec_i + α₃*Ent_i + α₄*Prior_i + 
      α₅*Auth_i + α₆*Spec_i - α₇*Unc_i

// Pairwise terms (top-M neighbors per doc)
r_ij = redundancy_penalty * similarity(i,j)    // Diversity via penalties
c_ij = coherence_bonus * concept_overlap(i,j)  // Coherence via bonuses

// Maxoptimization objective
SOFT: x_i (weight: scale(v_i))              // Reward selecting doc i
SOFT: ¬(x_i ∧ x_j) (weight: scale(r_ij))    // Penalty for redundant pairs
SOFT: (x_i ∧ x_j) (weight: scale(c_ij))     // Bonus for coherent pairs

// Hard budgets
Σ t_i * x_i ≤ B              // Token budget (linear arithmetic)
Σ x_i ≤ D_max                // Max documents
```

**Option B: Lexicographic Priorities (Priority Tiers)**
```go
// Tier-based weights with computed dominance bounds
// M_t = 1 + Σ_{u>t} U_u where U_u is max possible sum for tier u
func computeTierMultipliers() []int {
    // After integer scaling (×1000), compute upper bounds per tier
    U := []int{1000, 1000, 1000, 1000, 1000, 1000, 1000}  // max per feature
    M := make([]int, 7)
    M[6] = 1  // base tier
    for t := 5; t >= 0; t-- {
        M[t] = 1 + sum(U[t+1:])  // strict dominance
    }
    return M  // e.g., [6001, 5001, 4001, 3001, 2001, 1001, 1]
}

// Soft weight for document i (lexicographic priority order)
W_i = M₁*Rel_i + M₂*Rec_i + M₃*Ent_i + M₄*Prior_i + 
      M₅*Auth_i + M₆*Spec_i + M₇*(1-Unc_i)

// Single Maxoptimization solve with computed tiered weights
// Guarantees: Relevance first, then Recency, then Entanglement, etc.
```

**Option C: ε-Constraint (Pareto Control)**
```go
// Primary objective: maximize relevance
max Σ Rel_i * x_i

// Secondary budgets using PAIRWISE metrics (not set-dependent features)
Σ sim_ij * y_ij ≤ R_max         // Cap total redundancy
Σ concept_overlap_ij * y_ij ≥ C_min  // Minimum coherence requirement
Σ Rec_i * x_i ≥ θ_recency       // Minimum recency (set-independent)
Σ Ent_i * x_i ≥ θ_entanglement  // Minimum entanglement density
```

### 2.3 optimization Model Construction & Solving
```go
// Model size bounds for tractability
K ≤ 200 candidates           // Keep optimization model manageable
M ≤ 5 pairs per doc          // Limit pairwise budgets
Variables ≈ K + K*M ≈ 1,200  // x_i + y_ij variables
Constraints ≈ 3*K*M ≈ 3,000  // Linking + budget + cardinality

// optimization system configuration
optimization_timeout_ms: 250          // Hard timeout
max_opt_gap: 0.05            // 5% optimality gap acceptable
integer_scaling: 1000        // Scale weights to int64 for solver

// Fallback strategy (when optimization times out/fails)
1. MMR-greedy selection with 7D weighted scoring
2. Deterministic knapsack within token budget
3. Log fallback reason and achieved objective value
```

---

## 3. SQLite Storage: Schema & Performance

### 3.1 Schema
```sql
CREATE TABLE documents (
  id TEXT PRIMARY KEY,
  content TEXT NOT NULL,
  content_hash TEXT NOT NULL,
  path TEXT,                             -- File path for workspace docs
  lang TEXT,                             -- Programming language detected
  mtime BIGINT,                          -- Modified time for invalidation
  token_count INTEGER,                   -- Model-specific token count
  model_id TEXT,                         -- Tokenizer model used
  quantum_score REAL DEFAULT 0,
  entanglement_map TEXT,
  coherence_history TEXT,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
CREATE VIRTUAL TABLE documents_fts USING fts5(
  content,
  content=documents,
  content_rowid=rowid,
  tokenize='porter ascii'
);
CREATE TABLE query_cache (
  query_hash TEXT PRIMARY KEY,
  corpus_hash TEXT NOT NULL,             -- Corpus version for invalidation
  model_id TEXT NOT NULL,                -- Tokenizer version
  tokenizer_version TEXT NOT NULL,       -- Tokenizer version hash
  result_context TEXT NOT NULL,
  quantum_metrics TEXT NOT NULL,
  document_scores TEXT NOT NULL,
  coherence_score REAL NOT NULL,
  optimization_gap REAL,                 -- Solver optimality gap
  solve_time_ms INTEGER,                 -- Solver timing
  fallback_used BOOLEAN DEFAULT 0,       -- Whether fallback was used
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  expires_at TIMESTAMP NOT NULL,
  access_count INTEGER DEFAULT 1
);
CREATE TABLE workspace_weights (
  workspace_path TEXT PRIMARY KEY,
  relevance_weight REAL DEFAULT 0.4,
  recency_weight REAL DEFAULT 0.2,
  diversity_weight REAL DEFAULT 0.2,
  entanglement_weight REAL DEFAULT 0.2,
  redundancy_penalty REAL DEFAULT 0.3,
  normalization_stats TEXT,              -- JSON: z-score params per feature
  update_count INTEGER DEFAULT 0,
  last_updated TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
CREATE TABLE concepts (
  doc_id TEXT,
  term TEXT,
  tf INTEGER,
  df INTEGER,                            -- Document frequency
  PRIMARY KEY(doc_id, term)
);
CREATE TABLE meta (
  key TEXT PRIMARY KEY,
  value TEXT NOT NULL,
  updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
-- Meta keys: corpus_hash, tokenizer_version, vocab_hash, schema_version
CREATE INDEX idx_documents_token_count ON documents(token_count);
CREATE INDEX idx_documents_mtime ON documents(mtime);
CREATE INDEX idx_concepts_term ON concepts(term);
CREATE INDEX idx_query_cache_composite ON query_cache(corpus_hash, model_id, tokenizer_version);
```

### 3.2 Performance Pragmas
```sql
PRAGMA journal_mode = WAL;
PRAGMA synchronous = NORMAL;
PRAGMA cache_size = -64000;
PRAGMA temp_store = MEMORY;
PRAGMA mmap_size = 268435456;
PRAGMA optimize;
```

---

## 4. HTTP API: Sidecar Endpoints

### 4.1 Context Assembly
```http
POST /api/v1/context/assemble
{
  "query": "How does user authentication work?",
  "max_tokens": 4000,
  "max_documents": 10,
  "use_optimization": true,
  "optimization_timeout_ms": 250,
  "objective_style": "weighted-sum"
}
```

### 4.2 Health & Stats
```http
GET /health
GET /api/v1/storage/info
```

---

## 5. Caching & Optimization
- **L1:** In-memory LRU for hot queries
- **L2:** SQLite query cache with comprehensive invalidation keys
- **L3:** Context snapshots (precomputed assemblies for common patterns)
- **Cache Keys:** (corpus_hash, model_id, tokenizer_version, query_hash, weights_hash, concept_df_version)
- **Background:**
  - optimization model optimization
  - Cache warming for common queries
  - Database VACUUM/ANALYZE

---

## 6. Complete HTTP Sidecar Implementation Plan

### Core Architecture
```
contextlite/
├── cmd/
│   └── contextlite/
│       └── main.go                    # HTTP sidecar server
├── internal/
│   ├── optimization/
│   │   ├── solver.go                  # **CORE**: optimization system integration (optimizer/CVC5)
│   │   ├── model.go                   # optimization model construction (variables, budgets, Maxoptimization)
│   │   ├── fallback.go                # MMR-greedy + knapsack fallback
│   │   └── calibration.go             # Per-workspace weight adaptation
│   ├── storage/
│   │   ├── sqlite.go                  # SQLite + FTS5 + schema management
│   │   ├── schema.sql                 # Full schema with weight calibration
│   │   ├── migrations.go              # Schema versioning
│   │   └── invalidation.go            # Cache invalidation logic
│   ├── features/
│   │   ├── scoring.go                 # 7D feature extraction with z-score normalization
│   │   ├── similarity.go              # Pairwise similarity (TF-IDF, SimHash)
│   │   ├── concepts.go                # PMI-based entanglement calculation
│   │   └── tokenizer.go               # Model-specific token counting
│   ├── pipeline/
│   │   ├── assembly.go                # Main pipeline: FTS → optimization → Assemble
│   │   ├── sampling.go                # k-best softmax sampling (optional)
│   │   └── timing.go                  # Per-stage timing instrumentation
│   ├── cache/
│   │   ├── memory.go                  # L1 in-memory LRU cache
│   │   ├── sqlite.go                  # L2 SQLite query cache
│   │   └── snapshots.go               # L3 quantum context snapshots
│
│   └── api/
│       ├── server.go                  # Chi router + middleware
│       ├── handlers.go                # HTTP handlers
│       ├── types.go                   # Request/response structs
│       └── middleware.go              # Logging, CORS, auth prep
├── pkg/
│   ├── types/
│   │   ├── document.go                # Core document types
│   │   ├── quantum.go                 # Quantum scoring types
│   │   └── context.go                 # Context assembly types
│   └── config/
│       └── config.go                  # Configuration management
├── configs/
│   └── default.yaml                   # Default configuration
├── go.mod
├── Dockerfile
├── docker-compose.yml                 # For local development
└── README.md
```

### HTTP API Design (Complete Sidecar Interface)

**Core Endpoints:**
```go
// Context assembly (main endpoint with optimization optimization)
POST /api/v1/context/assemble

// Document management
POST /api/v1/documents                 # Add single document
POST /api/v1/documents/bulk            # Bulk import documents
POST /api/v1/documents/workspace       # Scan workspace directory
DELETE /api/v1/documents/{id}          # Remove document
GET /api/v1/documents/search           # Direct search (no assembly)

// optimization budget management
POST /api/v1/optimization/budgets           # Add/update optimization budget
GET /api/v1/optimization/budgets            # List active budgets
DELETE /api/v1/optimization/budgets/{id}    # Remove budget
POST /api/v1/optimization/solve                 # Direct optimization solve for debugging

// Weight calibration management
POST /api/v1/weights/update            # Update workspace weights from user feedback
GET /api/v1/weights                    # Get current workspace weights
POST /api/v1/weights/reset             # Reset weights to defaults

// Cache management
POST /api/v1/cache/invalidate          # Clear cache
GET /api/v1/cache/stats                # Cache performance

// System endpoints
GET /health                            # Health check with detailed stats
GET /api/v1/storage/info              # Storage stats
GET /api/v1/optimization/stats                  # optimization system performance metrics
```

**Main Context Assembly API:**
```go
type AssembleRequest struct {
    Query               string   `json:"query"`
    MaxTokens          int      `json:"max_tokens"`
    MaxDocuments       int      `json:"max_documents"`
    WorkspacePath      string   `json:"workspace_path,omitempty"`
    IncludePatterns    []string `json:"include_patterns,omitempty"`
    ExcludePatterns    []string `json:"exclude_patterns,omitempty"`
    ModelID            string   `json:"model_id,omitempty"`        // Tokenizer model
    
    // optimization optimization parameters
    Useoptimization             bool     `json:"use_optimization"`
    optimizationTimeoutMs       int      `json:"optimization_timeout_ms,omitempty"`
    MaxOptGap          float64  `json:"max_opt_gap,omitempty"`
    
    // Sampling (k-best only)
    EnableSampling     bool     `json:"enable_sampling"`
    Temperature        float64  `json:"temperature,omitempty"`
    TopK               int      `json:"top_k,omitempty"`           // k-best solutions
    
    // Caching
    UseCache           bool     `json:"use_cache"`
    CacheTTL           int      `json:"cache_ttl,omitempty"`
}

type AssembledContext struct {
    Query               string              `json:"query"`
    Documents           []DocumentReference `json:"documents"`
    TotalTokens         int                 `json:"total_tokens"`
    CoherenceScore      float64             `json:"coherence_score"`
    optimizationMetrics          optimizationMetrics          `json:"optimization_metrics"`
    Timings             StageTimings        `json:"timings"`
}

type DocumentReference struct {
    ID              string             `json:"id"`
    Path            string             `json:"path"`
    Content         string             `json:"content"`
    Language        string             `json:"language"`
    UtilityScore    float64            `json:"utility_score"`         // v_i
    RelevanceScore  float64            `json:"relevance_score"`
    RecencyScore    float64            `json:"recency_score"`
    DiversityScore  float64            `json:"diversity_score"`
    InclusionReason string             `json:"inclusion_reason"`
}

type optimizationMetrics struct {
    SolverUsed      string  `json:"solver_used"`           // "z3opt" or "mmr-fallback"
    SolveTimeMs     int     `json:"solve_time_ms"`
    VariableCount   int     `json:"variable_count"`
    ConstraintCount int     `json:"budget_count"`
    KCandidates     int     `json:"K_candidates"`
    PairsCount      int     `json:"pairs_count"`
    BudgetTokens    int     `json:"budget_tokens"`
    MaxDocs         int     `json:"max_docs"`
    optimizerStatus        string  `json:"z3_status,omitempty"`   // "sat", "unsat", "timeout"
    Objective       int     `json:"objective,omitempty"`   // Integer objective from optimizer
    FallbackReason  string  `json:"fallback_reason,omitempty"`
}

type StageTimings struct {
    FTSHarvestMs    int `json:"fts_harvest_ms"`
    FeatureBuildMs  int `json:"feature_build_ms"`
    optimizationSolverMs     int `json:"optimization_solver_ms"`
    TotalMs         int `json:"total_ms"`
}
```

### Implementation Strategy

**Phase 0: Benchmarking Framework (Day 1)**
1. `bench/` - Baseline performance measurements vs existing solutions
2. `bench/comparison_test.go` - Prove "10,000x faster" claims
3. `bench/testdata/` - Sample documents for repeatable benchmarks
4. **Deliverable**: Performance baseline established

**Phase 1: Core Foundation + optimization Engine (Week 1)**
1. `go.mod` with deps: chi, modernc.org/sqlite, yaml config
2. `pkg/types/` - all core data structures including optimization budgets
3. `internal/optimization/` - **ESSENTIAL**: optimization context optimization engine (from aistatepilot-go)
4. `internal/optimization/patterns.go` - Expected value patterns & budget generation
5. `internal/optimization/dossiers.go` - Superposition dossier system for context chunking
6. `internal/api/` - HTTP server skeleton with optimization-aware endpoints
7. **Deliverable**: optimization engine working with mock data, HTTP server responding

**Phase 2: SQLite Storage + Schema (Week 1-2)**
1. `internal/storage/schema.sql` - Full schema including optimization budget storage
2. `internal/storage/sqlite.go` - CRUD with FTS5 + optimization budget persistence
3. `internal/storage/migrations.go` - Schema versioning
4. Wire storage into document management + optimization budget storage
5. **Deliverable**: Can import documents, store optimization patterns, perform FTS search

**Phase 3: Features + Advanced Optimization (Week 2-3)**
1. `internal/features/scoring.go` - 7D SET-INDEPENDENT feature extraction with z-score normalization
2. `internal/features/similarity.go` - Pairwise similarity computation for coherence/diversity
3. `internal/optimization/model.go` - optimization model construction with proper set-independent objectives
4. `internal/pipeline/assembly.go` - Main pipeline: FTS → Features → optimization → Assembly
5. **Deliverable**: Full intelligent context selection with mathematically correct optimization

**Phase 4: Multi-Level Caching + Optimization (Week 3)**
1. `internal/cache/memory.go` - L1 LRU cache (includes optimization solution caching)
2. `internal/cache/sqlite.go` - L2 query cache with optimization pattern storage
3. `internal/cache/snapshots.go` - L3 quantum snapshots + precomputed optimization solutions
4. Token counting, context window management
5. **Deliverable**: Full caching hierarchy + performance optimization

**Phase 5: Production Ready (Week 4)**
1. Configuration management (env vars + config.json)
2. Logging, metrics, error handling
3. Docker container + docker-compose
4. Bulk document operations, health checks
5. **Deliverable**: Production-ready intelligent context sidecar

### Configuration
```yaml
# configs/default.yaml
server:
  port: 8080
  host: "127.0.0.1"                     # Local bind by default
  cors_enabled: false                   # CORS off by default
  auth_token: ""                        # Optional bearer token
  
storage:
  database_path: "./contextlite.db"
  cache_size_mb: 64
  
optimization:
  solver_timeout_ms: 250                # Hard optimization system timeout
  max_opt_gap: 0.05                     # 5% optimality gap acceptable
  max_candidates: 200                   # K limit
  max_pairs_per_doc: 5                  # M limit
  integer_scaling: 1000                 # Scale weights to int64
  objective_style: "weighted-sum"       # weighted-sum | lexicographic | epsilon-budget
  
# 7D Feature Weights (per-workspace adaptive)
weights:
  relevance: 0.30      # α₁
  recency: 0.20        # α₂  
  entanglement: 0.15   # α₃
  prior: 0.15          # α₄
  authority: 0.10      # α₅
  specificity: 0.05    # α₆
  uncertainty: 0.05    # α₇ (subtracted in objective)
  redundancy_penalty: 0.3               # Pairwise penalty weight
  coherence_bonus: 0.2                  # Pairwise coherence bonus
  weight_update_rate: 0.01              # Online learning rate
  weight_caps: [0.01, 0.5]              # Min/max weight bounds

# Lexicographic tier multipliers (computed at runtime from bounds)
lexicographic:
  compute_at_runtime: true              # Calculate M_t = 1 + Σ_{u>t} U_u
  
# ε-budget thresholds (when objective_style = "epsilon-budget")
epsilon_budget:
  max_redundancy: 0.4                   # Σ sim_ij * y_ij ≤ 0.4
  min_coherence: 0.3                    # Σ concept_overlap_ij * y_ij ≥ 0.3
  min_recency: 0.2                      # Σ Rec_i * x_i ≥ 0.2
  
tokenizer:
  model_id: "gpt-4"                     # Default model
  max_tokens_default: 4000
  
cache:
  l1_size: 1000
  l2_ttl_minutes: 30
  l3_enabled: true
  
logging:
  level: "info"
  include_timings: true
  include_optimization_metrics: true
```

### Dependencies
```go
// Local solver runtime dependencies
require (
    github.com/go-chi/chi/v5 v5.0.8         // HTTP router
    github.com/go-chi/cors v1.2.1           // CORS middleware
    modernc.org/sqlite v1.27.0              // Pure Go SQLite
    gopkg.in/yaml.v3 v3.0.1                 // Config parsing
    go.uber.org/zap v1.25.0                 // Structured logging
    // optimizer Go bindings OR CP-SAT protobuf (choose one solver path)
    github.com/aclements/go-z3/z3 v0.0.0    // optimizer Maxoptimization system (if optimization path)
    // google.golang.org/protobuf v1.31.0   // CP-SAT alternative (if ILP path)
)
```

### Success Criteria
1. **Drop-in Sidecar**: Any AI can call HTTP API and get optimized context
2. **Performance**: p50 ≤300ms, p95 ≤600ms uncached; cached ≤30ms (documented hardware: NVMe, 100k docs, K=200)
3. **Local**: No cloud dependencies, local solver runtime only
4. **Optimal**: optimization Maxoptimization optimization with ≤5% gap or deterministic fallback
5. **Adaptive**: Per-workspace weight calibration with online learning
6. **Observable**: Per-stage timings, optimization gaps, fallback reasons in all responses

---

## 7. Key Code Snippets

### 7.1 optimization Model Construction for 7D Optimization
```go
func Buildoptimization7DModel(candidates []Document, 
                    query string, 
                    budget int,
                    style string) *optimizationModel {
  // Extract & normalize 7D features per workspace
  features := extractNormalized7DFeatures(candidates, workspace)
  
  // Choose objective formulation
  switch style {
  case "weighted-sum":
    return buildWeightedSumoptimization(features, budget)
  case "lexicographic": 
    return buildLexicographicoptimization(features, budget)
  case "epsilon-budget":
    return buildEpsilonConstraintoptimization(features, budget)
  }
  
  // Variables: x_i ∈ {0,1}, y_ij ∈ {0,1} for top-M pairs
  // Hard budgets: token budget, max docs, linking budgets
  // Soft budgets: 7D utility maximization, redundancy penalties
  // Returns: optimization model ready for optimizer/CVC5 Maxoptimization system
}
```

### 7.2 Context Assembly Pipeline (optimization 7D-Optimized)
```go
func AssembleContext(query string, workspace string) ContextResult {
  // 1. FTS search → top-K candidates (K≤200)
  // 2. Extract 7D SET-INDEPENDENT features → normalize per-workspace z-score
  // 3. Compute pairwise similarities for top-M neighbors per doc
  // 4. Build optimization model with chosen objective style (weighted-sum/lex/ε-budget)
  // 5. Solve with optimizer Maxoptimization (timeout 250ms, max gap 5%)
  // 6. If timeout/gap → fallback to 7D-weighted MMR-greedy + knapsack
  // 7. Optional: k-best sampling over diverse near-optimal optimization solutions
  // 8. Cache with (corpus_hash, model_id, tokenizer_version, query_hash, weights_hash, concept_df_version)
}
```

### 7.3 Per-Workspace 7D Weight Calibration
```go
func Update7DWeights(workspace string, feedback UserFeedback) {
  // 1. Load current 7D weights and normalization stats (μ, σ per feature)
  // 2. For each accepted/rejected document, compute 7D feature gradients
  // 3. Update weights via AdaGrad: w_new = w_old + η * ∇logistic_loss
  // 4. Apply weight caps: clip each α_i ∈ [0.01, 0.5], normalize Σα_i = 1
  // 5. Update workspace_weights table with new 7D weights
  // 6. Invalidate cached contexts for this workspace (weights_hash changed)
}
```

---

## 8. Business & Product
- **Dual license:** MIT (open) + Commercial
- **Target:** VS Code, Ollama, LocalAI, edge, privacy-first
- **Goal:** 10,000x faster than vector DBs, 100% local, drop-in binary

---

## 9. References
- AI State Pilot™ quantum-framework (Go)
- contextlite/ (previous attempt)
- This doc is the canonical starting point for a new AI to build ContextLite
