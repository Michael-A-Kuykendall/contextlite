# ContextLite Feature Formulas Documentation

## Overview

ContextLite implements a 7-dimensional feature vector system where each feature is **set-independent** to ensure mathematical correctness in optimization optimization. This document provides complete formula specifications with unit tests.

## 7D Feature Vector

### 1. Relevance (BM25-based Query Matching)

**Formula**: 
```
Relevance = Σ(term ∈ query) IDF(term) × TF_norm(term, doc)

Where:
- IDF(term) = log((N - df + 0.5) / (df + 0.5))
- TF_norm(term, doc) = tf × (k1 + 1) / (tf + k1 × (1 - b + b × |doc| / avg_doc_len))
- k1 = 1.5, b = 0.75 (BM25 parameters)
- N = total documents, df = document frequency, tf = term frequency
```

**Code Location**: `internal/features/scoring.go:computeRelevance()`

**Properties**: 
- Range: [0, ∞) (typically 0-20 for normal queries)
- Set-independent: Only depends on query-document pair, not other selected documents

### 2. Recency (Temporal Decay)

**Formula**:
```
Recency = exp(-ln(2) × days_since_modification / 7.0)

Where:
- days_since_modification = (current_time - doc.mtime) / (24 × 3600)
- Half-life = 7 days
```

**Code Location**: `internal/features/scoring.go:computeRecency()`

**Properties**:
- Range: [0, 1]
- Set-independent: Only depends on document modification time
- Decay: 50% after 7 days, 25% after 14 days, etc.

### 3. Entanglement (Cross-document Concept Density)

**Formula**:
```
Entanglement = (1/|T|) × Σ(i,j ∈ T×T, i≠j) PMI(i,j)

Where:
- PMI(i,j) = log(P(i,j) / (P(i) × P(j)))
- T = top 20% most frequent terms in document
- P(i) = term frequency / document length
- P(i,j) = co-occurrence frequency / document length
```

**Code Location**: `internal/features/scoring.go:computeEntanglement()`

**Properties**:
- Range: [-∞, ∞] (typically -2 to +2)
- Set-independent: Only depends on internal document term relationships
- Measures semantic coherence within document

### 4. Prior (Historical Selection Likelihood)

**Formula**:
```
Prior = path_frequency_weight × extension_bias

Where:
- path_frequency_weight = log(1 + workspace_selection_count[doc.path])
- extension_bias = file_type_multiplier[doc.extension]
```

**Code Location**: `internal/features/scoring.go:computePrior()`

**Properties**:
- Range: [0, ∞) (typically 0-5)
- Set-independent: Only depends on document metadata and historical usage
- Learns from user selection patterns

### 5. Uncertainty (Score Variance)

**Formula**:
```
Uncertainty = std_dev(relevance_estimators) / mean(relevance_estimators)

Where:
- relevance_estimators = [BM25, TF-IDF, cosine_similarity]
- Coefficient of variation approach
```

**Code Location**: `internal/features/scoring.go:computeUncertainty()`

**Properties**:
- Range: [0, ∞) (typically 0-2)
- Set-independent: Only depends on document-query scoring variance
- Higher uncertainty = less confident relevance assessment

### 6. Authority (Document Importance)

**Formula**:
```
Authority = 0.6 × size_score + 0.4 × token_score

Where:
- size_score = tanh(file_size_bytes / 10000)  # Normalized file size
- token_score = tanh(token_count / 2000)      # Normalized token count
```

**Code Location**: `internal/features/scoring.go:computeAuthority()`

**Properties**:
- Range: [0, 1]
- Set-independent: Only depends on document intrinsic properties
- Larger, more comprehensive documents score higher

### 7. Specificity (Query-Document Topic Alignment)

**Formula**:
```
Specificity = (query_overlap / |query_terms|) × (query_overlap / |doc_unique_terms|)

Where:
- query_overlap = |query_terms ∩ doc_terms|
- Geometric mean of query coverage and document focus
```

**Code Location**: `internal/features/scoring.go:computeSpecificity()`

**Properties**:
- Range: [0, 1]
- Set-independent: Only depends on query-document term overlap
- High when document focuses on query topics

## Feature Normalization

All features are normalized using workspace-specific statistics:

```go
normalized_feature = (raw_feature - workspace_mean) / (workspace_stddev + 1e-8)
```

This ensures features are:
- Zero-centered across the workspace
- Unit-scaled for fair weight combination
- Numerically stable (avoiding division by zero)

## Advanced Optimization

The 7D features combine into a utility score:

```
UtilityScore = w₁×Relevance + w₂×Recency + w₃×Entanglement + w₄×Prior + w₅×Uncertainty + w₆×Authority + w₇×Specificity

Where weights are workspace-adaptive:
- w = [0.30, 0.20, 0.15, 0.15, 0.10, 0.05, 0.05] (default)
- Weights updated via online learning based on user selections
```

The optimization system maximizes total utility while enforcing budgets:
- Document count limits
- Token budget budgets  
- Pairwise redundancy penalties
- Coherence requirements

## Mathematical Guarantees

1. **Set Independence**: Each feature depends only on (query, document) pair, not on other selected documents
2. **Normalization Stability**: Features bounded and numerically stable
3. **optimization Correctness**: Linear feature combination enables exact budget management
4. **Scalability**: O(K) feature computation for K documents

This mathematical foundation enables provably optimal document selection via optimizer optimization solving.
