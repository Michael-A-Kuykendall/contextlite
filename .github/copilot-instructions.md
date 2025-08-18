# ContextLite AI Coding Agent Instructions

Purpose: Enable an AI agent to be productive immediately in this repo. Follow these repo-specific conventions. Keep changes minimal, fast, and aligned with the existing architecture.

## 1. Big Picture Architecture
- Core Go library (pkg + internal) providing an embedded context engine atop SQLite (modernc.org/sqlite) – no external services.
- Layers:
  1. `pkg/types` – data contracts (Document, QueryResult, Config, QueryOptions, Stats, ScoredDocument).
  2. `pkg/storage` – persistence (SQLite schema, FTS5 virtual table, caching, document scores). Optimized via PRAGMAs; avoid changing unless needed for performance/compatibility.
  3. `internal/engine` – scoring & selection (“quantum-inspired” heuristics: relevance, recency (7‑day half-life), diversity (Jaccard), quantum weight, coherence filtering, temperature-based probabilistic selection).
  4. `pkg/contextlite` – public client façade (options pattern, caching, background cache cleanup every 5m, convenience query option helpers).
  5. `cmd/contextlite` – HTTP server providing REST API for context operations.
- Data flow (query path): HTTP client -> REST API -> client -> engine -> storage (search + scoring) -> result -> back to client.

## 2. Key Workflows
- Build all: `make build` (produces `./build/contextlite`).
- Run tests: `make test` (Go tests under `test/`). Benchmarks: `make bench` (uses `test` package benchmarks). Coverage: `make coverage`.
- Quick example: `go run ./examples/basic`.
- Release cross-compiles: `make release` (CGO_DISABLED=0 not set except to 0? Currently sets `CGO_ENABLED=0` for static builds with modernc sqlite pure Go driver).
- Clean: `make clean` (also removes temp DB files).

## 3. Conventions & Patterns
- Options Pattern: Public configuration via functional options (`WithDatabase`, `WithMaxDocuments`, etc.). For per-query overrides use `QueryWithOpts` + inline option builders (`WithMaxResults`, `WithoutCache`, etc.). Maintain naming symmetry.
- Caching: Enabled by default. Cache key = SHA256(query). Only cache if `Score > 0.5`. Respect `WithoutCache()` which sets `QueryOptions.NoCache`.
- Document IDs: If empty, auto-generated from first 8 bytes of SHA256(content). Keep this deterministic behavior.
- Scoring Weights: TotalScore formula in `engine.scoreDocuments` – preserve weight ratios unless a deliberate tuning (document rationale in commit message if changed).
- Recency: Exponential decay with 7‑day half-life. Adjust only with justification.
- Diversity: Simple similarity Jaccard-style on token sets. Avoid expensive embeddings; project promise = zero dependencies/max speed.
- Coherence Threshold: If selection coherence below threshold, perform stricter selection (`strictSelection`). Maintain this fallback structure.
- Storage: Use FTS5 first; fallback to LIKE search on error. Any schema change must preserve backward compatibility or include migration logic.
- Background routines: Cache cleanup goroutine launched only if caching enabled.
- Error Handling: Return wrapped errors with context (`fmt.Errorf("...: %w", err)`). Do not panic in library code.
- Public API Stability: Keep `Client` surface small; prefer adding new option functions over new parameters.

## 4. Adding Features Safely
- New Query Dimension: Add fields to `types.ScoredDocument` & adjust weight composition; update serialization only if exposed via results (`QueryResult.Documents` only exposes subset fields via `DocumentReference`).
- New Storage Data: Add table + index in `initSchema`; ensure idempotent CREATE statements. Consider migration path; avoid destructive ALTER.
- Performance Guardrails: Avoid introducing external network calls or heavy dependencies (promise: zero-dependency, local, microseconds). Any added library must be pure Go and lightweight.

## 5. Testing Practices
- Tests live in `test/` (integration-style using real SQLite file DB). Create temp DB paths and defer removal. Keep test runtime small (< a few seconds). Use existing patterns from `client_test.go`.
- Benchmarks: Place under same package; disable cache for query benchmarks (`WithCacheEnabled(false)`).

## 6. Common Pitfalls / Gotchas
- FTS Index: After updating a document, code currently inserts into `documents_fts` again (could duplicate rows). Evaluate before refactoring; if optimizing, ensure search results remain correct.
- Stats Struct Mismatch: Extension expects fields like `totalQueries`, `cacheHits` not currently in Go `Stats`; added usage in CLI implies future fields (`Stats` currently lacks these). If implementing, extend `types.Stats` + populate in storage/client and adjust CLI.
- Randomness: `probabilisticSelection` & `calculateQuantumWeight` rely on `math/rand` default seed; deterministic tests might need seeding if asserting order—current tests avoid order assertions.
- Large Files: Extension skips files > ~100k chars during auto indexing. Maintain threshold to keep performance promise.

## 8. Example: Adding a New Per-Query Option
1. Extend `types.QueryOptions` with field (e.g., `MinRelevance float64`).
2. Add helper `WithMinRelevance(val float64)` returning modifier func.
3. In `engine.Query`, apply override; filter `scoredDocs` before selection.
4. Update tests in `test/` verifying behavior.

## 9. Performance Principles
- Favor O(n) scans over complex indices; small local datasets (<10k docs typical).
- Keep allocations low; reuse slices only if measurable gain.
- Avoid reflection / generics complexity unless necessary.

## 10. Licensing Note
- Dual-license model; keep public API MIT-safe. Avoid adding GPL or copyleft deps.

## 11. When Unsure
- Imitate existing option & scoring patterns.
- Prioritize speed, determinism (outside controlled randomness), and zero external calls.
- Provide concise commit messages referencing affected layer (e.g., "engine: adjust diversity weight to reduce redundancy").

---
Provide feedback if any section is unclear or needs deeper detail; this doc should stay lean (goal: actionable guidance, not exhaustive spec).
