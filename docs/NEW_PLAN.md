# ContextLite → RAG Drop‑In: Full Refactor + Adapters (Patch‑Ready)

Purpose: remove VS Code/Copilot surface; add RAG‑stack integrations (LangChain/LlamaIndex/MCP) and native Go/Rust clients. Below are **surgical, paste‑ready diffs/files** matched to your repo (from the uploaded zip).

Repo root observed: `contextlite/` with `cmd/contextlite`, `internal/api`, `internal/pipeline`, `internal/storage`, `pkg/types`, and `vscode-extension/`.

---

## 0) High‑level steps (tl;dr)

1. **Delete** `vscode-extension/` and any build steps referencing it.
2. **Add** two HTTP endpoints used by adapters: `/api/v1/rank` and `/api/v1/snippet`.
3. **Add** one storage method: `GetDocumentByPath(ctx, path)`.
4. **Add** adapters/clients in `adapters/` for Python (LangChain/LlamaIndex), Node (MCP), Go, and Rust.
5. **Docs/Build**: update README/Makefile; add quick benchmarks scaffolding.

All code below is complete; copy it in as indicated.

---

## 1) Remove VS Code surface

**Delete (tree):**

```
vscode-extension/
```

If you want to keep the prior design note, move `COPILOT_INTEGRATION_DESIGN.md` into `archive/` (optional).

**Makefile cleanup:** remove targets that package the extension (if present). If you don’t keep a Makefile, ignore.

---

## 2) HTTP API additions (server + types)

### 2.1 Add `/api/v1/rank` and `/api/v1/snippet` routes

**File:** `internal/api/server.go`

**Insert into the API route block** (inside `r.Route("/api/v1", func(r chi.Router) { ... })`), just after existing context routes:

```go
// Lightweight RAG endpoints
r.Post("/rank", s.handleRank)
r.Post("/snippet", s.handleSnippet)
```

### 2.2 Add request/response structs and handlers

Append to `internal/api/server.go` (end of file or near other handlers):

```go
// --- RAG convenience types ---
type rankRequest struct {
    Query     string `json:"query"`
    K         int    `json:"k"`
    BudgetMs  int    `json:"budget_ms"`
    MaxTokens int    `json:"max_tokens,omitempty"`
    UseCache  bool   `json:"use_cache,omitempty"`
}

type position struct { Line int `json:"line"`; Character int `json:"character"` }

type rangeJSON struct { Start position `json:"start"`; End position `json:"end"` }

type rankItem struct {
    File    string    `json:"file"`
    Range   *rangeJSON `json:"range,omitempty"`
    Snippet string    `json:"snippet"`
    Score   float64   `json:"score"`
    Why     string    `json:"why"`
}

type rankResponse struct {
    Items  []rankItem `json:"items"`
    P99Ms  int        `json:"p99_ms"`
}

type snippetRequest struct {
    File  string   `json:"file"`
    Start position `json:"start"`
    End   position `json:"end"`
}

type snippetResponse struct {
    Snippet string `json:"snippet"`
}

// --- /api/v1/rank ---
func (s *Server) handleRank(w http.ResponseWriter, r *http.Request) {
    var reqBody rankRequest
    if err := json.NewDecoder(r.Body).Decode(&reqBody); err != nil {
        s.writeError(w, http.StatusBadRequest, "Invalid request body: "+err.Error())
        return
    }
    if reqBody.Query == "" { s.writeError(w, http.StatusBadRequest, "query required"); return }

    // Map to AssembleRequest
    ar := types.AssembleRequest{
        Query:        reqBody.Query,
        MaxTokens:    s.config.Tokenizer.MaxTokensDefault,
        MaxDocuments: 10,
        UseSMT:       true,
        UseCache:     reqBody.UseCache,
    }
    if reqBody.K > 0 { ar.MaxDocuments = reqBody.K }
    if reqBody.MaxTokens > 0 { ar.MaxTokens = reqBody.MaxTokens }

    ctx := r.Context()
    res, err := s.pipeline.AssembleContext(ctx, &ar)
    if err != nil {
        s.logger.Error("rank assembly failed", zap.Error(err))
        s.writeError(w, http.StatusInternalServerError, "assembly failed: "+err.Error())
        return
    }

    items := make([]rankItem, 0, len(res.Documents))
    for _, d := range res.Documents {
        score := d.UtilityScore
        if score == 0 && d.RelevanceScore > 0 { score = d.RelevanceScore }
        items = append(items, rankItem{
            File:    d.Path,
            Range:   nil,                   // precise line ranges unavailable here; use /snippet for exact slicing
            Snippet: d.Content,             // SMT/packing already trimmed content
            Score:   score,
            Why:     d.InclusionReason,
        })
    }

    out := rankResponse{ Items: items, P99Ms: int(res.Timings.TotalMs) }
    s.writeJSON(w, http.StatusOK, out)
}

// --- /api/v1/snippet ---
func (s *Server) handleSnippet(w http.ResponseWriter, r *http.Request) {
    var req snippetRequest
    if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
        s.writeError(w, http.StatusBadRequest, "Invalid request body: "+err.Error())
        return
    }
    if req.File == "" { s.writeError(w, http.StatusBadRequest, "file required"); return }

    ctx := r.Context()
    // Fast path: read from storage by path
    doc, err := s.storage.GetDocumentByPath(ctx, req.File)
    if err != nil || doc == nil { s.writeError(w, http.StatusNotFound, "file not indexed: "+req.File); return }

    lines := strings.Split(doc.Content, "\n")
    // clamp indices
    sLine := req.Start.Line; eLine := req.End.Line
    if sLine < 0 { sLine = 0 }
    if eLine <= 0 || eLine > len(lines) { eLine = len(lines) }
    if sLine > eLine { sLine, eLine = eLine, sLine }

    snippet := strings.Join(lines[sLine:eLine], "\n")
    s.writeJSON(w, http.StatusOK, snippetResponse{ Snippet: snippet })
}
```

> Note: `/rank` returns packed content from your pipeline (already token‑budgeted). `/snippet` gives precise ranges if the client passes `start/end` (line/character). If you want character‑accurate slicing, extend to compute rune offsets; current implementation slices by lines.

### 2.3 Imports (if missing)

At the top of `internal/api/server.go`, ensure these imports exist:

```go
import (
    "encoding/json"
    "net/http"
    "strings"
    // ... existing
    "go.uber.org/zap"
    "contextlite/pkg/types"
)
```

If `zap` or `types` are already imported, keep only one import block.

---

## 3) Storage addition: GetDocumentByPath

**File:** `internal/storage/sqlite.go`

Add this method anywhere after existing methods:

```go
func (s *Storage) GetDocumentByPath(ctx context.Context, path string) (*types.Document, error) {
    var doc types.Document
    err := s.db.QueryRowContext(ctx, `
        SELECT id, content, content_hash, path, lang, mtime,
               token_count, model_id, quantum_score, entanglement_map,
               coherence_history, created_at, updated_at
        FROM documents WHERE path = ? LIMIT 1`, path).Scan(
        &doc.ID, &doc.Content, &doc.ContentHash, &doc.Path, &doc.Language,
        &doc.ModifiedTime, &doc.TokenCount, &doc.ModelID, &doc.QuantumScore,
        &doc.Entanglement, &doc.Coherence, &doc.CreatedAt, &doc.UpdatedAt)
    if err != nil { return nil, err }
    return &doc, nil
}
```

Add a quick test (optional) to `internal/storage/storage_test.go` mirroring `TestStorage_GetDocument` but searching by `Path`.

---

## 4) Python Adapters

Create new tree:

```
adapters/python/contextlite_langchain/
  ├─ pyproject.toml
  ├─ README.md
  └─ contextlite_langchain/__init__.py
  └─ contextlite_langchain/retriever.py

adapters/python/contextlite_llamaindex/
  ├─ pyproject.toml
  ├─ README.md
  └─ contextlite_llamaindex/__init__.py
  └─ contextlite_llamaindex/retriever.py
```

### 4.1 LangChain retriever

``

```toml
[project]
name = "contextlite-langchain"
version = "0.1.0"
description = "LangChain retriever for ContextLite"
requires-python = ">=3.9"
dependencies = ["requests>=2", "langchain>=0.2"]

[build-system]
requires = ["setuptools", "wheel"]
build-backend = "setuptools.build_meta"
```

``

```python
from .retriever import ContextLiteRetriever
```

``

```python
from __future__ import annotations
from typing import List, Optional
import os, requests
from langchain.retrievers import BaseRetriever
from langchain.schema import Document

class ContextLiteRetriever(BaseRetriever):
    def __init__(self, base_url: str = "http://localhost:8765", k: int = 6, budget_ms: int = 80, token: Optional[str] = None):
        self.base_url = base_url.rstrip("/")
        self.k = k
        self.budget_ms = budget_ms
        self.token = token or os.getenv("CONTEXTLITE_TOKEN") or os.getenv("CONTEXTLITE_AUTH_TOKEN")

    def _headers(self):
        h = {"content-type": "application/json"}
        if self.token:
            h["authorization"] = f"Bearer {self.token}"
        return h

    def _get_relevant_documents(self, query: str) -> List[Document]:
        r = requests.post(f"{self.base_url}/api/v1/rank", json={"query": query, "k": self.k, "budget_ms": self.budget_ms}, headers=self._headers(), timeout=15)
        r.raise_for_status()
        data = r.json()
        docs: List[Document] = []
        for it in data.get("items", []):
            meta = {"file": it.get("file"), "range": it.get("range"), "score": it.get("score"), "why": it.get("why")}
            docs.append(Document(page_content=it.get("snippet", ""), metadata=meta))
        return docs

    async def _aget_relevant_documents(self, query: str) -> List[Document]:
        # Optional: implement with httpx for async
        return self._get_relevant_documents(query)
```

``

```md
pip install -e adapters/python/contextlite_langchain

from contextlite_langchain import ContextLiteRetriever
retr = ContextLiteRetriever(base_url="http://localhost:8765", k=6)
retr.get_relevant_documents("explain payment capture flow")
```

### 4.2 LlamaIndex retriever

``

```toml
[project]
name = "contextlite-llamaindex"
version = "0.1.0"
description = "LlamaIndex retriever for ContextLite"
requires-python = ">=3.9"
dependencies = ["requests>=2", "llama-index-core>=0.10"]

[build-system]
requires = ["setuptools", "wheel"]
build-backend = "setuptools.build_meta"
```

``

```python
from .retriever import ContextLiteRetriever
```

``

```python
from __future__ import annotations
from typing import List, Optional
import os, requests
from llama_index.core.retrievers import BaseRetriever
from llama_index.core.schema import NodeWithScore, TextNode

class ContextLiteRetriever(BaseRetriever):
    def __init__(self, base_url: str = "http://localhost:8765", k: int = 6, budget_ms: int = 80, token: Optional[str] = None):
        self.base_url = base_url.rstrip("/")
        self.k = k
        self.budget_ms = budget_ms
        self.token = token or os.getenv("CONTEXTLITE_TOKEN") or os.getenv("CONTEXTLITE_AUTH_TOKEN")

    def _headers(self):
        h = {"content-type": "application/json"}
        if self.token:
            h["authorization"] = f"Bearer {self.token}"
        return h

    def _retrieve(self, query: str) -> List[NodeWithScore]:
        r = requests.post(f"{self.base_url}/api/v1/rank", json={"query": query, "k": self.k, "budget_ms": self.budget_ms}, headers=self._headers(), timeout=15)
        r.raise_for_status()
        data = r.json()
        out: List[NodeWithScore] = []
        for it in data.get("items", []):
            node = TextNode(text=it.get("snippet", ""), metadata={"file": it.get("file"), "range": it.get("range"), "why": it.get("why")})
            out.append(NodeWithScore(node=node, score=it.get("score", 0.0)))
        return out
```

---

## 5) Node MCP Server

Create:

```
adapters/node/mcp-server/
  ├─ package.json
  ├─ tsconfig.json
  └─ src/index.ts
```

``

```json
{
  "name": "contextlite-mcp",
  "version": "0.1.0",
  "bin": { "contextlite-mcp": "dist/index.js" },
  "type": "module",
  "scripts": {
    "build": "tsc -p .",
    "start": "node dist/index.js"
  },
  "dependencies": {
    "@modelcontextprotocol/sdk": "^0.5.0",
    "node-fetch": "^3.3.2"
  },
  "devDependencies": {
    "typescript": "^5.6.2"
  }
}
```

``

```json
{ "compilerOptions": { "outDir": "dist", "target": "ES2022", "module": "ES2022", "moduleResolution": "Bundler", "strict": true, "esModuleInterop": true }, "include": ["src"] }
```

``

```ts
import { Server } from "@modelcontextprotocol/sdk/server";
import fetch from "node-fetch";

const BASE = process.env.CONTEXTLITE_URL || "http://localhost:8765";
const TOKEN = process.env.CONTEXTLITE_TOKEN || process.env.CONTEXTLITE_AUTH_TOKEN;

async function call(path: string, body: any) {
  const r = await fetch(`${BASE}${path}`, {
    method: "POST",
    headers: {
      "content-type": "application/json",
      ...(TOKEN ? { authorization: `Bearer ${TOKEN}` } : {}),
    },
    body: JSON.stringify(body),
  });
  if (!r.ok) throw new Error(`${path} ${r.status}`);
  return r.json();
}

const server = new Server({ name: "contextlite", version: "0.1.0" });

server.tool("search", { query: "string", k: { type: "number", optional: true } }, async ({ query, k }) => {
  const data = await call("/api/v1/rank", { query, k: k ?? 6, budget_ms: 80 });
  return data.items || [];
});

server.tool("fetch", { file: "string", start: { type: "object" }, end: { type: "object" } }, async (args) => {
  return await call("/api/v1/snippet", args);
});

server.start();
```

Usage:

```bash
cd adapters/node/mcp-server && npm i && npm run build
CONTEXTLITE_URL=http://localhost:8765 CONTEXTLITE_TOKEN=yourtoken npx contextlite-mcp
```

---

## 6) Go Adapter (client + LangChainGo retriever)

Create:

```
adapters/go/contextlite/
  ├─ go.mod
  ├─ client.go
  ├─ retriever_langchaingo.go
  └─ README.md
```

`` *(replace module path if you publish under your GitHub org)*

```go
module github.com/yourorg/contextlite/adapters/go/contextlite

go 1.22

require (
    github.com/tmc/langchaingo v0.1.0 // indirect ok if you don’t use directly here
)
```

``

```go
package contextlite

import (
    "bytes"
    "context"
    "encoding/json"
    "errors"
    "net/http"
    "os"
    "time"
)

type Client struct {
    base   string
    http   *http.Client
    token  string
}

type Position struct { Line int `json:"line"`; Character int `json:"character"` }

type Range struct { Start Position `json:"start"`; End Position `json:"end"` }

type RankItem struct {
    File    string   `json:"file"`
    Range   *Range   `json:"range,omitempty"`
    Snippet string   `json:"snippet"`
    Score   float64  `json:"score"`
    Why     string   `json:"why"`
}

type rankResp struct { Items []RankItem `json:"items"`; P99Ms int `json:"p99_ms"` }

type rankReq struct { Query string `json:"query"`; K int `json:"k"`; BudgetMs int `json:"budget_ms"`; MaxTokens int `json:"max_tokens,omitempty"` }

type snippetReq struct { File string `json:"file"`; Start Position `json:"start"`; End Position `json:"end"` }

type snippetResp struct { Snippet string `json:"snippet"` }

func New(baseURL string) *Client {
    return &Client{
        base: baseURL,
        http: &http.Client{ Timeout: 15 * time.Second },
        token: os.Getenv("CONTEXTLITE_TOKEN"),
    }
}

func (c *Client) headers() http.Header {
    h := http.Header{}
    h.Set("content-type", "application/json")
    if t := c.token; t != "" { h.Set("authorization", "Bearer "+t) }
    return h
}

func (c *Client) Rank(ctx context.Context, query string, k, budgetMS, maxTokens int) ([]RankItem, error) {
    body, _ := json.Marshal(rankReq{ Query: query, K: k, BudgetMs: budgetMS, MaxTokens: maxTokens })
    req, _ := http.NewRequestWithContext(ctx, http.MethodPost, c.base+"/api/v1/rank", bytes.NewReader(body))
    req.Header = c.headers()
    resp, err := c.http.Do(req)
    if err != nil { return nil, err }
    defer resp.Body.Close()
    if resp.StatusCode != 200 { return nil, errors.New(resp.Status) }
    var rr rankResp
    if err := json.NewDecoder(resp.Body).Decode(&rr); err != nil { return nil, err }
    return rr.Items, nil
}

func (c *Client) Snippet(ctx context.Context, file string, start, end Position) (string, error) {
    body, _ := json.Marshal(snippetReq{ File: file, Start: start, End: end })
    req, _ := http.NewRequestWithContext(ctx, http.MethodPost, c.base+"/api/v1/snippet", bytes.NewReader(body))
    req.Header = c.headers()
    resp, err := c.http.Do(req)
    if err != nil { return "", err }
    defer resp.Body.Close()
    if resp.StatusCode != 200 { return "", errors.New(resp.Status) }
    var sr snippetResp
    if err := json.NewDecoder(resp.Body).Decode(&sr); err != nil { return "", err }
    return sr.Snippet, nil
}
```

`` *(optional if you plan to wire to LangChainGo)*

```go
package contextlite

import (
    "context"
    lc "github.com/tmc/langchaingo/schema"
)

type Retriever struct {
    Client    *Client
    K         int
    BudgetMS  int
    MaxTokens int
}

func (r *Retriever) GetRelevantDocuments(ctx context.Context, query string) ([]*lc.Document, error) {
    items, err := r.Client.Rank(ctx, query, r.K, r.BudgetMS, r.MaxTokens)
    if err != nil { return nil, err }
    docs := make([]*lc.Document, 0, len(items))
    for _, it := range items {
        docs = append(docs, &lc.Document{ PageContent: it.Snippet, Metadata: map[string]any{ "file": it.File, "range": it.Range, "score": it.Score, "why": it.Why } })
    }
    return docs, nil
}
```

``

```md
go get github.com/yourorg/contextlite/adapters/go/contextlite

cli := contextlite.New("http://localhost:8765")
retr := &contextlite.Retriever{ Client: cli, K: 6, BudgetMS: 80, MaxTokens: 2048 }
retr.GetRelevantDocuments(context.Background(), "where is token refreshed?")
```

---

## 7) Rust Adapter (crate)

Create:

```
adapters/rust/contextlite/
  ├─ Cargo.toml
  └─ src/
     ├─ lib.rs
     ├─ client.rs
     └─ retriever.rs
```

``

```toml
[package]
name = "contextlite"
version = "0.1.0"
edition = "2021"

[dependencies]
anyhow = "1"
serde = { version = "1", features = ["derive"] }
serde_json = "1"
reqwest = { version = "0.12", features = ["json", "gzip", "brotli", "deflate", "rustls-tls"] }
async-trait = "0.1"
```

``

```rust
pub mod client;
pub mod retriever;
```

``

```rust
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Clone, Debug, Default)]
pub struct Position { pub line: i32, pub character: i32 }
#[derive(Serialize, Deserialize, Clone, Debug, Default)]
pub struct Range { pub start: Position, pub end: Position }
#[derive(Serialize, Deserialize, Clone, Debug, Default)]
pub struct Item { pub file: String, pub range: Option<Range>, pub snippet: String, pub score: f32, pub why: String }

#[derive(Clone)]
pub struct Client { base: reqwest::Url, http: reqwest::Client, token: Option<String> }

impl Client {
    pub fn new(base_url: &str) -> anyhow::Result<Self> {
        Ok(Self { base: reqwest::Url::parse(base_url)?, http: reqwest::Client::new(), token: std::env::var("CONTEXTLITE_TOKEN").ok() })
    }
    pub async fn rank(&self, query: &str, k: usize, budget_ms: u32, max_tokens: Option<u32>) -> anyhow::Result<Vec<Item>> {
        #[derive(Serialize)] struct Req<'a>{ query: &'a str, k: usize, budget_ms: u32, #[serde(skip_serializing_if="Option::is_none")] max_tokens: Option<u32> }
        #[derive(Deserialize)] struct Resp{ items: Vec<Item> }
        let mut url = self.base.clone(); url.set_path("/api/v1/rank");
        let mut req = self.http.post(url).json(&Req{ query, k, budget_ms, max_tokens });
        if let Some(t) = &self.token { req = req.header("authorization", format!("Bearer {}", t)); }
        let r = req.send().await?; if !r.status().is_success() { anyhow::bail!("rank: {}", r.status()); }
        Ok(r.json::<Resp>().await?.items)
    }
    pub async fn snippet(&self, file: &str, start: Position, end: Position) -> anyhow::Result<String> {
        #[derive(Serialize)] struct Req<'a>{ file: &'a str, start: Position, end: Position }
        #[derive(Deserialize)] struct Resp{ snippet: String }
        let mut url = self.base.clone(); url.set_path("/api/v1/snippet");
        let mut req = self.http.post(url).json(&Req{ file, start, end });
        if let Some(t) = &self.token { req = req.header("authorization", format!("Bearer {}", t)); }
        let r = req.send().await?; if !r.status().is_success() { anyhow::bail!("snippet: {}", r.status()); }
        Ok(r.json::<Resp>().await?.snippet)
    }
}
```

``

```rust
use crate::client::{Client, Item};
use async_trait::async_trait;
use serde_json::json;

pub struct Document { pub text: String, pub metadata: serde_json::Value }

#[async_trait]
pub trait Retriever { async fn retrieve(&self, query: &str) -> anyhow::Result<Vec<Document>>; }

pub struct ContextLiteRetriever { pub client: Client, pub k: usize, pub budget_ms: u32, pub max_tokens: Option<u32> }

#[async_trait]
impl Retriever for ContextLiteRetriever {
    async fn retrieve(&self, query: &str) -> anyhow::Result<Vec<Document>> {
        let items: Vec<Item> = self.client.rank(query, self.k, self.budget_ms, self.max_tokens).await?;
        Ok(items.into_iter().map(|it| Document{ text: it.snippet, metadata: json!({"file": it.file, "range": it.range, "score": it.score, "why": it.why}) }).collect())
    }
}
```

---

## 8) README update (server + adapters)

Append to `README.md` (or create `CONTEXTLITE_RAG.md`):

````md
# ContextLite RAG Drop‑In

## Server
```bash
go build -o bin/contextlite ./cmd/contextlite
CONTEXTLITE_AUTH_TOKEN=devtoken ./bin/contextlite serve
````

## Python (LangChain)

```python
from contextlite_langchain import ContextLiteRetriever
retr = ContextLiteRetriever(base_url="http://localhost:8765", k=6)
retr.get_relevant_documents("explain payment capture flow")
```

## Python (LlamaIndex)

```python
from contextlite_llamaindex import ContextLiteRetriever
retr = ContextLiteRetriever(base_url="http://localhost:8765", k=6)
retr.retrieve("where is token refreshed?")
```

## MCP

```bash
cd adapters/node/mcp-server && npm i && npm run build
CONTEXTLITE_URL=http://localhost:8765 CONTEXTLITE_TOKEN=devtoken npx contextlite-mcp
```

## Go

```go
cli := contextlite.New("http://localhost:8765")
items, _ := cli.Rank(context.Background(), "query", 6, 80, 2048)
```

## Rust

```rust
let client = contextlite::client::Client::new("http://localhost:8765")?;
let retr = contextlite::retriever::ContextLiteRetriever{ client, k:6, budget_ms:80, max_tokens:Some(2048) };
let docs = retr.retrieve("query").await?;
```

````

---
## 9) Quick Bench Scaffolding
Add a bare stub to `bench/README.md` describing P50/P95/P99 latency collection, recall@k (if you add labels), and cost.

---
## 10) Tests (optional, fast)
**File:** `internal/api/server_test.go` add table tests for `/rank` (200, missing query 400), `/snippet` (404 when missing path, 200 with synthetic doc). Use in‑memory test DB setup used elsewhere in tests.

---
## 11) Auth header
All adapters read `CONTEXTLITE_TOKEN` (or `CONTEXTLITE_AUTH_TOKEN`) and send `Authorization: Bearer <token>`. Ensure the server runs with `config.Server.AuthToken` set (env var loader already exists). If the env override is partially implemented in `pkg/config/config.go`, complete the assignment line:
```go
if token := os.Getenv("CONTEXTLITE_AUTH_TOKEN"); token != "" {
    config.Server.AuthToken = token
}
````

---

## 12) Acceptance checklist

-

---

## 13) Notes on precision

- `/rank` currently returns the **packed snippet** your pipeline already produces (good for immediate context stuffing). If you want **exact line ranges**, extend the pipeline to carry offsets (store byte offsets during harvest/FTS, map to line/column at assemble time). The current `/snippet` gives client‑requested ranges by reading the stored document text.

