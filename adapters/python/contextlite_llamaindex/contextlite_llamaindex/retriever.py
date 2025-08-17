from __future__ import annotations
from typing import List, Optional
import os, requests
from llama_index.core.retrievers import BaseRetriever
from llama_index.core.schema import NodeWithScore, TextNode

class ContextLiteRetriever(BaseRetriever):
    def __init__(self, base_url: str = "http://localhost:8080", k: int = 6, budget_ms: int = 80, token: Optional[str] = None):
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
