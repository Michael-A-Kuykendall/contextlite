from __future__ import annotations
from typing import List, Optional
import os, requests
from langchain.retrievers import BaseRetriever
from langchain.schema import Document

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
