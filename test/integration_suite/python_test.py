#!/usr/bin/env python3
"""
ContextLite Python Integration Tests

Tests the Python client integration with ContextLite server.
Requires ContextLite server running on localhost:8083.
"""

import json
import requests
import time
import unittest
from typing import Dict, List, Any


class ContextLitePythonClient:
    """Simple Python client for ContextLite API testing."""
    
    def __init__(self, base_url: str = "http://localhost:8083"):
        self.base_url = base_url.rstrip('/')
        self.session = requests.Session()
    
    def health_check(self) -> bool:
        """Check if the server is healthy."""
        try:
            response = self.session.get(f"{self.base_url}/health", timeout=5)
            return response.status_code == 200
        except requests.RequestException:
            return False
    
    def index_document(self, doc_id: str, content: str, metadata: Dict[str, Any] = None) -> bool:
        """Index a document."""
        payload = {
            "id": doc_id,
            "content": content,
            "metadata": metadata or {}
        }
        try:
            response = self.session.post(
                f"{self.base_url}/documents", 
                json=payload,
                timeout=10
            )
            return response.status_code in [200, 201]
        except requests.RequestException:
            return False
    
    def query_context(self, query: str, max_results: int = 5) -> Dict[str, Any]:
        """Query for relevant context."""
        payload = {
            "query": query,
            "max_results": max_results
        }
        try:
            response = self.session.post(
                f"{self.base_url}/query",
                json=payload,
                timeout=10
            )
            if response.status_code == 200:
                return response.json()
            return {}
        except requests.RequestException:
            return {}


class TestContextLitePythonIntegration(unittest.TestCase):
    """Integration tests for ContextLite Python client."""
    
    @classmethod
    def setUpClass(cls):
        """Set up test class."""
        cls.client = ContextLitePythonClient()
        cls.test_docs = [
            {
                "id": "python_test_1",
                "content": "Python is a high-level programming language with dynamic semantics.",
                "metadata": {"language": "python", "type": "definition"}
            },
            {
                "id": "python_test_2", 
                "content": "Machine learning algorithms can be implemented efficiently in Python using libraries like scikit-learn.",
                "metadata": {"language": "python", "type": "application"}
            }
        ]
    
    def test_01_server_health(self):
        """Test that the server is healthy and responding."""
        health = self.client.health_check()
        self.assertTrue(health, "ContextLite server should be healthy")
    
    def test_02_document_indexing(self):
        """Test document indexing functionality."""
        for doc in self.test_docs:
            success = self.client.index_document(
                doc["id"], 
                doc["content"], 
                doc["metadata"]
            )
            self.assertTrue(success, f"Should successfully index document {doc['id']}")
        
        # Allow time for indexing
        time.sleep(1)
    
    def test_03_context_search(self):
        """Test context search functionality."""
        result = self.client.query_context("Python programming language")
        self.assertIsInstance(result, dict, "Query result should be a dictionary")
        
        if "documents" in result:
            documents = result["documents"]
            self.assertIsInstance(documents, list, "Documents should be a list")
            self.assertGreater(len(documents), 0, "Should find relevant documents")


def run_integration_tests():
    """Run all integration tests."""
    print("=" * 60)
    print("ContextLite Python Integration Tests")
    print("=" * 60)
    
    # Check server availability first
    client = ContextLitePythonClient()
    if not client.health_check():
        print("‚ùå ERROR: ContextLite server not responding on localhost:8083")
        print("Please start the server with: ./build/contextlite")
        return False
    
    print("‚úÖ Server health check passed")
    
    # Run the test suite
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromTestCase(TestContextLitePythonIntegration)
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    success = len(result.failures) == 0 and len(result.errors) == 0
    if success:
        print("\nÌæâ All Python integration tests passed!")
    else:
        print(f"\n‚ùå Python integration tests failed")
    
    return success


if __name__ == "__main__":
    run_integration_tests()
