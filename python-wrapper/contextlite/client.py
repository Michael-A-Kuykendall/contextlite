"""
ContextLite Python Client

Provides a high-level Python interface to interact with ContextLite server.
"""

import json
import subprocess
import time
import requests
from pathlib import Path
from typing import Dict, List, Optional, Any, Union
from contextlib import contextmanager

from .binary_manager import BinaryManager
from .exceptions import ContextLiteError, ServerError, BinaryNotFoundError


class ContextLiteClient:
    """
    High-level Python client for ContextLite.
    
    This client can either connect to an existing ContextLite server or
    automatically manage a local server instance.
    """
    
    def __init__(
        self,
        host: str = "localhost",
        port: int = 8080,
        auto_start: bool = True,
        database_path: Optional[str] = None,
        timeout: float = 30.0
    ):
        """
        Initialize ContextLite client.
        
        Args:
            host: Server host (default: localhost)
            port: Server port (default: 8080)
            auto_start: Whether to auto-start server if not running
            database_path: Path to database file (optional)
            timeout: Request timeout in seconds
        """
        self.host = host
        self.port = port
        self.auto_start = auto_start
        self.database_path = database_path
        self.timeout = timeout
        self.base_url = f"http://{host}:{port}"
        
        self._server_process = None
        self._binary_manager = BinaryManager()
        
        if auto_start:
            self.ensure_server_running()
            
    def __enter__(self):
        """Context manager entry."""
        return self
        
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit - cleanup server if we started it."""
        self.close()
        
    def close(self):
        """Stop managed server and cleanup resources."""
        if self._server_process:
            try:
                self._server_process.terminate()
                self._server_process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self._server_process.kill()
            except Exception:
                pass
            self._server_process = None
            
    def ensure_server_running(self) -> bool:
        """
        Ensure ContextLite server is running.
        
        Returns:
            True if server is running, False otherwise
            
        Raises:
            BinaryNotFoundError: If binary not found and auto_start is True
            ServerError: If server fails to start
        """
        if self.is_server_running():
            return True
            
        if not self.auto_start:
            return False
            
        # Get binary path
        binary_path = self._binary_manager.get_binary_path()
        if not binary_path:
            raise BinaryNotFoundError(
                "ContextLite binary not found. Please install it first or set auto_start=False."
            )
            
        # Start server
        return self._start_server(binary_path)
        
    def is_server_running(self) -> bool:
        """Check if ContextLite server is running and responsive."""
        try:
            response = requests.get(f"{self.base_url}/health", timeout=2)
            return response.status_code == 200
        except requests.RequestException:
            return False
            
    def _start_server(self, binary_path: Path) -> bool:
        """Start ContextLite server process."""
        try:
            cmd = [str(binary_path)]
            
            # Add database path if specified
            if self.database_path:
                cmd.extend(["--database", self.database_path])
                
            # Add port if non-default
            if self.port != 8080:
                cmd.extend(["--port", str(self.port)])
                
            # Start server process
            self._server_process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
            
            # Wait for server to be ready
            for _ in range(30):  # Wait up to 30 seconds
                if self.is_server_running():
                    return True
                time.sleep(1)
                
            # If we reach here, server didn't start properly
            stdout, stderr = self._server_process.communicate(timeout=5)
            raise ServerError(f"Server failed to start. Error: {stderr}")
            
        except Exception as e:
            raise ServerError(f"Failed to start ContextLite server: {e}")
            
    def add_document(
        self,
        content: str,
        document_id: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """
        Add a document to ContextLite.
        
        Args:
            content: Document content
            document_id: Optional document ID (auto-generated if not provided)
            metadata: Optional metadata dictionary
            
        Returns:
            Response from server
            
        Raises:
            ServerError: If request fails
        """
        payload = {"content": content}
        
        if document_id:
            payload["id"] = document_id
            
        if metadata:
            payload["metadata"] = metadata
            
        return self._post("/documents", payload)
        
    def query(
        self,
        query: str,
        max_results: Optional[int] = None,
        min_score: Optional[float] = None
    ) -> Dict[str, Any]:
        """
        Query ContextLite for relevant documents.
        
        Args:
            query: Search query
            max_results: Maximum number of results (optional)
            min_score: Minimum relevance score (optional)
            
        Returns:
            Query results
            
        Raises:
            ServerError: If request fails
        """
        params = {"q": query}
        
        if max_results is not None:
            params["max_results"] = max_results
            
        if min_score is not None:
            params["min_score"] = min_score
            
        return self._get("/query", params)
        
    def get_document(self, document_id: str) -> Dict[str, Any]:
        """
        Get a specific document by ID.
        
        Args:
            document_id: Document ID
            
        Returns:
            Document data
            
        Raises:
            ServerError: If request fails
        """
        return self._get(f"/documents/{document_id}")
        
    def delete_document(self, document_id: str) -> Dict[str, Any]:
        """
        Delete a document by ID.
        
        Args:
            document_id: Document ID
            
        Returns:
            Deletion confirmation
            
        Raises:
            ServerError: If request fails
        """
        return self._delete(f"/documents/{document_id}")
        
    def get_stats(self) -> Dict[str, Any]:
        """
        Get ContextLite statistics.
        
        Returns:
            Statistics data
            
        Raises:
            ServerError: If request fails
        """
        return self._get("/stats")
        
    def _get(self, endpoint: str, params: Optional[Dict] = None) -> Dict[str, Any]:
        """Make GET request to ContextLite server."""
        return self._request("GET", endpoint, params=params)
        
    def _post(self, endpoint: str, data: Dict[str, Any]) -> Dict[str, Any]:
        """Make POST request to ContextLite server."""
        return self._request("POST", endpoint, json=data)
        
    def _delete(self, endpoint: str) -> Dict[str, Any]:
        """Make DELETE request to ContextLite server."""
        return self._request("DELETE", endpoint)
        
    def _request(
        self,
        method: str,
        endpoint: str,
        params: Optional[Dict] = None,
        json: Optional[Dict] = None
    ) -> Dict[str, Any]:
        """Make HTTP request to ContextLite server."""
        if not self.ensure_server_running():
            raise ServerError("ContextLite server is not running")
            
        url = f"{self.base_url}{endpoint}"
        
        try:
            response = requests.request(
                method=method,
                url=url,
                params=params,
                json=json,
                timeout=self.timeout
            )
            response.raise_for_status()
            return response.json()
            
        except requests.RequestException as e:
            raise ServerError(f"Request failed: {e}")
        except ValueError as e:
            raise ServerError(f"Invalid JSON response: {e}")


@contextmanager
def contextlite_client(*args, **kwargs):
    """
    Context manager for ContextLite client.
    
    Example:
        with contextlite_client() as client:
            client.add_document("Hello world!")
            results = client.query("hello")
    """
    client = ContextLiteClient(*args, **kwargs)
    try:
        yield client
    finally:
        client.close()
