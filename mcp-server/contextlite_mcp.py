# ContextLite MCP Server for GitHub Copilot Integration
#
# This MCP server allows GitHub Copilot to access ContextLite's RAG capabilities
# natively without monkey-patching or fragile integrations.
#
# Installation:
# 1. Install MCP CLI: npm install -g @modelcontextprotocol/cli
# 2. Configure in VS Code settings.json
# 3. ContextLite automatically provides context to Copilot

import json
import asyncio
import sqlite3
import os
import sys
from typing import Dict, List, Any, Optional
from pathlib import Path
import aiohttp
import logging
from datetime import datetime

# MCP Protocol Implementation
class ContextLiteMCPServer:
    """
    MCP Server that bridges GitHub Copilot with ContextLite's RAG storage.
    
    Key Features:
    - Provides project-specific context to Copilot
    - Stores chat history in SQLite for searchable memory
    - Auto-discovers ContextLite instances (solves port problem)
    - Works with native Copilot APIs (no monkey-patching)
    """
    
    def __init__(self, project_root: str):
        self.project_root = Path(project_root)
        self.project_name = self.project_root.name
        self.db_path = self.project_root / ".contextlite" / "copilot_memory.db"
        self.contextlite_port = None
        self.session = None
        self.setup_logging()
        self.init_database()
    
    def setup_logging(self):
        """Setup logging for MCP server."""
        log_dir = self.project_root / ".contextlite" / "logs"
        log_dir.mkdir(parents=True, exist_ok=True)
        
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
            handlers=[
                logging.FileHandler(log_dir / "mcp_server.log"),
                logging.StreamHandler()
            ]
        )
        self.logger = logging.getLogger(f"contextlite-mcp-{self.project_name}")
    
    def init_database(self):
        """Initialize SQLite database for chat memory."""
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS chat_history (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
                    session_id TEXT,
                    message_type TEXT, -- 'user', 'assistant', 'system'
                    content TEXT,
                    context_used TEXT, -- JSON of files/context provided
                    file_path TEXT,
                    project_name TEXT,
                    embedding BLOB -- Store embeddings for semantic search
                )
            """)
            
            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_timestamp ON chat_history(timestamp);
            """)
            
            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_session ON chat_history(session_id);
            """)
            
            conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_project ON chat_history(project_name);
            """)
            
            conn.execute("""
                CREATE VIRTUAL TABLE IF NOT EXISTS chat_fts USING fts5(
                    content, file_path, project_name, content=chat_history
                );
            """)
    
    async def auto_discover_contextlite(self) -> Optional[int]:
        """
        Auto-discover running ContextLite instances.
        Solves the port poker problem!
        """
        common_ports = [8080, 8081, 8082, 8083, 8084, 8085, 8086, 8087, 8088, 8089, 8090]
        
        for port in common_ports:
            try:
                async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=2)) as session:
                    async with session.get(f"http://localhost:{port}/health") as response:
                        if response.status == 200:
                            data = await response.json()
                            if "smt" in data and "database" in data:  # Confirm it's ContextLite
                                self.logger.info(f"Found ContextLite on port {port}")
                                return port
            except:
                continue
        
        return None
    
    async def start_contextlite_if_needed(self) -> bool:
        """Start ContextLite for this project if not running."""
        if self.contextlite_port:
            return True
            
        # Try to discover existing instance
        port = await self.auto_discover_contextlite()
        if port:
            self.contextlite_port = port
            return True
        
        # Start new instance for this project
        try:
            import subprocess
            import asyncio
            
            # Find available port
            for candidate_port in range(8080, 8091):
                try:
                    import socket
                    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                        s.bind(('localhost', candidate_port))
                        available_port = candidate_port
                        break
                except OSError:
                    continue
            else:
                self.logger.error("No available ports in range 8080-8090")
                return False
            
            # Create project-specific config
            config_dir = self.project_root / ".contextlite"
            config_dir.mkdir(exist_ok=True)
            
            config_file = config_dir / "config.yaml"
            with open(config_file, 'w') as f:
                f.write(f"""
# Auto-generated config for {self.project_name}
server:
  port: {available_port}
  host: "127.0.0.1"

storage:
  database_path: "{config_dir}/contextlite.db"

cluster:
  enabled: true
  node_id: "contextlite-{self.project_name}-{available_port}"
  
affinity:
  workspace_routing: true
  rules:
    "{self.project_name}":
      resource_tier: "high"
      max_memory_mb: 512
      
# Copilot-optimized settings  
performance:
  cache_embeddings: true
  enable_smart_indexing: true
  update_frequency: "on_save"

privacy:
  project_isolation: true
  exclude_patterns:
    - "*.env*"
    - "*.key"
    - "*.pem"
    - "secrets/*"
    - "node_modules/*"
    - ".git/*"
""")
            
            # Start ContextLite process
            cmd = ["contextlite", "--config", str(config_file)]
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                cwd=self.project_root
            )
            
            # Wait for startup
            await asyncio.sleep(3)
            
            # Verify it started
            port = await self.auto_discover_contextlite()
            if port:
                self.contextlite_port = port
                
                # Save port to project file for future sessions
                port_file = config_dir / "port"
                with open(port_file, 'w') as f:
                    f.write(str(port))
                
                self.logger.info(f"Started ContextLite for {self.project_name} on port {port}")
                return True
                
        except Exception as e:
            self.logger.error(f"Failed to start ContextLite: {e}")
            
        return False
    
    async def get_project_context(self, query: str, max_results: int = 10) -> List[Dict]:
        """Get relevant context from ContextLite for the current project."""
        if not await self.start_contextlite_if_needed():
            return []
        
        try:
            async with aiohttp.ClientSession() as session:
                payload = {
                    "query": query,
                    "max_documents": max_results,
                    "workspace_path": str(self.project_root),
                    "use_optimization": True
                }
                
                headers = {
                    "X-Workspace-ID": self.project_name,
                    "Content-Type": "application/json"
                }
                
                async with session.post(
                    f"http://localhost:{self.contextlite_port}/api/v1/context/assemble",
                    json=payload,
                    headers=headers
                ) as response:
                    if response.status == 200:
                        data = await response.json()
                        return data.get("documents", [])
                        
        except Exception as e:
            self.logger.error(f"Failed to get context: {e}")
            
        return []
    
    async def store_chat_interaction(self, 
                                   session_id: str,
                                   user_message: str, 
                                   assistant_response: str,
                                   context_files: List[str] = None):
        """Store chat interaction in local SQLite for searchable memory."""
        with sqlite3.connect(self.db_path) as conn:
            # Store user message
            conn.execute("""
                INSERT INTO chat_history 
                (session_id, message_type, content, context_used, project_name)
                VALUES (?, ?, ?, ?, ?)
            """, (session_id, "user", user_message, 
                  json.dumps(context_files or []), self.project_name))
            
            # Store assistant response
            conn.execute("""
                INSERT INTO chat_history 
                (session_id, message_type, content, context_used, project_name)
                VALUES (?, ?, ?, ?, ?)
            """, (session_id, "assistant", assistant_response,
                  json.dumps(context_files or []), self.project_name))
    
    async def search_chat_history(self, query: str, limit: int = 10) -> List[Dict]:
        """Search previous chat history for relevant context."""
        with sqlite3.connect(self.db_path) as conn:
            conn.row_factory = sqlite3.Row
            cursor = conn.execute("""
                SELECT * FROM chat_history 
                WHERE project_name = ? AND content MATCH ?
                ORDER BY timestamp DESC
                LIMIT ?
            """, (self.project_name, query, limit))
            
            return [dict(row) for row in cursor.fetchall()]

# MCP Protocol Implementation
class MCPServer:
    """Standard MCP server that integrates with VS Code/Copilot."""
    
    def __init__(self):
        self.contextlite = None
        
    async def handle_request(self, request: Dict) -> Dict:
        """Handle MCP protocol requests from Copilot."""
        method = request.get("method")
        params = request.get("params", {})
        
        if method == "initialize":
            return await self.handle_initialize(params)
        elif method == "textDocument/completion":
            return await self.handle_completion(params)
        elif method == "workspace/context":
            return await self.handle_workspace_context(params)
        else:
            return {"error": {"code": -32601, "message": "Method not found"}}
    
    async def handle_initialize(self, params: Dict) -> Dict:
        """Initialize MCP server for current workspace."""
        workspace_uri = params.get("workspaceFolders", [{}])[0].get("uri", "")
        if workspace_uri.startswith("file://"):
            workspace_path = workspace_uri[7:]  # Remove file:// prefix
            self.contextlite = ContextLiteMCPServer(workspace_path)
            
        return {
            "capabilities": {
                "textDocumentSync": {"openClose": True, "change": 1},
                "completionProvider": {"triggerCharacters": ["@", "#"]},
                "contextProvider": True
            }
        }
    
    async def handle_completion(self, params: Dict) -> Dict:
        """Provide context-aware completions to Copilot."""
        if not self.contextlite:
            return {"items": []}
            
        text_document = params.get("textDocument", {})
        position = params.get("position", {})
        
        # Get current line context
        uri = text_document.get("uri", "")
        if uri.startswith("file://"):
            file_path = uri[7:]
            
            try:
                with open(file_path, 'r') as f:
                    lines = f.readlines()
                    current_line = lines[position.get("line", 0)]
                    
                # Get relevant context from ContextLite
                context_docs = await self.contextlite.get_project_context(
                    current_line.strip(), max_results=5
                )
                
                # Convert to completion items
                items = []
                for doc in context_docs:
                    items.append({
                        "label": f"Context: {doc.get('path', 'Unknown')}",
                        "detail": doc.get("content", "")[:100] + "...",
                        "documentation": {
                            "kind": "markdown",
                            "value": f"```\n{doc.get('content', '')}\n```"
                        }
                    })
                
                return {"items": items}
                
            except Exception as e:
                logging.error(f"Completion error: {e}")
        
        return {"items": []}
    
    async def handle_workspace_context(self, params: Dict) -> Dict:
        """Provide workspace context to Copilot."""
        if not self.contextlite:
            return {"context": []}
            
        query = params.get("query", "")
        context_docs = await self.contextlite.get_project_context(query)
        
        return {
            "context": [
                {
                    "uri": f"file://{doc.get('path', '')}",
                    "content": doc.get("content", ""),
                    "relevance": doc.get("score", 0.5)
                }
                for doc in context_docs
            ]
        }

# Entry point for MCP server
async def main():
    """Main entry point for ContextLite MCP server."""
    server = MCPServer()
    
    # Read JSON-RPC requests from stdin
    while True:
        try:
            line = await asyncio.get_event_loop().run_in_executor(None, sys.stdin.readline)
            if not line:
                break
                
            request = json.loads(line.strip())
            response = await server.handle_request(request)
            
            # Send response to stdout
            print(json.dumps(response))
            sys.stdout.flush()
            
        except Exception as e:
            error_response = {
                "error": {"code": -32603, "message": f"Internal error: {e}"}
            }
            print(json.dumps(error_response))
            sys.stdout.flush()

if __name__ == "__main__":
    asyncio.run(main())
