# ContextLite Setup for MCP/RAG Usage

## Quick Start
1. **Extract the binaries**:
   - Windows: `contextlite.exe`
   - Linux: `contextlite-linux`

2. **Install Professional License**:
   ```bash
   # Windows
   ./contextlite.exe license install CONTEXTLITE-PRO-2025-COFOUNDER-UNLIMITED
   
   # Linux
   ./contextlite-linux license install CONTEXTLITE-PRO-2025-COFOUNDER-UNLIMITED
   ```

3. **Start ContextLite Server**:
   ```bash
   # Windows
   ./contextlite.exe
   
   # Linux
   ./contextlite-linux
   ```
   - Server runs on `http://localhost:8080`
   - API documentation: `http://localhost:8080/docs`

## MCP Integration for Claude Desktop

ContextLite works as an MCP server for Claude Desktop. Add to your Claude Desktop config:

```json
{
  "mcpServers": {
    "contextlite": {
      "command": "path/to/contextlite.exe",
      "args": ["--mcp"]
    }
  }
}
```

## RAG Storage Usage

### REST API Endpoints
- **Add documents**: `POST /api/v1/documents`
- **Query**: `POST /api/v1/query`
- **Stats**: `GET /api/v1/stats`

### Example Usage
```bash
# Add a document
curl -X POST http://localhost:8080/api/v1/documents \
  -H "Content-Type: application/json" \
  -d '{"content": "Your document content", "id": "doc1"}'

# Query for relevant content
curl -X POST http://localhost:8080/api/v1/query \
  -H "Content-Type: application/json" \
  -d '{"query": "search terms", "max_results": 10}'
```

## Professional Features Included
- ✅ Unlimited documents and workspaces
- ✅ Advanced SMT optimization engine
- ✅ Commercial usage rights
- ✅ Priority support
- ✅ Hardware-bound licensing (works across your devices)

## Support
- Documentation: https://github.com/Michael-A-Kuykendall/contextlite/wiki
- Website: https://contextlite.com
- Support: support@contextlite.com

**Note**: This is a pre-configured Professional license for cofounder use. No trial limitations.
