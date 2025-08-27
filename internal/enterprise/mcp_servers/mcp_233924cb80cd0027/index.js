const express = require('express');
const app = express();
const port = process.env.MCP_PORT || 3000;

app.use(express.json());

// Health check endpoint
app.get('/health', (req, res) => {
  res.json({ status: 'healthy', server: 'jira-mcp' });
});

// MCP endpoints
app.post('/mcp/tools/search_issues', (req, res) => {
  // TODO: Implement Jira issue search
  res.json({ message: 'Jira search not implemented' });
});

app.listen(port, () => {
  console.log('Jira MCP server running on port', port);
});