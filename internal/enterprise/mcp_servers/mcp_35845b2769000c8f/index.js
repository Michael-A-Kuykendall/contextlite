const express = require('express');
const app = express();
const port = process.env.MCP_PORT || 3000;

app.use(express.json());

// Health check endpoint
app.get('/health', (req, res) => {
  res.json({ status: 'healthy', server: 'slack-mcp' });
});

// MCP endpoints
app.post('/mcp/tools/send_message', (req, res) => {
  // TODO: Implement Slack message sending
  res.json({ message: 'Slack integration not implemented' });
});

app.listen(port, () => {
  console.log('Slack MCP server running on port', port);
});