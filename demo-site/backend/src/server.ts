import express from 'express';
import { createServer } from 'http';
import { Server } from 'socket.io';
import cors from 'cors';
import helmet from 'helmet';
import { RateLimiterMemory } from 'rate-limiter-flexible';
import { DEMO_FILES, DEMO_SEARCH_RESULTS, CONTEXTLITE_METRICS, VECTOR_RAG_METRICS } from './demo-data';

const app = express();
const server = createServer(app);
const io = new Server(server, {
  cors: {
    origin: process.env.FRONTEND_URL || "http://localhost:3000",
    methods: ["GET", "POST"]
  }
});

const PORT = process.env.PORT || 3001;

// Rate limiting
const rateLimiter = new RateLimiterMemory({
  points: 10, // 10 requests
  duration: 60, // per 60 seconds
});

// Middleware
app.use(helmet());
app.use(cors({
  origin: process.env.FRONTEND_URL || "http://localhost:3000"
}));
app.use(express.json());

// Rate limiting middleware
app.use(async (req, res, next) => {
  try {
    const key = req.ip || 'unknown';
    await rateLimiter.consume(key);
    next();
  } catch (rejRes) {
    res.status(429).send('Too Many Requests');
  }
});

// Health check
app.get('/health', (req, res) => {
  res.json({ status: 'ok', timestamp: new Date().toISOString() });
});

// Mock ContextLite API endpoints
app.post('/api/contextlite/search', async (req, res) => {
  const { query, dataset } = req.body;
  
  // Simulate ContextLite's blazing fast search
  await new Promise(resolve => setTimeout(resolve, Math.random() * 5));
  
  // Find matching results from demo data
  const searchKey = query.toLowerCase() as keyof typeof DEMO_SEARCH_RESULTS;
  const results = DEMO_SEARCH_RESULTS[searchKey] || [
    { file: 'No exact matches', line: 0, context: 'Try searching for: button, input field, modal dialog, data table, api client, useDebounce', relevance: 0.1 }
  ];

  res.json({
    query,
    dataset,
    results: results.map((r: any) => ({
      file: r.file,
      line: r.line,
      content: r.context,
      context: `Relevance: ${(r.relevance * 100).toFixed(1)}%`
    })),
    timing: CONTEXTLITE_METRICS.searchTime,
    accuracy: CONTEXTLITE_METRICS.accuracy,
    totalFound: results.length
  });
});

app.post('/api/contextlite/explain', async (req, res) => {
  const { path, dataset } = req.body;
  
  await new Promise(resolve => setTimeout(resolve, Math.random() * 200));
  
  res.json({
    path,
    dataset,
    explanation: {
      type: 'React Component',
      purpose: 'Reusable button component with multiple variants',
      features: [
        'TypeScript support',
        'Multiple style variants (primary, secondary, danger)',
        'Loading states',
        'Icon support',
        'Accessibility features'
      ],
      dependencies: ['React', 'Tailwind CSS'],
      usage: '<Button variant="primary" onClick={handleClick}>Text</Button>'
    },
    timing: Math.random() * 10 + 5 // 5-15ms
  });
});

app.post('/api/contextlite/analyze', async (req, res) => {
  const { path, dataset, options } = req.body;
  
  await new Promise(resolve => setTimeout(resolve, Math.random() * 300));
  
  res.json({
    path,
    dataset,
    analysis: {
      complexity: 'Low (2.3/10)',
      maintainability: 'A+',
      testCoverage: '94%',
      typeScriptUsage: '100%',
      totalFiles: 47,
      totalLines: 1243,
      issues: []
    },
    timing: Math.random() * 15 + 10 // 10-25ms
  });
});

// Mock Vector RAG comparison endpoint
app.post('/api/vector-rag/search', async (req, res) => {
  const { query } = req.body;
  
  // Simulate much slower Vector RAG processing
  await new Promise(resolve => setTimeout(resolve, VECTOR_RAG_METRICS.searchTime));
  
  // Vector RAG finds less relevant results
  const mockResults = [
    {
      file: 'docs/components.md',
      line: 1,
      content: 'Component documentation and usage examples...',
      context: 'Documentation file'
    },
    {
      file: 'README.md', 
      line: 45,
      content: 'Installation and setup instructions',
      context: 'Project readme'
    },
    {
      file: 'package.json',
      line: 12,
      content: '"dependencies": { "react": "^18.0.0" }',
      context: 'Package configuration'
    }
  ];

  res.json({
    query,
    results: mockResults,
    timing: VECTOR_RAG_METRICS.searchTime,
    accuracy: VECTOR_RAG_METRICS.accuracy,
    totalFound: mockResults.length
  });
});

// WebSocket for real-time terminal
io.on('connection', (socket) => {
  console.log('Client connected:', socket.id);
  
  socket.on('terminal-command', async (data) => {
    const { command, dataset } = data;
    
    // Simulate command execution
    await new Promise(resolve => setTimeout(resolve, 300));
    
    let result = '';
    
    if (command.startsWith('contextlite search')) {
      const query = command.match(/"([^"]+)"/)?.[1] || command.split(' ').slice(2).join(' ');
      result = `🔍 Found 3 matches in 0.3ms:

📁 components/Button/Button.tsx:15
   export const Button: FC<ButtonProps> = ({ children, variant = 'primary' }) => {

📁 components/Button/Button.stories.tsx:8  
   export const PrimaryButton = () => <Button variant="primary">Click me</Button>;

📁 components/IconButton/IconButton.tsx:12
   export const IconButton: FC<IconButtonProps> = ({ icon, ...props }) => {

💡 Try: contextlite explain components/Button/`;
    } else if (command.startsWith('contextlite explain')) {
      result = `📖 Code Analysis:

Button Component Structure:
- TypeScript React component with variants
- Supports primary, secondary, danger styles
- Uses Tailwind CSS for styling  
- Includes accessibility props (aria-label)
- Has comprehensive Storybook stories

Key Features:
- ✅ Responsive design
- ✅ Dark mode support
- ✅ Loading states
- ✅ Icon support

Usage: <Button variant="primary" onClick={handleClick}>Text</Button>`;
    } else if (command.startsWith('contextlite analyze')) {
      result = `📊 Complexity Analysis:

Components Directory:
- 47 total files
- Average complexity: Low (2.3/10)  
- Test coverage: 94%
- TypeScript usage: 100%

Maintainability Score: A+
⚡ Analysis completed in 0.2ms`;
    } else {
      result = `Unknown command: ${command}
Try: contextlite search "query", contextlite explain path/, contextlite analyze path/`;
    }
    
    socket.emit('terminal-result', { command, result });
  });
  
  socket.on('disconnect', () => {
    console.log('Client disconnected:', socket.id);
  });
});

server.listen(PORT, () => {
  console.log(`🚀 ContextLite Demo API running on port ${PORT}`);
  console.log(`🌐 Frontend URL: ${process.env.FRONTEND_URL || 'http://localhost:3000'}`);
  console.log(`📊 Demo data loaded: ${DEMO_FILES.length} files, ${Object.keys(DEMO_SEARCH_RESULTS).length} search patterns`);
});

export default app;
