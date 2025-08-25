"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const express_1 = __importDefault(require("express"));
const http_1 = require("http");
const socket_io_1 = require("socket.io");
const cors_1 = __importDefault(require("cors"));
const helmet_1 = __importDefault(require("helmet"));
const rate_limiter_flexible_1 = require("rate-limiter-flexible");
const app = (0, express_1.default)();
const server = (0, http_1.createServer)(app);
const io = new socket_io_1.Server(server, {
    cors: {
        origin: process.env.FRONTEND_URL || "http://localhost:3000",
        methods: ["GET", "POST"]
    }
});
const PORT = process.env.PORT || 3001;
// Rate limiting
const rateLimiter = new rate_limiter_flexible_1.RateLimiterMemory({
    points: 10, // 10 requests
    duration: 60, // per 60 seconds
});
// Middleware
app.use((0, helmet_1.default)());
app.use((0, cors_1.default)({
    origin: process.env.FRONTEND_URL || "http://localhost:3000"
}));
app.use(express_1.default.json());
// Rate limiting middleware
app.use(async (req, res, next) => {
    try {
        const key = req.ip || 'unknown';
        await rateLimiter.consume(key);
        next();
    }
    catch (rejRes) {
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
    // Simulate processing time
    await new Promise(resolve => setTimeout(resolve, Math.random() * 100));
    const mockResults = [
        {
            file: 'components/Button/Button.tsx',
            line: 15,
            content: 'export const Button: FC<ButtonProps> = ({ children, variant = "primary" }) => {',
            context: 'React component definition'
        },
        {
            file: 'components/Button/Button.stories.tsx',
            line: 8,
            content: 'export const PrimaryButton = () => <Button variant="primary">Click me</Button>;',
            context: 'Storybook story'
        },
        {
            file: 'components/IconButton/IconButton.tsx',
            line: 12,
            content: 'export const IconButton: FC<IconButtonProps> = ({ icon, ...props }) => {',
            context: 'Icon button component'
        }
    ];
    res.json({
        query,
        dataset,
        results: mockResults,
        timing: Math.random() * 5 + 1, // 1-6ms
        accuracy: 94,
        totalFound: mockResults.length
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
    // Simulate much slower processing
    await new Promise(resolve => setTimeout(resolve, Math.random() * 200 + 400));
    const mockResults = [
        {
            file: 'docs/authentication.md',
            line: 1,
            content: 'Authentication documentation and examples...',
            context: 'Documentation file'
        },
        {
            file: 'config/auth.yaml',
            line: 12,
            content: 'auth_provider: oauth2',
            context: 'Configuration file'
        },
        {
            file: 'tests/auth_test.go',
            line: 89,
            content: 'func TestAuthentication(t *testing.T) {',
            context: 'Test file'
        }
    ];
    res.json({
        query,
        results: mockResults,
        timing: Math.random() * 200 + 400, // 400-600ms
        accuracy: 67,
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
        }
        else if (command.startsWith('contextlite explain')) {
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
        }
        else if (command.startsWith('contextlite analyze')) {
            result = `📊 Complexity Analysis:

Components Directory:
- 47 total files
- Average complexity: Low (2.3/10)  
- Test coverage: 94%
- TypeScript usage: 100%

Maintainability Score: A+
⚡ Analysis completed in 0.2ms`;
        }
        else {
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
});
exports.default = app;
//# sourceMappingURL=server.js.map