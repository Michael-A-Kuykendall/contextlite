"use strict";
/**
 * ContextLite Node.js Client
 *
 * Provides a high-level Node.js interface to interact with ContextLite server.
 */
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.ContextLiteClient = exports.ServerError = exports.BinaryNotFoundError = exports.ContextLiteError = void 0;
exports.withContextLiteClient = withContextLiteClient;
const node_fetch_1 = __importDefault(require("node-fetch"));
const child_process_1 = require("child_process");
const binary_manager_1 = require("./binary-manager");
class ContextLiteError extends Error {
    constructor(message) {
        super(message);
        this.name = 'ContextLiteError';
    }
}
exports.ContextLiteError = ContextLiteError;
class BinaryNotFoundError extends ContextLiteError {
    constructor(message = 'ContextLite binary not found') {
        super(message);
        this.name = 'BinaryNotFoundError';
    }
}
exports.BinaryNotFoundError = BinaryNotFoundError;
class ServerError extends ContextLiteError {
    constructor(message) {
        super(message);
        this.name = 'ServerError';
    }
}
exports.ServerError = ServerError;
class ContextLiteClient {
    constructor(options = {}) {
        this.host = options.host || 'localhost';
        this.port = options.port || 8080;
        this.autoStart = options.autoStart !== false;
        this.databasePath = options.databasePath;
        this.timeout = options.timeout || 30000;
        this.baseUrl = `http://${this.host}:${this.port}`;
        this.binaryManager = new binary_manager_1.BinaryManager();
        if (this.autoStart) {
            this.ensureServerRunning();
        }
    }
    /**
     * Ensure ContextLite server is running.
     */
    async ensureServerRunning() {
        if (await this.isServerRunning()) {
            return true;
        }
        if (!this.autoStart) {
            return false;
        }
        const binaryPath = await this.binaryManager.getBinaryPath();
        if (!binaryPath) {
            throw new BinaryNotFoundError('ContextLite binary not found. Please install it first or set autoStart=false.');
        }
        return this.startServer(binaryPath);
    }
    /**
     * Check if ContextLite server is running and responsive.
     */
    async isServerRunning() {
        try {
            const controller = new AbortController();
            const timeoutId = setTimeout(() => controller.abort(), 2000);
            const response = await (0, node_fetch_1.default)(`${this.baseUrl}/health`, {
                signal: controller.signal
            });
            clearTimeout(timeoutId);
            return response.ok;
        }
        catch {
            return false;
        }
    }
    /**
     * Start ContextLite server process.
     */
    async startServer(binaryPath) {
        try {
            const args = [];
            if (this.databasePath) {
                args.push('--database', this.databasePath);
            }
            if (this.port !== 8080) {
                args.push('--port', this.port.toString());
            }
            this.serverProcess = (0, child_process_1.spawn)(binaryPath, args, {
                stdio: ['ignore', 'pipe', 'pipe']
            });
            // Wait for server to be ready
            for (let i = 0; i < 30; i++) {
                if (await this.isServerRunning()) {
                    return true;
                }
                await new Promise(resolve => setTimeout(resolve, 1000));
            }
            throw new ServerError('Server failed to start within timeout');
        }
        catch (error) {
            throw new ServerError(`Failed to start ContextLite server: ${error}`);
        }
    }
    /**
     * Add a document to ContextLite.
     */
    async addDocument(content, documentId, metadata) {
        const payload = { content };
        if (documentId) {
            payload.id = documentId;
        }
        if (metadata) {
            payload.metadata = metadata;
        }
        return this.post('/documents', payload);
    }
    /**
     * Query ContextLite for relevant documents.
     */
    async query(query, options = {}) {
        const params = new URLSearchParams({ q: query });
        if (options.maxResults !== undefined) {
            params.append('max_results', options.maxResults.toString());
        }
        if (options.minScore !== undefined) {
            params.append('min_score', options.minScore.toString());
        }
        return this.get(`/query?${params.toString()}`);
    }
    /**
     * Get a specific document by ID.
     */
    async getDocument(documentId) {
        return this.get(`/documents/${encodeURIComponent(documentId)}`);
    }
    /**
     * Delete a document by ID.
     */
    async deleteDocument(documentId) {
        return this.delete(`/documents/${encodeURIComponent(documentId)}`);
    }
    /**
     * Get ContextLite statistics.
     */
    async getStats() {
        return this.get('/stats');
    }
    /**
     * Stop managed server and cleanup resources.
     */
    async close() {
        if (this.serverProcess) {
            try {
                this.serverProcess.kill('SIGTERM');
                // Wait for graceful shutdown
                await new Promise((resolve) => {
                    const timeout = setTimeout(() => {
                        this.serverProcess?.kill('SIGKILL');
                        resolve(undefined);
                    }, 5000);
                    this.serverProcess?.on('exit', () => {
                        clearTimeout(timeout);
                        resolve(undefined);
                    });
                });
            }
            catch {
                // Ignore cleanup errors
            }
            this.serverProcess = undefined;
        }
    }
    /**
     * Make GET request to ContextLite server.
     */
    async get(endpoint) {
        return this.request('GET', endpoint);
    }
    /**
     * Make POST request to ContextLite server.
     */
    async post(endpoint, data) {
        return this.request('POST', endpoint, {
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(data)
        });
    }
    /**
     * Make DELETE request to ContextLite server.
     */
    async delete(endpoint) {
        return this.request('DELETE', endpoint);
    }
    /**
     * Make HTTP request to ContextLite server.
     */
    async request(method, endpoint, options = {}) {
        if (!(await this.ensureServerRunning())) {
            throw new ServerError('ContextLite server is not running');
        }
        const url = `${this.baseUrl}${endpoint}`;
        const controller = new AbortController();
        const timeoutId = setTimeout(() => controller.abort(), this.timeout);
        try {
            const response = await (0, node_fetch_1.default)(url, {
                method,
                signal: controller.signal,
                ...options
            });
            clearTimeout(timeoutId);
            if (!response.ok) {
                throw new ServerError(`HTTP ${response.status}: ${response.statusText}`);
            }
            return await response.json();
        }
        catch (error) {
            clearTimeout(timeoutId);
            if (error instanceof Error) {
                if (error.name === 'AbortError') {
                    throw new ServerError('Request timeout');
                }
                throw new ServerError(`Request failed: ${error.message}`);
            }
            throw new ServerError('Request failed with unknown error');
        }
    }
}
exports.ContextLiteClient = ContextLiteClient;
/**
 * Create a ContextLite client with automatic cleanup.
 */
async function withContextLiteClient(options, callback) {
    const client = new ContextLiteClient(options);
    try {
        return await callback(client);
    }
    finally {
        await client.close();
    }
}
//# sourceMappingURL=index.js.map