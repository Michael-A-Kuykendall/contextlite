/**
 * ContextLite Node.js Client
 * 
 * Provides a high-level Node.js interface to interact with ContextLite server.
 */

import fetch from 'node-fetch';
import { spawn, ChildProcess } from 'child_process';
import { BinaryManager } from './binary-manager';

export interface Document {
    id: string;
    content: string;
    metadata?: Record<string, any>;
}

export interface QueryOptions {
    maxResults?: number;
    minScore?: number;
}

export interface QueryResult {
    documents: Array<{
        id: string;
        content: string;
        score: number;
        metadata?: Record<string, any>;
    }>;
    totalResults: number;
    queryTime: number;
}

export interface ServerStats {
    documentsCount: number;
    queriesCount: number;
    cacheHits: number;
    averageQueryTime: number;
    uptime: number;
}

export class ContextLiteError extends Error {
    constructor(message: string) {
        super(message);
        this.name = 'ContextLiteError';
    }
}

export class BinaryNotFoundError extends ContextLiteError {
    constructor(message: string = 'ContextLite binary not found') {
        super(message);
        this.name = 'BinaryNotFoundError';
    }
}

export class ServerError extends ContextLiteError {
    constructor(message: string) {
        super(message);
        this.name = 'ServerError';
    }
}

export interface ClientOptions {
    host?: string;
    port?: number;
    autoStart?: boolean;
    databasePath?: string;
    timeout?: number;
}

export class ContextLiteClient {
    private host: string;
    private port: number;
    private autoStart: boolean;
    private databasePath?: string;
    private timeout: number;
    private baseUrl: string;
    private serverProcess?: ChildProcess;
    private binaryManager: BinaryManager;

    constructor(options: ClientOptions = {}) {
        this.host = options.host || 'localhost';
        this.port = options.port || 8080;
        this.autoStart = options.autoStart !== false;
        this.databasePath = options.databasePath;
        this.timeout = options.timeout || 30000;
        this.baseUrl = `http://${this.host}:${this.port}`;
        
        this.binaryManager = new BinaryManager();
        
        if (this.autoStart) {
            this.ensureServerRunning();
        }
    }

    /**
     * Ensure ContextLite server is running.
     */
    async ensureServerRunning(): Promise<boolean> {
        if (await this.isServerRunning()) {
            return true;
        }

        if (!this.autoStart) {
            return false;
        }

        const binaryPath = await this.binaryManager.getBinaryPath();
        if (!binaryPath) {
            throw new BinaryNotFoundError(
                'ContextLite binary not found. Please install it first or set autoStart=false.'
            );
        }

        return this.startServer(binaryPath);
    }

    /**
     * Check if ContextLite server is running and responsive.
     */
    async isServerRunning(): Promise<boolean> {
        try {
            const controller = new AbortController();
            const timeoutId = setTimeout(() => controller.abort(), 2000);
            
            const response = await fetch(`${this.baseUrl}/health`, {
                signal: controller.signal
            });
            
            clearTimeout(timeoutId);
            return response.ok;
        } catch {
            return false;
        }
    }

    /**
     * Start ContextLite server process.
     */
    private async startServer(binaryPath: string): Promise<boolean> {
        try {
            const args: string[] = [];
            
            if (this.databasePath) {
                args.push('--database', this.databasePath);
            }
            
            if (this.port !== 8080) {
                args.push('--port', this.port.toString());
            }

            this.serverProcess = spawn(binaryPath, args, {
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
        } catch (error) {
            throw new ServerError(`Failed to start ContextLite server: ${error}`);
        }
    }

    /**
     * Add a document to ContextLite.
     */
    async addDocument(
        content: string,
        documentId?: string,
        metadata?: Record<string, any>
    ): Promise<any> {
        const payload: any = { content };
        
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
    async query(query: string, options: QueryOptions = {}): Promise<QueryResult> {
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
    async getDocument(documentId: string): Promise<Document> {
        return this.get(`/documents/${encodeURIComponent(documentId)}`);
    }

    /**
     * Delete a document by ID.
     */
    async deleteDocument(documentId: string): Promise<any> {
        return this.delete(`/documents/${encodeURIComponent(documentId)}`);
    }

    /**
     * Get ContextLite statistics.
     */
    async getStats(): Promise<ServerStats> {
        return this.get('/stats');
    }

    /**
     * Stop managed server and cleanup resources.
     */
    async close(): Promise<void> {
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
            } catch {
                // Ignore cleanup errors
            }
            this.serverProcess = undefined;
        }
    }

    /**
     * Make GET request to ContextLite server.
     */
    private async get(endpoint: string): Promise<any> {
        return this.request('GET', endpoint);
    }

    /**
     * Make POST request to ContextLite server.
     */
    private async post(endpoint: string, data: any): Promise<any> {
        return this.request('POST', endpoint, {
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(data)
        });
    }

    /**
     * Make DELETE request to ContextLite server.
     */
    private async delete(endpoint: string): Promise<any> {
        return this.request('DELETE', endpoint);
    }

    /**
     * Make HTTP request to ContextLite server.
     */
    private async request(method: string, endpoint: string, options: any = {}): Promise<any> {
        if (!(await this.ensureServerRunning())) {
            throw new ServerError('ContextLite server is not running');
        }

        const url = `${this.baseUrl}${endpoint}`;
        const controller = new AbortController();
        const timeoutId = setTimeout(() => controller.abort(), this.timeout);

        try {
            const response = await fetch(url, {
                method,
                signal: controller.signal,
                ...options
            });

            clearTimeout(timeoutId);

            if (!response.ok) {
                throw new ServerError(`HTTP ${response.status}: ${response.statusText}`);
            }

            return await response.json();
        } catch (error) {
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

/**
 * Create a ContextLite client with automatic cleanup.
 */
export async function withContextLiteClient<T>(
    options: ClientOptions,
    callback: (client: ContextLiteClient) => Promise<T>
): Promise<T> {
    const client = new ContextLiteClient(options);
    try {
        return await callback(client);
    } finally {
        await client.close();
    }
}
