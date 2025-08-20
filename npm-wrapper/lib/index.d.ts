/**
 * ContextLite Node.js Client
 *
 * Provides a high-level Node.js interface to interact with ContextLite server.
 */
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
export declare class ContextLiteError extends Error {
    constructor(message: string);
}
export declare class BinaryNotFoundError extends ContextLiteError {
    constructor(message?: string);
}
export declare class ServerError extends ContextLiteError {
    constructor(message: string);
}
export interface ClientOptions {
    host?: string;
    port?: number;
    autoStart?: boolean;
    databasePath?: string;
    timeout?: number;
}
export declare class ContextLiteClient {
    private host;
    private port;
    private autoStart;
    private databasePath?;
    private timeout;
    private baseUrl;
    private serverProcess?;
    private binaryManager;
    constructor(options?: ClientOptions);
    /**
     * Ensure ContextLite server is running.
     */
    ensureServerRunning(): Promise<boolean>;
    /**
     * Check if ContextLite server is running and responsive.
     */
    isServerRunning(): Promise<boolean>;
    /**
     * Start ContextLite server process.
     */
    private startServer;
    /**
     * Add a document to ContextLite.
     */
    addDocument(content: string, documentId?: string, metadata?: Record<string, any>): Promise<any>;
    /**
     * Query ContextLite for relevant documents.
     */
    query(query: string, options?: QueryOptions): Promise<QueryResult>;
    /**
     * Get a specific document by ID.
     */
    getDocument(documentId: string): Promise<Document>;
    /**
     * Delete a document by ID.
     */
    deleteDocument(documentId: string): Promise<any>;
    /**
     * Get ContextLite statistics.
     */
    getStats(): Promise<ServerStats>;
    /**
     * Stop managed server and cleanup resources.
     */
    close(): Promise<void>;
    /**
     * Make GET request to ContextLite server.
     */
    private get;
    /**
     * Make POST request to ContextLite server.
     */
    private post;
    /**
     * Make DELETE request to ContextLite server.
     */
    private delete;
    /**
     * Make HTTP request to ContextLite server.
     */
    private request;
}
/**
 * Create a ContextLite client with automatic cleanup.
 */
export declare function withContextLiteClient<T>(options: ClientOptions, callback: (client: ContextLiteClient) => Promise<T>): Promise<T>;
//# sourceMappingURL=index.d.ts.map