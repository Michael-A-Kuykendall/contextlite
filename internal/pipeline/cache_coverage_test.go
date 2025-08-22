package pipeline

import (
	"context"
	"testing"
	"time"

	"contextlite/pkg/types"
)

// Simple mock storage that always returns a cache hit for getCachedResultByKey
type mockStorageWithCacheHit struct {
	realStorage types.StorageInterface
}

func (m *mockStorageWithCacheHit) GetCachedResultByKey(ctx context.Context, cacheKey string) (*types.QueryResult, error) {
	// Always return a cached result to trigger cache hit
	return &types.QueryResult{
		Query:          "mock cached query",
		Documents:      []types.DocumentReference{
			{ID: "cached-mock-doc", Path: "/cached/mock.go"},
		},
		TotalDocuments: 1,
		TotalTokens:    50,
		CoherenceScore: 0.8,
		CacheHit:       false, // Will be set to true by pipeline
		CacheKey:       cacheKey,
	}, nil
}

// Delegate all other methods to real storage
func (m *mockStorageWithCacheHit) AddDocument(ctx context.Context, doc *types.Document) error {
	return m.realStorage.AddDocument(ctx, doc)
}

func (m *mockStorageWithCacheHit) GetDocument(ctx context.Context, id string) (*types.Document, error) {
	return m.realStorage.GetDocument(ctx, id)
}

func (m *mockStorageWithCacheHit) GetDocumentByPath(ctx context.Context, path string) (*types.Document, error) {
	return m.realStorage.GetDocumentByPath(ctx, path)
}

func (m *mockStorageWithCacheHit) DeleteDocument(ctx context.Context, id string) error {
	return m.realStorage.DeleteDocument(ctx, id)
}

func (m *mockStorageWithCacheHit) InsertDocument(doc types.Document) error {
	return nil
}

func (m *mockStorageWithCacheHit) UpdateDocument(doc types.Document) error {
	return nil
}

func (m *mockStorageWithCacheHit) SearchDocuments(ctx context.Context, query string, limit int) ([]types.Document, error) {
	return []types.Document{}, nil
}

func (m *mockStorageWithCacheHit) GetWorkspaceStats(workspacePath string) (*types.WorkspaceStats, error) {
	return &types.WorkspaceStats{}, nil
}

func (m *mockStorageWithCacheHit) GetWorkspaceWeights(ctx context.Context, workspacePath string) (*types.WorkspaceWeights, error) {
	return m.realStorage.GetWorkspaceWeights(ctx, workspacePath)
}

func (m *mockStorageWithCacheHit) SaveWorkspaceWeights(workspacePath string, weights types.FeatureWeights) error {
	return m.realStorage.SaveWorkspaceWeights(workspacePath, weights)
}

func (m *mockStorageWithCacheHit) GetCorpusHash(ctx context.Context) (string, error) {
	return m.realStorage.GetCorpusHash(ctx)
}

func (m *mockStorageWithCacheHit) GetQueryCache(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion string) (*types.QueryResult, error) {
	return nil, nil
}

func (m *mockStorageWithCacheHit) SaveQueryCacheWithKey(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion, cacheKey string, result *types.QueryResult, expiresAt time.Time) error {
	return m.realStorage.SaveQueryCacheWithKey(ctx, queryHash, corpusHash, modelID, tokenizerVersion, cacheKey, result, expiresAt)
}

func (m *mockStorageWithCacheHit) InvalidateCache(ctx context.Context) error {
	return nil
}

func (m *mockStorageWithCacheHit) GetCacheStats(ctx context.Context) (*types.CacheStats, error) {
	return &types.CacheStats{}, nil
}

func (m *mockStorageWithCacheHit) GetStorageStats(ctx context.Context) (map[string]interface{}, error) {
	return map[string]interface{}{}, nil
}

func (m *mockStorageWithCacheHit) Close() error {
	return m.realStorage.Close()
}

// Test using mock storage that guarantees cache hit - lines 68-72
func TestPipeline_MockCacheHit_Lines68to72(t *testing.T) {
	// Create real storage first
	realPipeline, realStorage, cleanup := setupTestPipeline(t)
	defer cleanup()

	// Wrap it with our mock that always returns cache hits
	mockStorage := &mockStorageWithCacheHit{realStorage: realStorage}
	
	// Create new pipeline with mock storage
	pipeline := New(mockStorage, realPipeline.engine, realPipeline.config)

	ctx := context.Background()
	req := &types.AssembleRequest{
		Query:         "mock cache hit test",
		MaxTokens:     1000,
		MaxDocuments:  3,
		WorkspacePath: "/test",
		ModelID:       "test-model",
		UseCache:      true, // This is critical
	}

	// This should hit our mock cache and exercise lines 68-72
	result, err := pipeline.AssembleContext(ctx, req)
	if err != nil {
		t.Fatalf("Failed to assemble context: %v", err)
	}

	// Verify cache hit occurred
	if !result.CacheHit {
		t.Errorf("Expected cache hit but got cache miss")
	}
	
	if result.CacheKey == "" {
		t.Errorf("Expected non-empty cache key")
	}
	
	// Verify we got the cached content
	if len(result.Documents) != 1 || result.Documents[0].ID != "cached-mock-doc" {
		t.Errorf("Expected cached document, got: %+v", result.Documents)
	}
	
	t.Logf("SUCCESS: Mock cache hit achieved! Lines 68-72 covered.")
	t.Logf("CacheHit: %v, CacheKey: %s", result.CacheHit, result.CacheKey)
}