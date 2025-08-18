package engine

import (
	"context"
	"testing"
	"time"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// mockStorage provides a simple storage implementation for testing
type mockStorage struct{}

func (m *mockStorage) InsertDocument(doc types.Document) error { return nil }
func (m *mockStorage) UpdateDocument(doc types.Document) error { return nil }
func (m *mockStorage) GetDocument(ctx context.Context, id string) (*types.Document, error) { return nil, nil }
func (m *mockStorage) GetDocumentByPath(ctx context.Context, path string) (*types.Document, error) { return nil, nil }
func (m *mockStorage) DeleteDocument(ctx context.Context, id string) error { return nil }
func (m *mockStorage) AddDocument(ctx context.Context, doc *types.Document) error { return nil }
func (m *mockStorage) SearchDocuments(ctx context.Context, query string, limit int) ([]types.Document, error) { return []types.Document{}, nil }
func (m *mockStorage) GetWorkspaceStats(workspacePath string) (*types.WorkspaceStats, error) { return nil, nil }
func (m *mockStorage) GetWorkspaceWeights(ctx context.Context, workspacePath string) (*types.WorkspaceWeights, error) { return nil, nil }
func (m *mockStorage) SaveWorkspaceWeights(workspacePath string, weights types.FeatureWeights) error { return nil }
func (m *mockStorage) GetCorpusHash(ctx context.Context) (string, error) { return "test-hash", nil }
func (m *mockStorage) GetQueryCache(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion string) (*types.QueryResult, error) { return nil, nil }
func (m *mockStorage) SaveQueryCacheWithKey(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion, cacheKey string, result *types.QueryResult, expiresAt time.Time) error { return nil }
func (m *mockStorage) GetCachedResultByKey(ctx context.Context, cacheKey string) (*types.QueryResult, error) { return nil, nil }
func (m *mockStorage) InvalidateCache(ctx context.Context) error { return nil }
func (m *mockStorage) GetCacheStats(ctx context.Context) (*types.CacheStats, error) { return &types.CacheStats{}, nil }
func (m *mockStorage) GetStorageStats(ctx context.Context) (map[string]interface{}, error) { return map[string]interface{}{}, nil }
func (m *mockStorage) Close() error { return nil }

func TestLoadEngine(t *testing.T) {
	cfg := &config.Config{
		optimization: config.optimizationConfig{
			SolverTimeoutMs: 5000,
			MaxCandidates:   100,
		},
	}
	storage := &mockStorage{}
	
	// Test engine loading (should fallback to stub since no private binary exists)
	engine := LoadEngine(cfg, storage)
	
	if engine == nil {
		t.Fatal("LoadEngine returned nil")
	}
	
	// Verify it's a stub engine (since private binary won't be available in test)
	if _, ok := engine.(*CoreEngine); !ok {
		t.Errorf("Expected CoreEngine, got %T", engine)
	}
}

func TestPrivateEngineAvailable(t *testing.T) {
	// Should return false in test environment (no private binary)
	available := PrivateEngineAvailable()
	
	// This is expected to be false in CI/test environment
	if available {
		t.Log("Private engine is available (unexpected in test env, but not an error)")
	} else {
		t.Log("Private engine not available (expected in test environment)")
	}
}

func TestGetEngineInfo(t *testing.T) {
	cfg := &config.Config{}
	storage := &mockStorage{}
	
	// Test with stub engine
	coreEngine := NewCoreEngine(cfg, storage)
	info := GetEngineInfo(coreEngine)
	
	if info["type"] != "core-engine" {
		t.Errorf("Expected type 'core-engine', got %v", info["type"])
	}
	
	if info["communication"] != "direct" {
		t.Errorf("Expected communication 'direct', got %v", info["communication"])
	}
}

func TestCoreEngineBasicFunctionality(t *testing.T) {
	cfg := &config.Config{}
	storage := &mockStorage{}
	
	engine := NewCoreEngine(cfg, storage)
	
	// Test basic operations don't panic
	stats, err := engine.GetStats()
	if err != nil {
		t.Errorf("GetStats failed: %v", err)
	}
	
	if stats.LicenseTier != "open-source" {
		t.Errorf("Expected open-source license tier, got %s", stats.LicenseTier)
	}
	
	// Test Close doesn't fail
	if err := engine.Close(); err != nil {
		t.Errorf("Close failed: %v", err)
	}
}
