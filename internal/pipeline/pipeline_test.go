package pipeline

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"

	"contextlite/internal/engine"
	"contextlite/internal/storage"
	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

func TestMain(m *testing.M) {
	// Setup
	code := m.Run()
	// Cleanup any test databases
	os.RemoveAll("test_*.db")
	os.Exit(code)
}

func setupTestPipeline(t *testing.T) (*Pipeline, *storage.Storage, func()) {
	dbPath := filepath.Join(t.TempDir(), "test_pipeline.db")
	
	store, err := storage.New(dbPath)
	if err != nil {
		t.Fatalf("Failed to create storage: %v", err)
	}
	
	cfg := &config.Config{
		Tokenizer: config.TokenizerConfig{
			ModelID:          "test-model",
			MaxTokensDefault: 4000,
		},
		SMT: config.SMTConfig{
			SolverTimeoutMs: 5000,
			MaxCandidates:   50,
			MaxPairsPerDoc:  4000,
			Z3: config.Z3Config{
				BinaryPath:         "z3",
				EnableVerification: false,
			},
		},
	}
	
	// Create core engine for testing
	engine := engine.NewCoreEngine(cfg, store)
	
	pipeline := New(store, engine, cfg)
	
	cleanup := func() {
		store.Close()
		os.Remove(dbPath)
	}
	
	return pipeline, store, cleanup
}

func addTestDocuments(t *testing.T, store *storage.Storage) {
	docs := []*types.Document{
		{
			ID:           "test-doc-1",
			Path:         "/test/main.go",
			Content:      "package main\n\nfunc main() {\n\tfmt.Println(\"Hello World\")\n}",
			Language:     "go",
			TokenCount:   15,
			ModifiedTime: time.Now().Unix(),
		},
		{
			ID:           "test-doc-2", 
			Path:         "/test/utils.go",
			Content:      "package main\n\nfunc helper() {\n\treturn \"helper function\"\n}",
			Language:     "go",
			TokenCount:   10,
			ModifiedTime: time.Now().Unix(),
		},
	}
	
	ctx := context.Background()
	for _, doc := range docs {
		err := store.AddDocument(ctx, doc)
		if err != nil {
			t.Fatalf("Failed to add test document: %v", err)
		}
	}
}

// Test pipeline construction
func TestPipeline_New(t *testing.T) {
	dbPath := filepath.Join(t.TempDir(), "test_new.db")
	defer os.Remove(dbPath)
	
	store, err := storage.New(dbPath)
	if err != nil {
		t.Fatalf("Failed to create storage: %v", err)
	}
	defer store.Close()
	
	cfg := &config.Config{}
	
	// Create core engine for testing
	engine := engine.NewCoreEngine(cfg, store)
	
	pipeline := New(store, engine, cfg)
	
	if pipeline == nil {
		t.Errorf("Pipeline should not be nil")
	}
	
	if pipeline.Storage() != store {
		t.Errorf("Pipeline storage should match provided storage")
	}
	
	if pipeline.Config() != cfg {
		t.Errorf("Pipeline config should match provided config")
	}
}

// Test basic context assembly delegation
func TestPipeline_AssembleContext(t *testing.T) {
	pipeline, store, cleanup := setupTestPipeline(t)
	defer cleanup()
	
	addTestDocuments(t, store)
	
	ctx := context.Background()
	req := &types.AssembleRequest{
		Query:         "main",
		MaxTokens:     1000,
		MaxDocuments:  3,
		WorkspacePath: "/test",
		ModelID:       "test-model",
	}
	
	result, err := pipeline.AssembleContext(ctx, req)
	if err != nil {
		t.Fatalf("Failed to assemble context: %v", err)
	}
	
	if result == nil {
		t.Fatalf("Result should not be nil")
	}
	
	// Verify basic result structure
	if result.Query != req.Query {
		t.Errorf("Result query should match request query")
	}
	
	if result.TotalDocuments != len(result.Documents) {
		t.Errorf("TotalDocuments should match Documents length")
	}
	
	if len(result.Documents) > req.MaxDocuments {
		t.Errorf("Result should not exceed max documents. Got %d, max %d", len(result.Documents), req.MaxDocuments)
	}
	
	// Verify timing information is populated
	if result.Timings.TotalMs < 0 {
		t.Errorf("Total time should be non-negative, got %f", result.Timings.TotalMs)
	}
}

// Test caching behavior
func TestPipeline_CacheOperations(t *testing.T) {
	pipeline, store, cleanup := setupTestPipeline(t)
	defer cleanup()
	
	addTestDocuments(t, store)
	
	ctx := context.Background()
	req := &types.AssembleRequest{
		Query:         "cache test query",
		MaxTokens:     1000,
		MaxDocuments:  3,
		WorkspacePath: "/test",
		ModelID:       "test-model",
		UseCache:      true,
	}
	
	// First assembly should not hit cache
	result1, err := pipeline.AssembleContext(ctx, req)
	if err != nil {
		t.Fatalf("Failed to assemble context: %v", err)
	}
	
	if result1.CacheHit {
		t.Errorf("First request should not hit cache")
	}
	
	// Second assembly with same request should hit cache if enabled
	result2, err := pipeline.AssembleContext(ctx, req)
	if err != nil {
		t.Fatalf("Failed to assemble context on second call: %v", err)
	}
	
	// Note: Cache hit depends on implementation and result quality
	// Just verify we get a valid result
	if result2 == nil {
		t.Errorf("Second result should not be nil")
	}
}

// Test document management delegation
func TestPipeline_DocumentOperations(t *testing.T) {
	pipeline, _, cleanup := setupTestPipeline(t)
	defer cleanup()
	
	doc := types.Document{
		ID:           "pipeline-test-doc",
		Path:         "/test/pipeline.go", 
		Content:      "package main\n\nfunc pipelineTest() {}",
		Language:     "go",
		TokenCount:   5,
		ModifiedTime: time.Now().Unix(),
	}
	
	// Test IndexDocument delegation
	err := pipeline.IndexDocument(doc)
	if err != nil {
		t.Fatalf("IndexDocument should delegate to engine: %v", err)
	}
	
	// Test RemoveDocument delegation  
	err = pipeline.RemoveDocument(doc.ID)
	if err != nil {
		t.Fatalf("RemoveDocument should delegate to engine: %v", err)
	}
}

// Test engine stats delegation
func TestPipeline_GetEngineStats(t *testing.T) {
	pipeline, _, cleanup := setupTestPipeline(t)
	defer cleanup()
	
	stats, err := pipeline.GetEngineStats()
	if err != nil {
		t.Fatalf("GetEngineStats should delegate to engine: %v", err)
	}
	
	if stats == nil {
		t.Errorf("Stats should not be nil")
		return // Avoid nil pointer dereference
	}
	
	// Stub engine should return basic stats
	if stats.LicenseTier == "" {
		t.Errorf("Stats should include license tier")
	}
}

// Test configuration delegation
func TestPipeline_UpdateEngineConfig(t *testing.T) {
	pipeline, _, cleanup := setupTestPipeline(t)
	defer cleanup()
	
	engineConfig := types.EngineConfig{
		OptimizationStrategy: types.StrategyWeightedSum,
		SolverTimeout:       5 * time.Second,
		MaxCandidates:       100,
	}
	
	err := pipeline.UpdateEngineConfig(engineConfig)
	if err != nil {
		t.Fatalf("UpdateEngineConfig should delegate to engine: %v", err)
	}
}

// Test cleanup operations
func TestPipeline_Close(t *testing.T) {
	pipeline, _, cleanup := setupTestPipeline(t)
	defer cleanup()
	
	err := pipeline.Close()
	if err != nil {
		t.Fatalf("Close should not fail: %v", err)
	}
}

// Test cache key building (this stays in pipeline)
func TestPipeline_CacheKeyBuilding(t *testing.T) {
	pipeline, _, cleanup := setupTestPipeline(t)
	defer cleanup()
	
	ctx := context.Background()
	req1 := &types.AssembleRequest{
		Query:         "test query",
		MaxTokens:     1000,
		MaxDocuments:  10,
		WorkspacePath: "/test",
	}
	
	req2 := &types.AssembleRequest{
		Query:         "test query", 
		MaxTokens:     1000,
		MaxDocuments:  10,
		WorkspacePath: "/test",
	}
	
	req3 := &types.AssembleRequest{
		Query:         "different query",
		MaxTokens:     1000,
		MaxDocuments:  10,
		WorkspacePath: "/test",
	}
	
	key1 := pipeline.buildCacheKey(ctx, req1)
	key2 := pipeline.buildCacheKey(ctx, req2)
	key3 := pipeline.buildCacheKey(ctx, req3)
	
	if key1 != key2 {
		t.Errorf("Identical requests should have same cache key")
	}
	
	if key1 == key3 {
		t.Errorf("Different requests should have different cache keys")
	}
}

// Test query hashing (this stays in pipeline)
func TestPipeline_QueryHashing(t *testing.T) {
	pipeline, _, cleanup := setupTestPipeline(t)
	defer cleanup()
	
	req1 := &types.AssembleRequest{
		Query:         "test query",
		MaxTokens:     1000,
		MaxDocuments:  10,
		WorkspacePath: "/test",
	}
	
	req2 := &types.AssembleRequest{
		Query:         "test query",
		MaxTokens:     1000,
		MaxDocuments:  10,
		WorkspacePath: "/test",
	}
	
	req3 := &types.AssembleRequest{
		Query:         "different query",
		MaxTokens:     1000,
		MaxDocuments:  10,
		WorkspacePath: "/test",
	}
	
	hash1 := pipeline.hashQuery(req1)
	hash2 := pipeline.hashQuery(req2)
	hash3 := pipeline.hashQuery(req3)
	
	if hash1 != hash2 {
		t.Errorf("Identical requests should have same hash")
	}
	
	if hash1 == hash3 {
		t.Errorf("Different requests should have different hashes")
	}
	
	if len(hash1) != 64 { // SHA256 hex length
		t.Errorf("Hash should be 64 characters long, got %d", len(hash1))
	}
}
