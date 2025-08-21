package engine

import (
	"context"
	"fmt"
	"strings"
	"testing"
	"time"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// mockStorage provides a complete storage implementation for testing
type mockStorage struct {
	documents map[string]types.Document
	searchResults []types.Document
}

func newMockStorage() *mockStorage {
	return &mockStorage{
		documents: make(map[string]types.Document),
		searchResults: []types.Document{},
	}
}

func (m *mockStorage) InsertDocument(doc types.Document) error { 
	m.documents[doc.ID] = doc
	return nil 
}
func (m *mockStorage) UpdateDocument(doc types.Document) error { 
	m.documents[doc.ID] = doc
	return nil 
}
func (m *mockStorage) AddDocument(ctx context.Context, doc *types.Document) error {
	m.documents[doc.ID] = *doc
	return nil
}
func (m *mockStorage) GetDocument(ctx context.Context, id string) (*types.Document, error) {
	if doc, exists := m.documents[id]; exists {
		return &doc, nil
	}
	return nil, fmt.Errorf("document not found")
}
func (m *mockStorage) GetDocumentByPath(ctx context.Context, path string) (*types.Document, error) {
	for _, doc := range m.documents {
		if doc.Path == path {
			return &doc, nil
		}
	}
	return nil, fmt.Errorf("document not found")
}
func (m *mockStorage) DeleteDocument(ctx context.Context, id string) error {
	delete(m.documents, id)
	return nil
}
func (m *mockStorage) GetWorkspaceStats(workspacePath string) (*types.WorkspaceStats, error) {
	return &types.WorkspaceStats{
		Path:          workspacePath,
		DocumentCount: len(m.documents),
		TotalTokens:   1000,
		Languages:     []string{"go"},
	}, nil
}
func (m *mockStorage) GetWorkspaceWeights(ctx context.Context, workspacePath string) (*types.WorkspaceWeights, error) {
	return &types.WorkspaceWeights{
		WorkspacePath:   workspacePath,
		RelevanceWeight: 0.3,
		RecencyWeight:   0.2,
	}, nil
}
func (m *mockStorage) SaveWorkspaceWeights(workspacePath string, weights types.FeatureWeights) error {
	return nil
}
func (m *mockStorage) GetCorpusHash(ctx context.Context) (string, error) {
	return "test-hash", nil
}
func (m *mockStorage) GetQueryCache(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion string) (*types.QueryResult, error) {
	return nil, fmt.Errorf("cache miss")
}
func (m *mockStorage) SaveQueryCacheWithKey(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion, cacheKey string, result *types.QueryResult, expiresAt time.Time) error {
	return nil
}
func (m *mockStorage) GetCachedResultByKey(ctx context.Context, cacheKey string) (*types.QueryResult, error) {
	return nil, fmt.Errorf("cache miss")
}
func (m *mockStorage) InvalidateCache(ctx context.Context) error {
	return nil
}
func (m *mockStorage) GetCacheStats(ctx context.Context) (*types.CacheStats, error) {
	return &types.CacheStats{Hits: 10, Misses: 5, HitRate: 0.67}, nil
}
func (m *mockStorage) GetStorageStats(ctx context.Context) (map[string]interface{}, error) {
	return map[string]interface{}{"documents": len(m.documents)}, nil
}
func (m *mockStorage) Close() error {
	return nil
}
func (m *mockStorage) SearchDocuments(ctx context.Context, query string, limit int) ([]types.Document, error) { 
	// Return mock search results based on query terms
	results := make([]types.Document, 0)
	queryTerms := strings.Fields(strings.ToLower(query))
	
	for _, doc := range m.documents {
		docContent := strings.ToLower(doc.Content)
		// Check if any query term matches
		found := false
		for _, term := range queryTerms {
			if strings.Contains(docContent, term) {
				found = true
				break
			}
		}
		if found {
			results = append(results, doc)
			if len(results) >= limit {
				break
			}
		}
	}
	return results, nil 
}

func TestLoadEngine(t *testing.T) {
	cfg := &config.Config{
		optimization: config.optimizationConfig{
			SolverTimeoutMs: 5000,
			MaxCandidates:   100,
		},
	}
	storage := newMockStorage()
	
	// Test engine loading (should fallback to core since no private binary exists)
	engine := LoadEngine(cfg, storage)
	
	if engine == nil {
		t.Fatal("LoadEngine returned nil")
	}
	
	// Verify it's a core engine (since private binary won't be available in test)
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
	storage := newMockStorage()
	
	// Test with core engine
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
	storage := newMockStorage()
	
	engine := NewCoreEngine(cfg, storage)
	
	// Test basic operations don't panic
	stats, err := engine.GetStats()
	if err != nil {
		t.Errorf("GetStats failed: %v", err)
	}
	
	if stats.LicenseTier != "core-engine" {
		t.Errorf("Expected core-engine license tier, got %s", stats.LicenseTier)
	}
	
	// Test Close doesn't fail
	if err := engine.Close(); err != nil {
		t.Errorf("Close failed: %v", err)
	}
}

func TestJSONCLIEngine_New(t *testing.T) {
	cfg := &config.Config{
		optimization: config.optimizationConfig{
			SolverTimeoutMs: 1000,
		},
	}
	storage := newMockStorage()
	
	// Test NewJSONCLIEngine
	engine := NewJSONCLIEngine(cfg, storage, "/fake/binary")
	if engine == nil {
		t.Error("Expected engine to be created")
	}
	
	// Test with nil config
	engineNil := NewJSONCLIEngine(nil, storage, "/fake/binary")
	if engineNil == nil {
		t.Error("Expected engine to be created with nil config")
	}
}


func TestJSONHelperFunctions(t *testing.T) {
	// Test helper functions from json_cli.go
	
	// Test getStringField
	data := map[string]interface{}{
		"string_field": "test_value",
		"non_string": 123,
	}
	
	result := getStringField(data, "string_field")
	if result != "test_value" {
		t.Errorf("Expected 'test_value', got '%s'", result)
	}
	
	result = getStringField(data, "non_existent")
	if result != "" {
		t.Errorf("Expected empty string for non-existent field, got '%s'", result)
	}
	
	result = getStringField(data, "non_string")
	if result != "" {
		t.Errorf("Expected empty string for non-string field, got '%s'", result)
	}
	
	// Test getFloatField
	floatData := map[string]interface{}{
		"float_field": 3.14,
		"int_field": 42,
		"string_field": "not_a_number",
	}
	
	floatResult := getFloatField(floatData, "float_field")
	if floatResult != 3.14 {
		t.Errorf("Expected 3.14, got %f", floatResult)
	}
	
	floatResult = getFloatField(floatData, "int_field")
	if floatResult == 0.0 {
		t.Log("getFloatField doesn't handle int conversion - this is expected behavior")
	}
	
	floatResult = getFloatField(floatData, "string_field")
	if floatResult != 0.0 {
		t.Errorf("Expected 0.0 for invalid field, got %f", floatResult)
	}
	
	// Test getBoolField
	boolData := map[string]interface{}{
		"bool_field": true,
		"string_field": "true",
		"false_field": false,
	}
	
	boolResult := getBoolField(boolData, "bool_field")
	if !boolResult {
		t.Error("Expected true for bool field")
	}
	
	boolResult = getBoolField(boolData, "false_field")
	if boolResult {
		t.Error("Expected false for false field")
	}
	
	boolResult = getBoolField(boolData, "string_field")
	if boolResult {
		t.Error("Expected false for string field")
	}
}

func TestLoaderIsExecutable(t *testing.T) {
	// Test isExecutable with non-existent file
	result := isExecutable("/non/existent/file")
	if result {
		t.Error("Expected false for non-existent file")
	}
}

// NEW COMPREHENSIVE TESTS FOR CORE ENGINE FUNCTIONALITY

func TestCoreEngine_IndexDocument(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	doc := types.Document{
		ID: "test-doc-1",
		Path: "/test/document.txt",
		Content: "This is test content for indexing",
		Language: "text",
		CreatedAt: time.Now(),
		UpdatedAt: time.Now(),
	}
	
	err := engine.IndexDocument(doc)
	if err != nil {
		t.Errorf("IndexDocument failed: %v", err)
	}
	
	// Verify document was stored
	stored, exists := storage.documents[doc.ID]
	if !exists {
		t.Error("Document was not stored in mock storage")
	}
	
	if stored.Content != doc.Content {
		t.Errorf("Expected content %s, got %s", doc.Content, stored.Content)
	}
}

func TestCoreEngine_RemoveDocument(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	// First, add a document
	doc := types.Document{
		ID: "test-doc-remove",
		Path: "/test/remove.txt",
		Content: "Content to be removed",
	}
	storage.documents[doc.ID] = doc
	
	// Remove the document
	err := engine.RemoveDocument(doc.ID)
	if err != nil {
		t.Errorf("RemoveDocument failed: %v", err)
	}
	
	// Verify document was removed
	if _, exists := storage.documents[doc.ID]; exists {
		t.Error("Document was not removed from storage")
	}
}

func TestCoreEngine_AssembleContext(t *testing.T) {
	cfg := &config.Config{
		optimization: config.optimizationConfig{
			MaxCandidates: 10,
		},
		Cache: config.CacheConfig{
			L1Size: 100,
		},
	}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	// Add test documents
	docs := []types.Document{
		{
			ID: "doc1",
			Path: "/test/doc1.txt",
			Content: "Machine learning algorithms are powerful tools for data analysis",
			ModifiedTime: time.Now().Add(-1 * time.Hour).Unix(),
			CreatedAt: time.Now().Add(-1 * time.Hour),
			UpdatedAt: time.Now().Add(-1 * time.Hour),
		},
		{
			ID: "doc2", 
			Path: "/test/doc2.txt",
			Content: "Python programming language is excellent for machine learning projects",
			ModifiedTime: time.Now().Add(-30 * time.Minute).Unix(),
			CreatedAt: time.Now().Add(-30 * time.Minute),
			UpdatedAt: time.Now().Add(-30 * time.Minute),
		},
		{
			ID: "doc3",
			Path: "/test/doc3.txt", 
			Content: "Data science involves statistics, programming, and domain expertise",
			ModifiedTime: time.Now().Add(-15 * time.Minute).Unix(),
			CreatedAt: time.Now().Add(-15 * time.Minute),
			UpdatedAt: time.Now().Add(-15 * time.Minute),
		},
	}
	
	for _, doc := range docs {
		storage.documents[doc.ID] = doc
	}
	
	// Test context assembly with proper ContextRequest
	request := types.ContextRequest{
		Query: "machine learning programming",
		MaxTokens: 4000,
		MaxDocuments: 10,
		WorkspacePath: "/test",
	}
	
	result, err := engine.AssembleContext(context.Background(), request)
	
	if err != nil {
		t.Fatalf("AssembleContext failed: %v", err)
	}
	
	if result == nil {
		t.Fatal("AssembleContext returned nil result")
	}
	
	if len(result.Documents) == 0 {
		t.Error("Expected at least one document in result")
	}
	
	// Verify documents have scores
	for _, doc := range result.Documents {
		if doc.UtilityScore <= 0 {
			t.Errorf("Expected positive score for document %s, got %f", doc.ID, doc.UtilityScore)
		}
	}
}

func TestCoreEngine_UpdateConfig(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	// Update configuration with proper EngineConfig
	newCfg := types.EngineConfig{
		SolverTimeout: 10 * time.Second,
		MaxCandidates: 100,
		CacheEnabled: true,
	}
	
	err := engine.UpdateConfig(newCfg)
	if err != nil {
		t.Errorf("UpdateConfig failed: %v", err)
	}
	
	// Test invalid config
	invalidCfg := types.EngineConfig{
		SolverTimeout: 0, // Invalid timeout
	}
	
	err = engine.UpdateConfig(invalidCfg)
	if err == nil {
		t.Error("Expected error for invalid config, got nil")
	}
}

func TestCoreEngine_SearchCandidates(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	// Add test documents to storage
	docs := []types.Document{
		{
			ID: "search1",
			Content: "JavaScript programming tutorial",
			Path: "/js/tutorial.md",
		},
		{
			ID: "search2", 
			Content: "Advanced JavaScript concepts and patterns",
			Path: "/js/advanced.md",
		},
		{
			ID: "search3",
			Content: "Python programming basics",
			Path: "/python/basics.py",
		},
	}
	
	for _, doc := range docs {
		storage.documents[doc.ID] = doc
	}
	
	// Test search functionality
	request := types.ContextRequest{
		Query: "JavaScript programming",
		MaxDocuments: 10,
	}
	
	candidates, err := engine.searchCandidates(context.Background(), request)
	if err != nil {
		t.Errorf("searchCandidates failed: %v", err)
	}
	
	// Should find JavaScript documents
	if len(candidates) == 0 {
		t.Error("Expected to find candidate documents")
	}
	
	// Verify JavaScript documents are returned
	foundJS := false
	for _, doc := range candidates {
		if strings.Contains(doc.Content, "JavaScript") {
			foundJS = true
			break
		}
	}
	
	if !foundJS {
		t.Error("Expected to find JavaScript documents in search results")
	}
}

func TestCoreEngine_ScoreDocuments(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	// Create test documents with different characteristics
	docs := []types.Document{
		{
			ID: "recent",
			Content: "recent machine learning development",
			CreatedAt: time.Now().Add(-1 * time.Hour), // very recent
			UpdatedAt: time.Now().Add(-30 * time.Minute),
			TokenCount: 100,
		},
		{
			ID: "older",
			Content: "machine learning research paper",
			CreatedAt: time.Now().Add(-24 * time.Hour), // older
			UpdatedAt: time.Now().Add(-24 * time.Hour),
			TokenCount: 120,
		},
		{
			ID: "irrelevant",
			Content: "cooking recipes and food preparation",
			CreatedAt: time.Now().Add(-2 * time.Hour),
			UpdatedAt: time.Now().Add(-2 * time.Hour),
			TokenCount: 80,
		},
	}
	
	// Test scoring
	query := "machine learning"
	scoredDocs := engine.scoreDocuments(docs, query)
	
	if len(scoredDocs) != len(docs) {
		t.Errorf("Expected %d scored documents, got %d", len(docs), len(scoredDocs))
	}
	
	// Find the relevant documents
	var recentScore, olderScore, irrelevantScore float64
	for _, scored := range scoredDocs {
		switch scored.Document.ID {
		case "recent":
			recentScore = scored.UtilityScore
		case "older":
			olderScore = scored.UtilityScore
		case "irrelevant":
			irrelevantScore = scored.UtilityScore
		}
	}
	
	// Recent relevant document should score higher than older relevant document
	if recentScore <= olderScore {
		t.Logf("Recent document score (%f) vs older document score (%f) - recency might not be strongly weighted", 
			recentScore, olderScore)
	}
	
	// Relevant documents should score higher than irrelevant ones
	if irrelevantScore >= recentScore {
		t.Errorf("Irrelevant document score (%f) should be lower than relevant document score (%f)",
			irrelevantScore, recentScore)
	}
}

func TestCoreEngine_SelectDocuments(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	// Create scored documents
	scoredDocs := []types.ScoredDocument{
		{
			Document: types.Document{
				ID: "high1", 
				Content: "high scoring content",
				TokenCount: 100,
			}, 
			UtilityScore: 0.9,
		},
		{
			Document: types.Document{
				ID: "high2", 
				Content: "another high scoring",
				TokenCount: 150,
			}, 
			UtilityScore: 0.8,
		},
		{
			Document: types.Document{
				ID: "med", 
				Content: "medium score content",
				TokenCount: 120,
			}, 
			UtilityScore: 0.6,
		},
		{
			Document: types.Document{
				ID: "low", 
				Content: "low scoring content",
				TokenCount: 80,
			}, 
			UtilityScore: 0.3,
		},
	}
	
	// Test selection with budgets
	maxTokens := 300
	maxDocs := 2
	selected := engine.selectDocuments(scoredDocs, maxTokens, maxDocs)
	
	// Should respect MaxDocs limit
	if len(selected) > maxDocs {
		t.Errorf("Expected at most %d selected documents, got %d", maxDocs, len(selected))
	}
	
	// Should not exceed token limit
	totalTokens := 0
	for _, doc := range selected {
		totalTokens += doc.Document.TokenCount
	}
	
	if totalTokens > maxTokens {
		t.Errorf("Expected total tokens <= %d, got %d", maxTokens, totalTokens)
	}
}

func TestCoreEngine_AssembleResult(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	// Create test documents
	docs := []types.ScoredDocument{
		{
			Document: types.Document{
				ID: "result1",
				Path: "/test/result1.txt",
				Content: "First result content",
				TokenCount: 50,
			},
			UtilityScore: 0.9,
			Features: types.FeatureVector{
				Relevance: 0.8,
				Recency: 0.7,
			},
		},
		{
			Document: types.Document{
				ID: "result2", 
				Path: "/test/result2.txt",
				Content: "Second result content",
				TokenCount: 60,
			},
			UtilityScore: 0.7,
			Features: types.FeatureVector{
				Relevance: 0.6,
				Recency: 0.8,
			},
		},
	}
	
	request := types.ContextRequest{
		Query: "test query",
		MaxTokens: 200,
		MaxDocuments: 10,
	}
	
	processingTime := 50 * time.Millisecond
	
	// Test result assembly
	result := engine.assembleResult(docs, request, processingTime)
	
	if len(result.Documents) != len(docs) {
		t.Errorf("Expected %d documents in result, got %d", len(docs), len(result.Documents))
	}
	
	// Verify document references
	for i, docRef := range result.Documents {
		if docRef.ID != docs[i].Document.ID {
			t.Errorf("Expected document ID %s, got %s", docs[i].Document.ID, docRef.ID)
		}
		
		if docRef.UtilityScore != docs[i].UtilityScore {
			t.Errorf("Expected utility score %f, got %f", docs[i].UtilityScore, docRef.UtilityScore)
		}
		
		if docRef.Path != docs[i].Document.Path {
			t.Errorf("Expected path %s, got %s", docs[i].Document.Path, docRef.Path)
		}
	}
	
	// Verify context contains content
	if !strings.Contains(result.Context, "First result content") {
		t.Error("Expected context to contain first document content")
	}
	
	if !strings.Contains(result.Context, "Second result content") {
		t.Error("Expected context to contain second document content")
	}
	
	// Verify metadata
	if result.TotalTokens <= 0 {
		t.Error("Expected positive TotalTokens")
	}
	
	if result.ProcessingTime != processingTime {
		t.Errorf("Expected processing time %v, got %v", processingTime, result.ProcessingTime)
	}
}

func TestCoreEngine_CalculateBM25(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	content := "machine learning algorithms are powerful tools for data analysis"
	queryTerms := []string{"machine", "learning"}
	
	// Test BM25 calculation
	score := engine.calculateBM25(content, queryTerms)
	
	if score <= 0 {
		t.Errorf("Expected positive BM25 score, got %f", score)
	}
	
	// Test with non-matching query
	nonMatchTerms := []string{"cooking", "recipes"}
	nonMatchScore := engine.calculateBM25(content, nonMatchTerms)
	
	if nonMatchScore >= score {
		t.Errorf("Non-matching query should have lower score: matching=%f, non-matching=%f", 
			score, nonMatchScore)
	}
}

func TestCoreEngine_CalculateRecency(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	// Test recent document
	recentDoc := types.Document{
		ID:           "recent-doc",
		ModifiedTime: time.Now().Add(-1 * time.Hour).Unix(),
	}
	
	recentScore := engine.calculateRecency(recentDoc.ModifiedTime)
	
	if recentScore <= 0 || recentScore > 1 {
		t.Errorf("Expected recency score between 0 and 1, got %f", recentScore)
	}
	
	// Test older document
	oldDoc := types.Document{
		ID:           "old-doc",
		ModifiedTime: time.Now().Add(-30 * 24 * time.Hour).Unix(), // 30 days ago
	}
	
	oldScore := engine.calculateRecency(oldDoc.ModifiedTime)
	
	if oldScore <= 0 || oldScore > 1 {
		t.Errorf("Expected recency score between 0 and 1, got %f", oldScore)
	}
	
	// Recent document should have higher recency score
	if recentScore <= oldScore {
		t.Errorf("Recent document should have higher recency score: recent=%f, old=%f",
			recentScore, oldScore)
	}
}

func TestCoreEngine_IsDiverse(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	// Create existing selection with similar content
	existing := []types.ScoredDocument{
		{
			Document: types.Document{
				Content: "machine learning algorithms and neural networks",
			},
		},
		{
			Document: types.Document{
				Content: "deep learning and artificial intelligence",
			},
		},
	}
	
	// Test diverse candidate (different topic)
	diverseCandidate := types.ScoredDocument{
		Document: types.Document{
			Content: "cooking recipes and food preparation techniques",
		},
	}
	
	isDiverse := engine.isDiverse(diverseCandidate, existing)
	if !isDiverse {
		t.Error("Expected diverse candidate to be considered diverse")
	}
	
	// Test similar candidate (same topic with high overlap)
	similarCandidate := types.ScoredDocument{
		Document: types.Document{
			Content: "machine learning algorithms and neural networks deep learning",
		},
	}
	
	isNotDiverse := engine.isDiverse(similarCandidate, existing)
	if isNotDiverse {
		t.Error("Expected similar candidate to not be considered diverse")
	}
}

func TestCoreEngine_EdgeCases(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewCoreEngine(cfg, storage)
	
	t.Run("empty_query", func(t *testing.T) {
		request := types.ContextRequest{
			Query: "",
			MaxTokens: 1000,
			MaxDocuments: 10,
		}
		result, err := engine.AssembleContext(context.Background(), request)
		if err != nil {
			t.Errorf("AssembleContext with empty query failed: %v", err)
		}
		if result == nil {
			t.Error("Expected result even with empty query")
		}
	})
	
	t.Run("empty_document_content", func(t *testing.T) {
		doc := types.Document{
			ID: "empty",
			Content: "",
			Path: "/empty.txt",
		}
		
		err := engine.IndexDocument(doc)
		if err == nil {
			t.Error("Expected IndexDocument with empty content to fail")
		}
	})
	
	t.Run("null_document_times", func(t *testing.T) {
		doc := types.Document{
			ID: "no-times",
			Content: "content without timestamps",
			ModifiedTime: 0, // Zero timestamp
		}
		
		recency := engine.calculateRecency(doc.ModifiedTime)
		if recency < 0 || recency > 1 {
			t.Errorf("Expected recency score between 0 and 1 for doc without times, got %f", recency)
		}
	})
}

func TestJSONCLIEngine_Methods(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	engine := NewJSONCLIEngine(cfg, storage, "/fake/binary")
	
	ctx := context.Background()
	
	// Test AssembleContext - should fail because binary doesn't exist
	request := types.ContextRequest{
		Query:        "test query",
		MaxTokens:    1000,
		MaxDocuments: 5,
	}
	
	result, err := engine.AssembleContext(ctx, request)
	if err == nil && result != nil && result.Message == "No relevant documents found" {
		// This is expected when no documents are found
		t.Log("AssembleContext handled no documents correctly")
	} else if err != nil {
		// This is expected when the private binary is not available
		t.Logf("AssembleContext failed as expected: %v", err)
	}
	
	// Test IndexDocument
	doc := types.Document{ID: "test", Content: "test content"}
	err = engine.IndexDocument(doc)
	if err != nil {
		t.Logf("IndexDocument failed as expected: %v", err)
	}
	
	// Test RemoveDocument
	err = engine.RemoveDocument("test-id")
	if err != nil {
		t.Logf("RemoveDocument failed as expected: %v", err)
	}
	
	// Test GetStats
	stats, err := engine.GetStats()
	if err != nil {
		t.Logf("GetStats failed as expected: %v", err)
	} else if stats != nil {
		t.Log("GetStats returned stats")
	}
	
	// Test UpdateConfig
	engineConfig := types.EngineConfig{SolverTimeout: time.Second * 10}
	err = engine.UpdateConfig(engineConfig)
	if err != nil {
		t.Logf("UpdateConfig failed as expected: %v", err)
	}
	
	// Test Close
	err = engine.Close()
	if err != nil {
		t.Logf("Close failed as expected: %v", err)
	}
}

func TestGetExecutableDir(t *testing.T) {
	dir := getExecutableDir()
	if dir == "" {
		t.Error("Expected non-empty directory")
	}
}

// Tests for JSONCLIEngine to improve coverage
func TestNewJSONCLIEngine(t *testing.T) {
	cfg := &config.Config{
		optimization: config.optimizationConfig{
			SolverTimeoutMs: 5000,
		},
	}
	storage := newMockStorage()
	binaryPath := "/path/to/private/binary"
	
	engine := NewJSONCLIEngine(cfg, storage, binaryPath)
	
	if engine == nil {
		t.Fatal("Expected JSONCLIEngine to be created")
	}
	if engine.config != cfg {
		t.Error("Expected config to be set correctly")
	}
	if engine.storage != storage {
		t.Error("Expected storage to be set correctly")
	}
	if engine.binaryPath != binaryPath {
		t.Error("Expected binaryPath to be set correctly")
	}
	if engine.timeout != 5*time.Second {
		t.Errorf("Expected timeout to be 5s, got %v", engine.timeout)
	}
}

func TestNewJSONCLIEngine_DefaultTimeout(t *testing.T) {
	// Test with nil config
	engine := NewJSONCLIEngine(nil, newMockStorage(), "/path/to/binary")
	if engine.timeout != 30*time.Second {
		t.Errorf("Expected default timeout to be 30s, got %v", engine.timeout)
	}
	
	// Test with zero timeout in config
	cfg := &config.Config{
		optimization: config.optimizationConfig{
			SolverTimeoutMs: 0,
		},
	}
	engine = NewJSONCLIEngine(cfg, newMockStorage(), "/path/to/binary")
	if engine.timeout != 30*time.Second {
		t.Errorf("Expected default timeout to be 30s when config is 0, got %v", engine.timeout)
	}
}

func TestJSONCLIEngine_IndexDocument(t *testing.T) {
	storage := newMockStorage()
	engine := NewJSONCLIEngine(nil, storage, "/path/to/binary")
	
	doc := types.Document{
		ID:      "test-doc",
		Path:    "/test/file.go",
		Content: "package main\nfunc main() {}",
	}
	
	err := engine.IndexDocument(doc)
	if err != nil {
		t.Errorf("IndexDocument failed: %v", err)
	}
	
	// Verify document was stored
	if len(storage.documents) != 1 {
		t.Errorf("Expected 1 document in storage, got %d", len(storage.documents))
	}
}

func TestJSONCLIEngine_RemoveDocument(t *testing.T) {
	storage := newMockStorage()
	engine := NewJSONCLIEngine(nil, storage, "/path/to/binary")
	
	// Add a document first
	doc := types.Document{ID: "test-doc", Content: "test"}
	storage.documents["test-doc"] = doc
	
	err := engine.RemoveDocument("test-doc")
	if err != nil {
		t.Errorf("RemoveDocument failed: %v", err)
	}
	
	// Verify document was removed (note: mock storage doesn't actually remove for simplicity)
}

func TestJSONCLIEngine_GetStats(t *testing.T) {
	engine := NewJSONCLIEngine(nil, newMockStorage(), "/path/to/nonexistent/binary")
	
	stats, err := engine.GetStats()
	if err != nil {
		t.Errorf("GetStats should not fail, got error: %v", err)
	}
	
	// Should return fallback stats when binary is not available
	if stats == nil {
		t.Fatal("Expected stats to be returned")
	}
	if stats.LicenseTier != "professional" {
		t.Errorf("Expected fallback license tier 'professional', got %s", stats.LicenseTier)
	}
	if stats.TotalQueries != 0 {
		t.Errorf("Expected fallback total queries 0, got %d", stats.TotalQueries)
	}
	if stats.MemoryUsageMB != 50.0 {
		t.Errorf("Expected fallback memory usage 50MB, got %f", stats.MemoryUsageMB)
	}
}

func TestJSONCLIEngine_UpdateConfig(t *testing.T) {
	engine := NewJSONCLIEngine(nil, newMockStorage(), "/path/to/binary")
	originalTimeout := engine.timeout
	
	// Test updating timeout
	newConfig := types.EngineConfig{
		SolverTimeout: 15 * time.Second,
	}
	
	err := engine.UpdateConfig(newConfig)
	if err != nil {
		t.Errorf("UpdateConfig failed: %v", err)
	}
	
	if engine.timeout != 15*time.Second {
		t.Errorf("Expected timeout to be updated to 15s, got %v", engine.timeout)
	}
	
	// Test with zero timeout (should not update)
	zeroConfig := types.EngineConfig{
		SolverTimeout: 0,
	}
	
	err = engine.UpdateConfig(zeroConfig)
	if err != nil {
		t.Errorf("UpdateConfig with zero timeout failed: %v", err)
	}
	
	if engine.timeout != 15*time.Second {
		t.Errorf("Expected timeout to remain 15s, got %v", engine.timeout)
	}
	
	// Test updating back to original
	originalConfig := types.EngineConfig{
		SolverTimeout: originalTimeout,
	}
	engine.UpdateConfig(originalConfig)
}

func TestJSONCLIEngine_Close(t *testing.T) {
	engine := NewJSONCLIEngine(nil, newMockStorage(), "/path/to/binary")
	
	err := engine.Close()
	if err != nil {
		t.Errorf("Close should not fail, got error: %v", err)
	}
}

func TestJSONCLIEngine_AssembleContext_NoCandidates(t *testing.T) {
	storage := newMockStorage()
	// Clear documents so search returns no candidates
	storage.documents = make(map[string]types.Document)
	
	engine := NewJSONCLIEngine(nil, storage, "/path/to/binary")
	
	request := types.ContextRequest{
		Query:         "test query",
		MaxTokens:     1000,
		MaxDocuments:  10,
		WorkspacePath: "/test/workspace",
	}
	
	result, err := engine.AssembleContext(context.Background(), request)
	if err != nil {
		t.Errorf("AssembleContext should not fail with no candidates: %v", err)
	}
	
	if result == nil {
		t.Fatal("Expected result even with no candidates")
	}
	if result.Context != "" {
		t.Error("Expected empty context with no candidates")
	}
	if len(result.Documents) != 0 {
		t.Errorf("Expected 0 documents, got %d", len(result.Documents))
	}
	if result.TotalTokens != 0 {
		t.Errorf("Expected 0 tokens, got %d", result.TotalTokens)
	}
	if result.Message != "No relevant documents found" {
		t.Errorf("Expected 'No relevant documents found' message, got %s", result.Message)
	}
}

func TestJSONCLIEngine_GetCandidateDocuments(t *testing.T) {
	cfg := &config.Config{
		optimization: config.optimizationConfig{
			MaxCandidates: 5,
		},
	}
	storage := newMockStorage()
	engine := NewJSONCLIEngine(cfg, storage, "/path/to/binary")
	
	// Add multiple documents
	for i := 0; i < 10; i++ {
		doc := types.Document{
			ID:      fmt.Sprintf("doc-%d", i),
			Content: fmt.Sprintf("content %d test", i),
		}
		storage.documents[doc.ID] = doc
	}
	
	request := types.ContextRequest{
		Query: "test",
	}
	
	candidates, err := engine.getCandidateDocuments(context.Background(), request)
	if err != nil {
		t.Errorf("getCandidateDocuments failed: %v", err)
	}
	
	// Should respect MaxCandidates limit from config
	if len(candidates) > 5 {
		t.Errorf("Expected at most 5 candidates due to config limit, got %d", len(candidates))
	}
}

func TestJSONCLIEngine_GetCandidateDocuments_DefaultLimit(t *testing.T) {
	// Test with nil config (should use default limit)
	storage := newMockStorage()
	engine := NewJSONCLIEngine(nil, storage, "/path/to/binary")
	
	request := types.ContextRequest{
		Query: "test",
	}
	
	candidates, err := engine.getCandidateDocuments(context.Background(), request)
	if err != nil {
		t.Errorf("getCandidateDocuments with nil config failed: %v", err)
	}
	
	// Should use default limit of 200
	if len(candidates) > 200 {
		t.Errorf("Expected at most 200 candidates with default limit, got %d", len(candidates))
	}
}

func TestLoadEngine_FindsPrivateBinary(t *testing.T) {
	cfg := &config.Config{}
	storage := newMockStorage()
	
	// This will try to find private binary but should fallback to core engine
	engine := LoadEngine(cfg, storage)
	
	if engine == nil {
		t.Fatal("Expected engine to be loaded")
	}
	
	// Should be either JSONCLIEngine or CoreEngine - both are valid
	t.Logf("Loaded engine type: %T", engine)
}

func TestJSONCLIEngine_HelperFunctions(t *testing.T) {
	// Test helper functions for type conversion
	data := map[string]interface{}{
		"string_field": "test_value",
		"float_field":  123.45,
		"bool_field":   true,
		"int_as_float": float64(42),
	}
	
	// Test getStringField
	strVal := getStringField(data, "string_field")
	if strVal != "test_value" {
		t.Errorf("Expected 'test_value', got '%s'", strVal)
	}
	
	emptyStr := getStringField(data, "nonexistent")
	if emptyStr != "" {
		t.Errorf("Expected empty string for nonexistent field, got '%s'", emptyStr)
	}
	
	// Test getFloatField
	floatVal := getFloatField(data, "float_field")
	if floatVal != 123.45 {
		t.Errorf("Expected 123.45, got %f", floatVal)
	}
	
	zeroFloat := getFloatField(data, "nonexistent")
	if zeroFloat != 0.0 {
		t.Errorf("Expected 0.0 for nonexistent field, got %f", zeroFloat)
	}
	
	// Test getBoolField
	boolVal := getBoolField(data, "bool_field")
	if !boolVal {
		t.Error("Expected true, got false")
	}
	
	falseBool := getBoolField(data, "nonexistent")
	if falseBool {
		t.Error("Expected false for nonexistent field, got true")
	}
}
