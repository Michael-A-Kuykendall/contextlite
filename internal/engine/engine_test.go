package engine

import (
	"context"
	"strings"
	"testing"
	"time"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// min function helper
func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

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
func (m *mockStorage) GetDocument(ctx context.Context, id string) (*types.Document, error) { 
	if doc, exists := m.documents[id]; exists {
		return &doc, nil
	}
	return nil, nil 
}
func (m *mockStorage) GetDocumentByPath(ctx context.Context, path string) (*types.Document, error) { 
	for _, doc := range m.documents {
		if doc.Path == path {
			return &doc, nil
		}
	}
	return nil, nil 
}
func (m *mockStorage) DeleteDocument(ctx context.Context, id string) error { 
	delete(m.documents, id)
	return nil 
}
func (m *mockStorage) AddDocument(ctx context.Context, doc *types.Document) error { 
	m.documents[doc.ID] = *doc
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
func (m *mockStorage) GetWorkspaceStats(workspacePath string) (*types.WorkspaceStats, error) { 
	return &types.WorkspaceStats{
		Path: workspacePath,
		DocumentCount: len(m.documents),
		TotalTokens: 1024,
		LastIndexed: time.Now(),
		Languages: []string{"text"},
		AverageFileSize: 512,
	}, nil 
}
func (m *mockStorage) GetWorkspaceWeights(ctx context.Context, workspacePath string) (*types.WorkspaceWeights, error) { 
	return &types.WorkspaceWeights{
		WorkspacePath: workspacePath,
		RelevanceWeight: 0.4,
		RecencyWeight: 0.3,
		DiversityWeight: 0.2,
		EntanglementWeight: 0.1,
	}, nil 
}
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
		SMT: config.SMTConfig{
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
		SMT: config.SMTConfig{
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
	
	// Test selection with constraints
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
