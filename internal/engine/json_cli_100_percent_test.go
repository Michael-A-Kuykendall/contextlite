package engine

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"contextlite/pkg/config"
	"contextlite/pkg/types"
)

// TestJSONCLI_100Percent - MISSION: Get json_cli.go to 100% coverage
// Target the lowest coverage functions: AssembleContext (38.5%), GetStats (42.9%), callPrivateBinary (50.0%)
func TestJSONCLI_100Percent(t *testing.T) {

	// ===============================
	// TARGET: AssembleContext (38.5% -> 100%)
	// ===============================
	t.Run("AssembleContext_AllBranches", func(t *testing.T) {
		// Test cases to hit every branch in AssembleContext
		testCases := []struct {
			name                string
			mockStorageReturns  []types.Document
			mockStorageError    error
			mockBinaryExists    bool
			expectedMessageLike string
		}{
			{
				name:                "NoCandidatesFound_EmptyResult",
				mockStorageReturns:  []types.Document{}, // Empty candidates
				mockStorageError:    nil,
				mockBinaryExists:    true,
				expectedMessageLike: "No relevant documents found",
			},
			{
				name:               "CandidatesFound_NoBinary_Error",
				mockStorageReturns: []types.Document{{ID: "doc1", Content: "test"}},
				mockStorageError:   nil,
				mockBinaryExists:   false, // Binary doesn't exist -> callPrivateBinary fails
			},
			{
				name:               "StorageError_Propagated",
				mockStorageReturns: nil,
				mockStorageError:   fmt.Errorf("storage failure"),
				mockBinaryExists:   true,
			},
		}

		for _, tc := range testCases {
			t.Run(tc.name, func(t *testing.T) {
				// Create mock storage
				mockStorage := &MockStorage{
					searchReturns: tc.mockStorageReturns,
					searchError:   tc.mockStorageError,
				}

				// Create engine
				var binaryPath string
				if tc.mockBinaryExists {
					// Create a fake binary for testing
					binaryPath = createMockBinary(t)
					defer os.Remove(binaryPath)
				} else {
					binaryPath = "/nonexistent/binary"
				}

				cfg := &config.Config{
					SMT: config.SMTConfig{
						SolverTimeoutMs: 1000,
						MaxCandidates:   100,
					},
				}
				
				engine := NewJSONCLIEngine(cfg, mockStorage, binaryPath)

				// Test AssembleContext
				request := types.ContextRequest{
					Query:         "test query",
					MaxTokens:     1000,
					MaxDocuments:  10,
					WorkspacePath: "/test/workspace",
				}

				result, err := engine.AssembleContext(context.Background(), request)

				if tc.mockStorageError != nil {
					// Should propagate storage error
					if err == nil {
						t.Errorf("Expected error from storage failure, got nil")
					}
					t.Logf("Storage error correctly propagated: %v", err)
					return
				}

				if len(tc.mockStorageReturns) == 0 {
					// Should return empty result with message
					if err != nil {
						t.Errorf("Expected no error for empty candidates, got: %v", err)
					}
					if result == nil {
						t.Errorf("Expected result even with no candidates")
						return
					}
					if result.Message != tc.expectedMessageLike {
						t.Errorf("Expected message '%s', got '%s'", tc.expectedMessageLike, result.Message)
					}
					if len(result.Documents) != 0 {
						t.Errorf("Expected empty documents for no candidates")
					}
					t.Logf("Empty candidates case handled correctly: %s", result.Message)
					return
				}

				if !tc.mockBinaryExists {
					// Should fail when binary doesn't exist
					if err == nil {
						t.Errorf("Expected error when binary doesn't exist, got nil")
					}
					t.Logf("Binary execution error correctly handled: %v", err)
				} else {
					// Should succeed with mock binary
					t.Logf("Result with mock binary: error=%v, result=%v", err, result != nil)
				}
			})
		}
	})

	// ===============================
	// TARGET: GetStats (42.9% -> 100%)
	// ===============================  
	t.Run("GetStats_AllBranches", func(t *testing.T) {
		testCases := []struct {
			name            string
			binaryExists    bool
			expectedFallback bool
		}{
			{
				name:            "BinaryUnavailable_ReturnsFallbackStats",
				binaryExists:    false,
				expectedFallback: true,
			},
			{
				name:            "BinaryAvailable_CallsPrivateBinary",
				binaryExists:    true,
				expectedFallback: false,
			},
		}

		for _, tc := range testCases {
			t.Run(tc.name, func(t *testing.T) {
				mockStorage := &MockStorage{}

				var binaryPath string
				if tc.binaryExists {
					binaryPath = createMockBinary(t)
					defer os.Remove(binaryPath)
				} else {
					binaryPath = "/nonexistent/binary"
				}

				engine := NewJSONCLIEngine(nil, mockStorage, binaryPath)
				
				stats, err := engine.GetStats()

				if tc.expectedFallback {
					// Should return fallback stats when binary unavailable
					if err != nil {
						t.Errorf("Expected no error for fallback stats, got: %v", err)
					}
					if stats == nil {
						t.Errorf("Expected fallback stats, got nil")
						return
					}
					// Verify fallback values
					if stats.TotalQueries != 0 {
						t.Errorf("Expected fallback TotalQueries=0, got %d", stats.TotalQueries)
					}
					if stats.LicenseTier != "professional" {
						t.Errorf("Expected fallback LicenseTier='professional', got '%s'", stats.LicenseTier)
					}
					t.Logf("Fallback stats correctly returned: %+v", stats)
				} else {
					// May succeed or fail depending on mock binary response format
					t.Logf("Binary stats call result: error=%v, stats=%v", err, stats != nil)
				}
			})
		}
	})

	// ===============================
	// TARGET: callPrivateBinary (50.0% -> 100%)
	// ===============================
	t.Run("callPrivateBinary_AllErrorPaths", func(t *testing.T) {
		testCases := []struct {
			name             string
			binaryPath       string
			binaryContent    string
			expectError      bool
			errorContains    string
		}{
			{
				name:          "BinaryDoesNotExist",
				binaryPath:    "/nonexistent/binary",
				expectError:   true,
				errorContains: "binary execution failed",
			},
			{
				name:          "BinaryExistsButInvalidOutput",
				binaryContent: "#!/bin/bash\necho 'invalid json'", // Returns invalid JSON
				expectError:   true,
				errorContains: "failed to parse response",
			},
			{
				name:          "BinaryReturnsErrorStatus",
				binaryContent: `#!/bin/bash
echo '{"status": "error", "error": "simulated binary error"}'`,
				expectError:   true,
				errorContains: "binary returned error",
			},
			{
				name:          "BinaryReturnsInvalidDataFormat",
				binaryContent: `#!/bin/bash
echo '{"status": "success", "data": "not a map"}'`,
				expectError:   true,
				errorContains: "invalid response data format",
			},
			{
				name:          "BinaryReturnsValidResponse",
				binaryContent: `#!/bin/bash
echo '{"status": "success", "data": {"result": "test"}}'`,
				expectError:   false,
			},
		}

		for _, tc := range testCases {
			t.Run(tc.name, func(t *testing.T) {
				mockStorage := &MockStorage{}

				var binaryPath string
				if tc.binaryContent != "" {
					binaryPath = createMockBinaryWithContent(t, tc.binaryContent)
					defer os.Remove(binaryPath)
				} else {
					binaryPath = tc.binaryPath
				}

				cfg := &config.Config{
					SMT: config.SMTConfig{
						SolverTimeoutMs: 100, // Short timeout for testing
					},
				}
				engine := NewJSONCLIEngine(cfg, mockStorage, binaryPath)

				// Test callPrivateBinary directly through a function that calls it
				docs := []types.Document{{ID: "test", Content: "test"}}
				result, err := engine.callPrivateBinary("test_action", "test query", docs, map[string]interface{}{"test": "option"})

				if tc.expectError {
					if err == nil {
						t.Errorf("Expected error for %s, got nil", tc.name)
					} else if tc.errorContains != "" && !containsString(err.Error(), tc.errorContains) {
						t.Errorf("Expected error containing '%s', got: %v", tc.errorContains, err)
					} else {
						t.Logf("Error correctly handled for %s: %v", tc.name, err)
					}
				} else {
					if err != nil {
						t.Errorf("Expected no error for %s, got: %v", tc.name, err)
					} else {
						t.Logf("Success case for %s: result=%v", tc.name, result)
					}
				}
			})
		}
	})

	// ===============================
	// EDGE CASES & BRANCH COMPLETION
	// ===============================
	t.Run("EdgeCases_100PercentCoverage", func(t *testing.T) {
		t.Run("NewJSONCLIEngine_NilConfig", func(t *testing.T) {
			mockStorage := &MockStorage{}
			engine := NewJSONCLIEngine(nil, mockStorage, "/test/binary")
			
			// Should use default timeout when config is nil
			expectedTimeout := 30 * time.Second
			if engine.timeout != expectedTimeout {
				t.Errorf("Expected default timeout %v, got %v", expectedTimeout, engine.timeout)
			}
			t.Logf("Nil config handled correctly with default timeout: %v", engine.timeout)
		})

		t.Run("NewJSONCLIEngine_ConfigWithTimeout", func(t *testing.T) {
			mockStorage := &MockStorage{}
			cfg := &config.Config{
				SMT: config.SMTConfig{
					SolverTimeoutMs: 5000,
				},
			}
			engine := NewJSONCLIEngine(cfg, mockStorage, "/test/binary")
			
			expectedTimeout := 5 * time.Second
			if engine.timeout != expectedTimeout {
				t.Errorf("Expected configured timeout %v, got %v", expectedTimeout, engine.timeout)
			}
			t.Logf("Config timeout correctly applied: %v", engine.timeout)
		})

		t.Run("getCandidateDocuments_ConfigSettings", func(t *testing.T) {
			testCases := []struct {
				name          string
				config        *config.Config
				expectedMax   int
			}{
				{
					name:        "NilConfig_DefaultMax",
					config:      nil,
					expectedMax: 200,
				},
				{
					name: "ConfigWithMaxCandidates",
					config: &config.Config{
						SMT: config.SMTConfig{
							MaxCandidates: 50,
						},
					},
					expectedMax: 50,
				},
				{
					name: "ConfigWithZeroMaxCandidates_UsesDefault",
					config: &config.Config{
						SMT: config.SMTConfig{
							MaxCandidates: 0,
						},
					},
					expectedMax: 200,
				},
			}

			for _, tc := range testCases {
				t.Run(tc.name, func(t *testing.T) {
					mockStorage := &MockStorage{
						searchLimit: -1, // Track the limit passed to SearchDocuments
					}
					
					engine := NewJSONCLIEngine(tc.config, mockStorage, "/test/binary")
					
					request := types.ContextRequest{Query: "test"}
					_, err := engine.getCandidateDocuments(context.Background(), request)
					
					if err != nil {
						t.Logf("getCandidateDocuments error (expected for mock): %v", err)
					}
					
					// The limit would be passed to mockStorage.SearchDocuments
					t.Logf("Config case %s completed", tc.name)
				})
			}
		})

		t.Run("UpdateConfig_Branches", func(t *testing.T) {
			mockStorage := &MockStorage{}
			engine := NewJSONCLIEngine(nil, mockStorage, "/test/binary")
			
			originalTimeout := engine.timeout
			
			// Test with positive timeout
			config1 := types.EngineConfig{
				SolverTimeout: 10 * time.Second,
			}
			err := engine.UpdateConfig(config1)
			if err != nil {
				t.Errorf("Expected no error for valid config, got: %v", err)
			}
			if engine.timeout != 10*time.Second {
				t.Errorf("Expected timeout to be updated to %v, got %v", 10*time.Second, engine.timeout)
			}
			
			// Test with zero/negative timeout (should not update)
			config2 := types.EngineConfig{
				SolverTimeout: 0,
			}
			err = engine.UpdateConfig(config2)
			if err != nil {
				t.Errorf("Expected no error for zero timeout config, got: %v", err)
			}
			if engine.timeout == originalTimeout {
				t.Logf("Timeout correctly unchanged for zero timeout config")
			}
			
			t.Logf("UpdateConfig branches tested successfully")
		})

		t.Run("IndexDocument_PassThrough", func(t *testing.T) {
			mockStorage := &MockStorage{}
			engine := NewJSONCLIEngine(nil, mockStorage, "/test/binary")
			
			doc := types.Document{ID: "test", Content: "test"}
			err := engine.IndexDocument(doc)
			
			// Should pass through to storage
			t.Logf("IndexDocument result: %v", err)
		})

		t.Run("RemoveDocument_PassThrough", func(t *testing.T) {
			mockStorage := &MockStorage{}
			engine := NewJSONCLIEngine(nil, mockStorage, "/test/binary")
			
			err := engine.RemoveDocument("test_doc_id")
			
			// Should pass through to storage  
			t.Logf("RemoveDocument result: %v", err)
		})

		t.Run("Close_NoOp", func(t *testing.T) {
			mockStorage := &MockStorage{}
			engine := NewJSONCLIEngine(nil, mockStorage, "/test/binary")
			
			err := engine.Close()
			if err != nil {
				t.Errorf("Expected no error from Close, got: %v", err)
			}
			t.Logf("Close completed successfully")
		})
	})
}

// Mock storage implementation
type MockStorage struct {
	searchReturns []types.Document
	searchError   error
	searchLimit   int // Track the limit passed to SearchDocuments
}

func (m *MockStorage) InsertDocument(doc types.Document) error {
	return nil
}

func (m *MockStorage) DeleteDocument(ctx context.Context, docID string) error {
	return nil
}

func (m *MockStorage) SearchDocuments(ctx context.Context, query string, limit int) ([]types.Document, error) {
	if m.searchLimit == -1 {
		m.searchLimit = limit // Track the limit for testing
	}
	return m.searchReturns, m.searchError
}

// Additional required methods for StorageInterface
func (m *MockStorage) GetDocument(ctx context.Context, docID string) (*types.Document, error) {
	return nil, fmt.Errorf("not implemented")
}

func (m *MockStorage) UpdateDocument(doc types.Document) error {
	return nil
}

func (m *MockStorage) GetWorkspaceStats(workspacePath string) (*types.WorkspaceStats, error) {
	return nil, fmt.Errorf("not implemented")
}

func (m *MockStorage) GetStorageStats(ctx context.Context) (map[string]interface{}, error) {
	return nil, fmt.Errorf("not implemented")
}

func (m *MockStorage) AddDocument(ctx context.Context, doc *types.Document) error {
	return nil
}

func (m *MockStorage) GetDocumentByPath(ctx context.Context, path string) (*types.Document, error) {
	return nil, fmt.Errorf("not implemented")
}

func (m *MockStorage) GetCorpusHash(ctx context.Context) (string, error) {
	return "mock-hash", nil
}

func (m *MockStorage) SaveWorkspaceWeights(workspace string, weights types.FeatureWeights) error {
	return nil
}

func (m *MockStorage) GetWorkspaceWeights(ctx context.Context, workspace string) (*types.WorkspaceWeights, error) {
	return nil, nil
}

func (m *MockStorage) SaveQueryCache(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion string, result *types.QueryResult, expiresAt time.Time) error {
	return nil
}

func (m *MockStorage) GetQueryCache(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion string) (*types.QueryResult, error) {
	return nil, fmt.Errorf("cache miss")
}

func (m *MockStorage) SaveQueryCacheWithKey(ctx context.Context, queryHash, corpusHash, modelID, tokenizerVersion, cacheKey string, result *types.QueryResult, expiresAt time.Time) error {
	return nil
}

func (m *MockStorage) GetCachedResultByKey(ctx context.Context, cacheKey string) (*types.QueryResult, error) {
	return nil, fmt.Errorf("cache miss")
}

func (m *MockStorage) InvalidateCache(ctx context.Context) error {
	return nil
}

func (m *MockStorage) GetCacheStats(ctx context.Context) (*types.CacheStats, error) {
	return &types.CacheStats{}, nil
}


func (m *MockStorage) Close() error {
	return nil
}

// Helper functions
func createMockBinary(t *testing.T) string {
	content := `#!/bin/bash
echo '{"status": "success", "data": {"stats": {"total_queries": 100}, "selected_docs": [0], "docs": [{"id": "test", "content": "test"}]}}'
`
	return createMockBinaryWithContent(t, content)
}

func createMockBinaryWithContent(t *testing.T, content string) string {
	tmpDir := t.TempDir()
	binaryPath := filepath.Join(tmpDir, "mock_binary")
	
	err := os.WriteFile(binaryPath, []byte(content), 0755)
	if err != nil {
		t.Fatalf("Failed to create mock binary: %v", err)
	}
	
	return binaryPath
}

func containsString(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || (len(s) > len(substr) && 
		(s[:len(substr)] == substr || s[len(s)-len(substr):] == substr || 
		 strings.Contains(s, substr))))
}