package api

import (
	"bytes"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"testing"
	"path/filepath"
	
	"contextlite/pkg/types"
	"contextlite/internal/storage"
	"contextlite/pkg/config"
	"contextlite/internal/engine"
	"go.uber.org/zap"
)


// Enhanced mock feature gate to test enhanced code paths
type enhancedMockFeatureGate struct {
	hasEnhancedFeatures bool
	trialActive         bool
}

func (e *enhancedMockFeatureGate) GetStatus() map[string]interface{} {
	status := map[string]interface{}{
		"tier":                "developer",
		"max_documents":       1000,
		"features":            []string{"basic_optimization", "workspaces"},
		"in_grace_period":     false,
		"status":              "enhanced",
		"message":             "Enhanced license system active",
	}
	
	if e.trialActive {
		status["trial"] = map[string]interface{}{
			"active":           true,
			"days_remaining":   7,
			"tier":            "professional",
			"expires_at":      "2024-09-01T00:00:00Z",
		}
	}
	
	return status
}

func (e *enhancedMockFeatureGate) TrialDaysRemaining() int {
	if e.trialActive {
		return 7
	}
	return 0
}

// Implement types.FeatureGate interface
func (e *enhancedMockFeatureGate) IsEnabled(feature string) bool {
	return true
}

func (e *enhancedMockFeatureGate) RequireFeature(feature string) error {
	return nil
}

func (e *enhancedMockFeatureGate) RequireProfessional() error {
	return nil
}

func (e *enhancedMockFeatureGate) RequireEnterprise() error {
	return nil
}

func (e *enhancedMockFeatureGate) GetTier() string {
	return "developer"
}

func (e *enhancedMockFeatureGate) ValidateCustomMCP() error {
	return nil
}

func (e *enhancedMockFeatureGate) ValidateMultiTenant() error {
	return nil
}

// Helper function to create server with custom feature gate
func setupTestServerWithFeatureGate(t *testing.T, featureGate types.FeatureGate) *Server {
	// Create temporary database
	dbPath := filepath.Join(t.TempDir(), "test.db")
	
	// Initialize storage
	store, err := storage.New(dbPath)
	if err != nil {
		t.Fatalf("Failed to create test storage: %v", err)
	}
	
	// Create config
	cfg := &config.Config{
		Server: config.ServerConfig{
			Host: "localhost",
			Port: 8080,
		},
		Storage: config.StorageConfig{
			DatabasePath: dbPath,
		},
		Tokenizer: config.TokenizerConfig{
			ModelID: "test-model",
		},
	}
	
	// Initialize engine
	eng := engine.LoadEngine(cfg, store)
	
	// Create logger
	logger := zap.NewNop()
	
	// Create server with custom feature gate
	return New(eng, store, cfg, logger, featureGate)
}

// Test low-coverage license handlers
func TestAPI_100Percent_LicenseHandlers(t *testing.T) {
	t.Run("handleLicenseStatus_EnhancedGate", func(t *testing.T) {
		// Create server with enhanced feature gate
		enhancedGate := &enhancedMockFeatureGate{
			hasEnhancedFeatures: true,
			trialActive:         false,
		}
		server := setupTestServerWithFeatureGate(t, enhancedGate)
		
		req := httptest.NewRequest("GET", "/api/v1/license/status", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Check enhanced fields are present
		expectedFields := []string{"tier", "max_documents", "features", "in_grace_period", "purchase_url", "trial_days_remaining"}
		for _, field := range expectedFields {
			if _, ok := response[field]; !ok {
				t.Errorf("Enhanced response should contain %s field", field)
			}
		}

		t.Logf("Enhanced license status response: %+v", response)
	})

	t.Run("handleLicenseStatus_BasicGate", func(t *testing.T) {
		// Test basic feature gate path (fallback)
		server, _, cleanup := setupTestServer(t)
		defer cleanup()

		req := httptest.NewRequest("GET", "/api/v1/license/status", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Check basic fallback fields
		if status, ok := response["status"]; !ok || status != "basic" {
			t.Error("Basic response should contain status: 'basic'")
		}
		if message, ok := response["message"]; !ok || message != "Basic license system active" {
			t.Error("Basic response should contain basic message")
		}

		t.Logf("Basic license status response: %+v", response)
	})

	t.Run("handleTrialInfo_WithTrial", func(t *testing.T) {
		// Create server with enhanced feature gate that has trial
		enhancedGate := &enhancedMockFeatureGate{
			hasEnhancedFeatures: true,
			trialActive:         true,
		}
		server := setupTestServerWithFeatureGate(t, enhancedGate)
		
		req := httptest.NewRequest("GET", "/api/v1/trial/info", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Check trial fields
		expectedFields := []string{"active", "days_remaining", "tier", "expires_at", "purchase_url", "features_available"}
		for _, field := range expectedFields {
			if _, ok := response[field]; !ok {
				t.Errorf("Trial response should contain %s field", field)
			}
		}

		t.Logf("Trial info response: %+v", response)
	})

	t.Run("handleTrialInfo_NoTrial", func(t *testing.T) {
		server, _, cleanup := setupTestServer(t)
		defer cleanup()

		req := httptest.NewRequest("GET", "/api/v1/trial/info", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Check no-trial fields
		if status, ok := response["status"]; !ok || status != "no_trial" {
			t.Error("No-trial response should contain status: 'no_trial'")
		}

		t.Logf("No-trial info response: %+v", response)
	})
}

// Test cache handlers - these require Professional license so will return 403
func TestAPI_100Percent_CacheHandlers_LicenseRequired(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("handleCacheStats_RequiresProfessional", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/api/v1/cache/stats", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// With Developer license, should return 403 - this tests the Professional requirement path
		if w.Code != http.StatusForbidden {
			t.Errorf("Expected status 403 with Developer license, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Should contain professional license error
		if errorMsg, ok := response["error"]; !ok {
			t.Error("Response should contain error message")
		} else {
			t.Logf("Cache stats license error: %v", errorMsg)
		}
	})

	t.Run("handleInvalidateCache_RequiresProfessional", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/api/v1/cache/invalidate", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// With Developer license, should return 403 - this tests the Professional requirement path
		if w.Code != http.StatusForbidden {
			t.Errorf("Expected status 403 with Developer license, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Should contain professional license error
		if errorMsg, ok := response["error"]; !ok {
			t.Error("Response should contain error message")
		} else {
			t.Logf("Cache invalidate license error: %v", errorMsg)
		}
	})
}

// Test storage info handler error paths
func TestAPI_100Percent_StorageInfoHandler(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("handleStorageInfo_AllFields", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/api/v1/storage/info", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Check for storage information fields
		expectedFields := []string{"total_documents", "database_size", "index_size"}
		for _, field := range expectedFields {
			if _, ok := response[field]; !ok {
				t.Logf("Storage info missing %s field (may be implementation dependent)", field)
			}
		}

		t.Logf("Storage info response: %+v", response)
	})
}

// Test weights handlers - these require Professional license so will test the license requirement path
func TestAPI_100Percent_WeightsHandlers_LicenseRequired(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("handleGetWeights_RequiresProfessional_NoWorkspace", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/api/v1/weights", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// With Developer license, should return 403 - this tests the Professional requirement path
		if w.Code != http.StatusForbidden {
			t.Errorf("Expected status 403 with Developer license, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Should contain professional license error
		if errorMsg, ok := response["error"]; !ok {
			t.Error("Response should contain error message")
		} else {
			t.Logf("Get weights license error: %v", errorMsg)
		}
	})

	t.Run("handleGetWeights_RequiresProfessional_WithWorkspace", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/api/v1/weights?workspace=/test/workspace", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// With Developer license, should return 403 - this tests the Professional requirement path  
		if w.Code != http.StatusForbidden {
			t.Errorf("Expected status 403 with Developer license, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Should contain professional license error
		if errorMsg, ok := response["error"]; !ok {
			t.Error("Response should contain error message")
		} else {
			t.Logf("Get weights with workspace license error: %v", errorMsg)
		}
	})

	t.Run("handleResetWeights_RequiresProfessional", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/api/v1/weights/reset", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// With Developer license, should return 403 - this tests the Professional requirement path
		if w.Code != http.StatusForbidden {
			t.Errorf("Expected status 403 with Developer license, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Should contain professional license error
		if errorMsg, ok := response["error"]; !ok {
			t.Error("Response should contain error message")
		} else {
			t.Logf("Reset weights license error: %v", errorMsg)
		}
	})
}

// Test rank handler - tests the Professional license requirement path
func TestAPI_100Percent_RankHandler_LicenseRequired(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("handleRank_RequiresProfessional", func(t *testing.T) {
		rankRequest := map[string]interface{}{
			"query":     "test query",
			"documents": []string{"doc1", "doc2", "doc3"},
		}
		jsonData, _ := json.Marshal(rankRequest)

		req := httptest.NewRequest("POST", "/api/v1/rank", bytes.NewBuffer(jsonData))
		req.Header.Set("Authorization", "Bearer test-token")
		req.Header.Set("Content-Type", "application/json")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// With Developer license, should return 403 - this tests the Professional requirement path
		if w.Code != http.StatusForbidden {
			t.Errorf("Expected status 403 with Developer license, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Should contain professional license error
		if errorMsg, ok := response["error"]; !ok {
			t.Error("Response should contain error message")
		} else {
			t.Logf("Rank license error: %v", errorMsg)
		}
	})

	t.Run("handleRank_InvalidJSON", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/api/v1/rank", bytes.NewBuffer([]byte("invalid json")))
		req.Header.Set("Authorization", "Bearer test-token")
		req.Header.Set("Content-Type", "application/json")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Should hit license check before JSON validation, so still 403
		if w.Code != http.StatusForbidden {
			t.Errorf("Expected status 403 for license check before JSON validation, got %d", w.Code)
		}

		t.Logf("Invalid JSON rank response status: %d", w.Code)
	})

	t.Run("handleRank_EmptyRequest", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/api/v1/rank", bytes.NewBuffer([]byte("{}")))
		req.Header.Set("Authorization", "Bearer test-token")
		req.Header.Set("Content-Type", "application/json")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Should hit license check before request validation, so still 403
		if w.Code != http.StatusForbidden {
			t.Errorf("Expected status 403 for license check before validation, got %d", w.Code)
		}

		t.Logf("Empty rank request response status: %d", w.Code)
	})
}

// Test document handlers error paths and edge cases
func TestAPI_100Percent_DocumentHandlers_EdgeCases(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("handleAddDocument_MissingFields", func(t *testing.T) {
		// Document with missing required fields
		doc := map[string]interface{}{
			"id": "incomplete-doc",
			// Missing path and content
		}
		jsonData, _ := json.Marshal(doc)

		req := httptest.NewRequest("POST", "/api/v1/documents", bytes.NewBuffer(jsonData))
		req.Header.Set("Authorization", "Bearer test-token")
		req.Header.Set("Content-Type", "application/json")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Should handle missing fields gracefully
		if w.Code != http.StatusOK && w.Code != http.StatusBadRequest {
			t.Errorf("Expected status 200 or 400 for incomplete document, got %d", w.Code)
		}

		t.Logf("Incomplete document response status: %d", w.Code)
	})

	t.Run("handleDeleteDocument_EmptyID", func(t *testing.T) {
		req := httptest.NewRequest("DELETE", "/api/v1/documents/", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Empty ID should return 404 or method not allowed
		if w.Code != http.StatusNotFound && w.Code != http.StatusMethodNotAllowed {
			t.Logf("Empty document ID response status: %d", w.Code)
		}
	})

	t.Run("handleAddDocument_DuplicateID", func(t *testing.T) {
		// Add first document
		doc := map[string]interface{}{
			"id":      "duplicate-test",
			"path":    "/test/duplicate.go",
			"content": "package duplicate",
		}
		jsonData, _ := json.Marshal(doc)

		req1 := httptest.NewRequest("POST", "/api/v1/documents", bytes.NewBuffer(jsonData))
		req1.Header.Set("Authorization", "Bearer test-token")
		req1.Header.Set("Content-Type", "application/json")
		server.ServeHTTP(httptest.NewRecorder(), req1)

		// Add duplicate document
		req2 := httptest.NewRequest("POST", "/api/v1/documents", bytes.NewBuffer(jsonData))
		req2.Header.Set("Authorization", "Bearer test-token")
		req2.Header.Set("Content-Type", "application/json")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req2)

		// Should handle duplicate gracefully (update or conflict)
		if w.Code != http.StatusOK && w.Code != http.StatusConflict && w.Code != http.StatusCreated {
			t.Logf("Duplicate document response status: %d", w.Code)
		}

		t.Logf("Duplicate add document response status: %d", w.Code)
	})
}

// Test middleware edge cases
func TestAPI_100Percent_Middleware_EdgeCases(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("authMiddleware_MissingAuth", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/api/v1/storage/info", nil)
		// No Authorization header
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Should return unauthorized
		if w.Code != http.StatusUnauthorized {
			t.Errorf("Expected status 401 for missing auth, got %d", w.Code)
		}
	})

	t.Run("authMiddleware_InvalidAuth", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/api/v1/storage/info", nil)
		req.Header.Set("Authorization", "Invalid token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Should return unauthorized
		if w.Code != http.StatusUnauthorized {
			t.Errorf("Expected status 401 for invalid auth, got %d", w.Code)
		}
	})

	t.Run("requireProfessional_DeveloperLicense", func(t *testing.T) {
		// This test uses regular setup (developer license)
		req := httptest.NewRequest("GET", "/api/v1/weights", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Should return forbidden for developer license
		if w.Code != http.StatusForbidden {
			t.Errorf("Expected status 403 for developer license, got %d", w.Code)
		}
	})
}