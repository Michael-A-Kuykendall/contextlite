package api

import (
	"bytes"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"testing"
)

// Tests specifically targeting low-coverage API handlers to boost overall coverage
func TestAPI_CoverageBoost_LicenseHandlers(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("handleLicenseStatus_NoLicense", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/api/v1/license/status", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// License status should always respond
		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Should contain license information
		if _, ok := response["tier"]; !ok {
			t.Error("Response should contain tier information")
		}

		t.Logf("License status response: %+v", response)
	})

	t.Run("handleTrialInfo_Default", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/api/v1/trial/info", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Trial info should always respond
		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		var response map[string]interface{}
		if err := json.NewDecoder(w.Body).Decode(&response); err != nil {
			t.Errorf("Failed to decode response: %v", err)
		}

		// Should contain trial information
		if _, ok := response["trial_active"]; !ok {
			t.Error("Response should contain trial_active field")
		}

		t.Logf("Trial info response: %+v", response)
	})
}

func TestAPI_CoverageBoost_WeightsHandlers(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("handleGetWeights_DefaultWeights", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/api/v1/weights", nil)
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

		// Should contain weight information
		if _, ok := response["relevance"]; !ok {
			t.Error("Response should contain relevance weight")
		}

		t.Logf("Weights response: %+v", response)
	})

	t.Run("handleGetWeights_WithWorkspace", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/api/v1/weights?workspace=/test/workspace", nil)
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

		t.Logf("Workspace weights response: %+v", response)
	})

	t.Run("handleResetWeights_Success", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/api/v1/weights/reset", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Reset weights should succeed
		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		t.Logf("Reset weights response status: %d", w.Code)
	})

	t.Run("handleResetWeights_WithWorkspace", func(t *testing.T) {
		resetData := map[string]interface{}{
			"workspace": "/test/reset/workspace",
		}
		jsonData, _ := json.Marshal(resetData)

		req := httptest.NewRequest("POST", "/api/v1/weights/reset", bytes.NewBuffer(jsonData))
		req.Header.Set("Authorization", "Bearer test-token")
		req.Header.Set("Content-Type", "application/json")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		t.Logf("Reset workspace weights response status: %d", w.Code)
	})
}

func TestAPI_CoverageBoost_CacheHandlers(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("handleCacheStats_Success", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/api/v1/cache/stats", nil)
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

		// Should contain cache statistics
		if _, ok := response["hits"]; !ok {
			t.Error("Response should contain cache hits")
		}

		t.Logf("Cache stats response: %+v", response)
	})

	t.Run("handleInvalidateCache_Success", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/api/v1/cache/invalidate", nil)
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

		// Should confirm cache invalidation
		if _, ok := response["message"]; !ok {
			t.Error("Response should contain confirmation message")
		}

		t.Logf("Cache invalidate response: %+v", response)
	})
}

func TestAPI_CoverageBoost_StorageInfoHandler(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("handleStorageInfo_Success", func(t *testing.T) {
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

		// Should contain storage information
		if _, ok := response["total_documents"]; !ok {
			t.Error("Response should contain total_documents")
		}

		t.Logf("Storage info response: %+v", response)
	})
}

func TestAPI_CoverageBoost_RankHandler(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("handleRank_ValidRequest", func(t *testing.T) {
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

		// Rank endpoint should respond (may return error if documents don't exist)
		if w.Code != http.StatusOK && w.Code != http.StatusBadRequest {
			t.Errorf("Expected status 200 or 400, got %d", w.Code)
		}

		t.Logf("Rank response status: %d", w.Code)
	})

	t.Run("handleRank_EmptyRequest", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/api/v1/rank", bytes.NewBuffer([]byte("{}")))
		req.Header.Set("Authorization", "Bearer test-token")
		req.Header.Set("Content-Type", "application/json")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Empty request should return bad request
		if w.Code != http.StatusBadRequest {
			t.Errorf("Expected status 400 for empty request, got %d", w.Code)
		}

		t.Logf("Empty rank request response status: %d", w.Code)
	})

	t.Run("handleRank_InvalidJSON", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/api/v1/rank", bytes.NewBuffer([]byte("invalid json")))
		req.Header.Set("Authorization", "Bearer test-token")
		req.Header.Set("Content-Type", "application/json")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Invalid JSON should return bad request
		if w.Code != http.StatusBadRequest {
			t.Errorf("Expected status 400 for invalid JSON, got %d", w.Code)
		}

		t.Logf("Invalid JSON rank request response status: %d", w.Code)
	})
}

func TestAPI_CoverageBoost_DocumentHandlers(t *testing.T) {
	server, _, cleanup := setupTestServer(t)
	defer cleanup()

	t.Run("handleAddDocument_ValidDocument", func(t *testing.T) {
		doc := map[string]interface{}{
			"id":      "boost-test-doc",
			"path":    "/test/boost.go",
			"content": "package boost\nfunc Test() {}",
		}
		jsonData, _ := json.Marshal(doc)

		req := httptest.NewRequest("POST", "/api/v1/documents", bytes.NewBuffer(jsonData))
		req.Header.Set("Authorization", "Bearer test-token")
		req.Header.Set("Content-Type", "application/json")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		if w.Code != http.StatusOK && w.Code != http.StatusCreated {
			t.Errorf("Expected status 200 or 201, got %d", w.Code)
		}

		t.Logf("Add document response status: %d", w.Code)
	})

	t.Run("handleAddDocument_InvalidDocument", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/api/v1/documents", bytes.NewBuffer([]byte("invalid json")))
		req.Header.Set("Authorization", "Bearer test-token")
		req.Header.Set("Content-Type", "application/json")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Invalid JSON should return bad request
		if w.Code != http.StatusBadRequest {
			t.Errorf("Expected status 400 for invalid JSON, got %d", w.Code)
		}

		t.Logf("Invalid add document response status: %d", w.Code)
	})

	t.Run("handleDeleteDocument_ExistingDocument", func(t *testing.T) {
		// First add a document to delete
		doc := map[string]interface{}{
			"id":      "delete-test-doc",
			"path":    "/test/delete.go",
			"content": "package delete",
		}
		jsonData, _ := json.Marshal(doc)
		addReq := httptest.NewRequest("POST", "/api/v1/documents", bytes.NewBuffer(jsonData))
		addReq.Header.Set("Authorization", "Bearer test-token")
		addReq.Header.Set("Content-Type", "application/json")
		server.ServeHTTP(httptest.NewRecorder(), addReq)

		// Now delete it
		req := httptest.NewRequest("DELETE", "/api/v1/documents/delete-test-doc", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		t.Logf("Delete document response status: %d", w.Code)
	})

	t.Run("handleDeleteDocument_NonExistentDocument", func(t *testing.T) {
		req := httptest.NewRequest("DELETE", "/api/v1/documents/nonexistent-doc", nil)
		req.Header.Set("Authorization", "Bearer test-token")
		
		w := httptest.NewRecorder()
		server.ServeHTTP(w, req)

		// Deleting non-existent document should succeed or return 404
		if w.Code != http.StatusOK && w.Code != http.StatusNotFound {
			t.Errorf("Expected status 200 or 404, got %d", w.Code)
		}

		t.Logf("Delete non-existent document response status: %d", w.Code)
	})
}