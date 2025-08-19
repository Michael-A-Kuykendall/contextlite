package middleware

import (
	"net/http"
	"net/http/httptest"
	"testing"
)

func TestRateLimiter_BasicFunctionality(t *testing.T) {
	config := RateLimiterConfig{
		RequestsPerMinute: 60,
		Burst:             3,
		Enabled:           true,
		EndpointSpecific:  map[string]int{},
	}

	rl := NewRateLimiter(config)
	middleware := rl.Middleware()

	// Create a simple handler for testing
	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
		w.Write([]byte("OK"))
	})

	wrappedHandler := middleware(handler)

	// Test that requests within burst limit succeed
	for i := 0; i < 3; i++ {
		req := httptest.NewRequest("GET", "/api/v1/test", nil)
		req.RemoteAddr = "192.168.1.1:12345"
		w := httptest.NewRecorder()

		wrappedHandler.ServeHTTP(w, req)

		if w.Code != http.StatusOK {
			t.Errorf("Request %d should succeed, got status %d", i+1, w.Code)
		}

		// Check rate limit headers
		if w.Header().Get("X-RateLimit-Limit") == "" {
			t.Error("Expected X-RateLimit-Limit header")
		}
	}

	// Test that burst+1 request is rate limited
	req := httptest.NewRequest("GET", "/api/v1/test", nil)
	req.RemoteAddr = "192.168.1.1:12345"
	w := httptest.NewRecorder()

	wrappedHandler.ServeHTTP(w, req)

	if w.Code != http.StatusTooManyRequests {
		t.Errorf("Expected rate limit (429), got status %d", w.Code)
	}

	// Check rate limit headers on 429 response
	if w.Header().Get("Retry-After") == "" {
		t.Error("Expected Retry-After header on 429 response")
	}
}

func TestRateLimiter_EndpointSpecificLimits(t *testing.T) {
	config := RateLimiterConfig{
		RequestsPerMinute: 60,
		Burst:             5,
		Enabled:           true,
		EndpointSpecific: map[string]int{
			"/api/v1/query": 30, // Lower limit for query endpoint
		},
	}

	rl := NewRateLimiter(config)
	middleware := rl.Middleware()

	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
	})

	wrappedHandler := middleware(handler)

	// Test that query endpoint gets different rate limit
	req := httptest.NewRequest("GET", "/api/v1/query", nil)
	req.RemoteAddr = "192.168.1.2:12345"
	w := httptest.NewRecorder()

	wrappedHandler.ServeHTTP(w, req)

	if w.Code != http.StatusOK {
		t.Errorf("Query request should succeed, got status %d", w.Code)
	}

	// The rate limit header should reflect the endpoint-specific limit
	limitHeader := w.Header().Get("X-RateLimit-Limit")
	if limitHeader != "30" {
		t.Errorf("Expected rate limit of 30 for query endpoint, got %s", limitHeader)
	}
}

func TestRateLimiter_DifferentIPs(t *testing.T) {
	config := RateLimiterConfig{
		RequestsPerMinute: 60,
		Burst:             2,
		Enabled:           true,
		EndpointSpecific:  map[string]int{},
	}

	rl := NewRateLimiter(config)
	middleware := rl.Middleware()

	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
	})

	wrappedHandler := middleware(handler)

	// Exhaust rate limit for first IP
	for i := 0; i < 2; i++ {
		req := httptest.NewRequest("GET", "/api/v1/test", nil)
		req.RemoteAddr = "192.168.1.1:12345"
		w := httptest.NewRecorder()
		wrappedHandler.ServeHTTP(w, req)
		
		if w.Code != http.StatusOK {
			t.Errorf("Request %d for IP1 should succeed", i+1)
		}
	}

	// Third request from same IP should be rate limited
	req1 := httptest.NewRequest("GET", "/api/v1/test", nil)
	req1.RemoteAddr = "192.168.1.1:12345"
	w1 := httptest.NewRecorder()
	wrappedHandler.ServeHTTP(w1, req1)

	if w1.Code != http.StatusTooManyRequests {
		t.Errorf("Expected rate limit for IP1, got status %d", w1.Code)
	}

	// But request from different IP should succeed
	req2 := httptest.NewRequest("GET", "/api/v1/test", nil)
	req2.RemoteAddr = "192.168.1.2:12345"
	w2 := httptest.NewRecorder()
	wrappedHandler.ServeHTTP(w2, req2)

	if w2.Code != http.StatusOK {
		t.Errorf("Request from IP2 should succeed, got status %d", w2.Code)
	}
}

func TestRateLimiter_HealthCheckExemption(t *testing.T) {
	config := RateLimiterConfig{
		RequestsPerMinute: 1, // Very low limit
		Burst:             1,
		Enabled:           true,
		EndpointSpecific:  map[string]int{},
	}

	rl := NewRateLimiter(config)
	middleware := rl.Middleware()

	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
	})

	wrappedHandler := middleware(handler)

	// Exhaust rate limit with regular request
	req := httptest.NewRequest("GET", "/api/v1/test", nil)
	req.RemoteAddr = "192.168.1.1:12345"
	w := httptest.NewRecorder()
	wrappedHandler.ServeHTTP(w, req)

	if w.Code != http.StatusOK {
		t.Error("First request should succeed")
	}

	// Second regular request should be rate limited
	req2 := httptest.NewRequest("GET", "/api/v1/test", nil)
	req2.RemoteAddr = "192.168.1.1:12345"
	w2 := httptest.NewRecorder()
	wrappedHandler.ServeHTTP(w2, req2)

	if w2.Code != http.StatusTooManyRequests {
		t.Error("Second request should be rate limited")
	}

	// But health check should still work
	healthReq := httptest.NewRequest("GET", "/health", nil)
	healthReq.RemoteAddr = "192.168.1.1:12345"
	healthW := httptest.NewRecorder()
	wrappedHandler.ServeHTTP(healthW, healthReq)

	if healthW.Code != http.StatusOK {
		t.Errorf("Health check should bypass rate limiting, got status %d", healthW.Code)
	}
}

func TestRateLimiter_Disabled(t *testing.T) {
	config := RateLimiterConfig{
		RequestsPerMinute: 1, // Very low limit
		Burst:             1,
		Enabled:           false, // Disabled
		EndpointSpecific:  map[string]int{},
	}

	rl := NewRateLimiter(config)
	middleware := rl.Middleware()

	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
	})

	wrappedHandler := middleware(handler)

	// Multiple requests should all succeed when disabled
	for i := 0; i < 5; i++ {
		req := httptest.NewRequest("GET", "/api/v1/test", nil)
		req.RemoteAddr = "192.168.1.1:12345"
		w := httptest.NewRecorder()
		wrappedHandler.ServeHTTP(w, req)

		if w.Code != http.StatusOK {
			t.Errorf("Request %d should succeed when rate limiting disabled, got status %d", i+1, w.Code)
		}
	}
}

func TestRateLimiter_XForwardedFor(t *testing.T) {
	config := RateLimiterConfig{
		RequestsPerMinute: 60,
		Burst:             2,
		Enabled:           true,
		EndpointSpecific:  map[string]int{},
	}

	rl := NewRateLimiter(config)
	middleware := rl.Middleware()

	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
	})

	wrappedHandler := middleware(handler)

	// Use X-Forwarded-For header
	req1 := httptest.NewRequest("GET", "/api/v1/test", nil)
	req1.RemoteAddr = "10.0.0.1:12345"
	req1.Header.Set("X-Forwarded-For", "203.0.113.1")
	w1 := httptest.NewRecorder()
	wrappedHandler.ServeHTTP(w1, req1)

	if w1.Code != http.StatusOK {
		t.Error("First request should succeed")
	}

	req2 := httptest.NewRequest("GET", "/api/v1/test", nil)
	req2.RemoteAddr = "10.0.0.1:12345"
	req2.Header.Set("X-Forwarded-For", "203.0.113.1")
	w2 := httptest.NewRecorder()
	wrappedHandler.ServeHTTP(w2, req2)

	if w2.Code != http.StatusOK {
		t.Error("Second request should succeed")
	}

	// Third request should be rate limited
	req3 := httptest.NewRequest("GET", "/api/v1/test", nil)
	req3.RemoteAddr = "10.0.0.1:12345"
	req3.Header.Set("X-Forwarded-For", "203.0.113.1")
	w3 := httptest.NewRecorder()
	wrappedHandler.ServeHTTP(w3, req3)

	if w3.Code != http.StatusTooManyRequests {
		t.Errorf("Third request should be rate limited, got status %d", w3.Code)
	}
}

func TestDefaultRateLimiterConfig(t *testing.T) {
	config := DefaultRateLimiterConfig()

	if config.RequestsPerMinute != 60 {
		t.Errorf("Expected default requests per minute of 60, got %d", config.RequestsPerMinute)
	}

	if config.Burst != 10 {
		t.Errorf("Expected default burst of 10, got %d", config.Burst)
	}

	if !config.Enabled {
		t.Error("Expected rate limiting to be enabled by default")
	}

	if config.EndpointSpecific["/api/v1/query"] != 30 {
		t.Error("Expected query endpoint to have 30 requests per minute")
	}

	if config.EndpointSpecific["/api/v1/enterprise"] != 100 {
		t.Error("Expected enterprise endpoint to have 100 requests per minute")
	}
}
