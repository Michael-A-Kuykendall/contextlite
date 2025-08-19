package middleware

import (
	"net/http"
	"strconv"
	"sync"
	"time"

	"golang.org/x/time/rate"
)

// RateLimiterConfig holds configuration for rate limiting
type RateLimiterConfig struct {
	RequestsPerMinute int               `yaml:"requests_per_minute" json:"requests_per_minute"`
	Burst             int               `yaml:"burst" json:"burst"`
	EndpointSpecific  map[string]int    `yaml:"endpoint_specific" json:"endpoint_specific"`
	Enabled           bool              `yaml:"enabled" json:"enabled"`
}

// DefaultRateLimiterConfig returns sensible defaults
func DefaultRateLimiterConfig() RateLimiterConfig {
	return RateLimiterConfig{
		RequestsPerMinute: 60,
		Burst:             10,
		Enabled:           true,
		EndpointSpecific: map[string]int{
			"/api/v1/query":        30,  // Query endpoint is more expensive
			"/api/v1/enterprise":   100, // Enterprise gets higher limits
		},
	}
}

// RateLimiter provides token bucket rate limiting per IP
type RateLimiter struct {
	config   RateLimiterConfig
	limiters map[string]*rate.Limiter
	mu       sync.RWMutex
}

// NewRateLimiter creates a new rate limiter with the given config
func NewRateLimiter(config RateLimiterConfig) *RateLimiter {
	return &RateLimiter{
		config:   config,
		limiters: make(map[string]*rate.Limiter),
	}
}

// getLimiter gets or creates a rate limiter for the given IP and endpoint
func (rl *RateLimiter) getLimiter(ip, endpoint string) *rate.Limiter {
	rl.mu.RLock()
	key := ip + ":" + endpoint
	limiter, exists := rl.limiters[key]
	rl.mu.RUnlock()

	if exists {
		return limiter
	}

	// Determine rate limit for this endpoint
	requestsPerMinute := rl.config.RequestsPerMinute
	if endpointLimit, exists := rl.config.EndpointSpecific[endpoint]; exists {
		requestsPerMinute = endpointLimit
	}

	// Convert per-minute to per-second rate
	ratePerSecond := rate.Limit(float64(requestsPerMinute) / 60.0)
	
	rl.mu.Lock()
	// Double-check to avoid race condition
	if limiter, exists := rl.limiters[key]; exists {
		rl.mu.Unlock()
		return limiter
	}
	
	limiter = rate.NewLimiter(ratePerSecond, rl.config.Burst)
	rl.limiters[key] = limiter
	rl.mu.Unlock()

	return limiter
}

// getClientIP extracts the client IP from the request
func getClientIP(r *http.Request) string {
	// Try X-Forwarded-For header first (for proxies)
	if xff := r.Header.Get("X-Forwarded-For"); xff != "" {
		return xff
	}
	
	// Try X-Real-IP header
	if xri := r.Header.Get("X-Real-IP"); xri != "" {
		return xri
	}
	
	// Fall back to RemoteAddr
	return r.RemoteAddr
}

// Middleware returns the rate limiting middleware function
func (rl *RateLimiter) Middleware() func(http.Handler) http.Handler {
	return func(next http.Handler) http.Handler {
		return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			// Skip rate limiting if disabled
			if !rl.config.Enabled {
				next.ServeHTTP(w, r)
				return
			}

			// Skip rate limiting for health check endpoints
			if r.URL.Path == "/health" || r.URL.Path == "/api/health" {
				next.ServeHTTP(w, r)
				return
			}

			ip := getClientIP(r)
			endpoint := r.URL.Path
			
			// For enterprise endpoints, use a generic key to share limits
			if len(endpoint) > 15 && endpoint[:15] == "/api/v1/enterprise" {
				endpoint = "/api/v1/enterprise"
			}

			limiter := rl.getLimiter(ip, endpoint)
			
			// Determine rate limit for headers
			requestsPerMinute := rl.config.RequestsPerMinute
			if endpointLimit, exists := rl.config.EndpointSpecific[endpoint]; exists {
				requestsPerMinute = endpointLimit
			}
			
			if !limiter.Allow() {
				// Rate limit exceeded - add headers and return 429
				w.Header().Set("X-RateLimit-Limit", strconv.Itoa(requestsPerMinute))
				w.Header().Set("X-RateLimit-Remaining", "0")
				w.Header().Set("X-RateLimit-Reset", strconv.FormatInt(time.Now().Add(time.Minute).Unix(), 10))
				w.Header().Set("Retry-After", "60")
				
				http.Error(w, "Rate limit exceeded. Please try again later.", http.StatusTooManyRequests)
				return
			}

			// Add rate limit headers to successful requests
			w.Header().Set("X-RateLimit-Limit", strconv.Itoa(requestsPerMinute))
			
			// Calculate remaining (approximate, since we don't track exact tokens)
			remaining := rl.config.Burst - 1
			if remaining < 0 {
				remaining = 0
			}
			w.Header().Set("X-RateLimit-Remaining", strconv.Itoa(remaining))
			w.Header().Set("X-RateLimit-Reset", strconv.FormatInt(time.Now().Add(time.Minute).Unix(), 10))

			next.ServeHTTP(w, r)
		})
	}
}

// CleanupOldLimiters removes limiters that haven't been used recently
// Should be called periodically to prevent memory leaks
func (rl *RateLimiter) CleanupOldLimiters() {
	// This is a simple implementation - in production you might want
	// to track last access time and remove truly stale limiters
	rl.mu.Lock()
	defer rl.mu.Unlock()
	
	// For now, just clear all if we have too many
	if len(rl.limiters) > 10000 {
		rl.limiters = make(map[string]*rate.Limiter)
	}
}
