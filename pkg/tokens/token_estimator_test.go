package tokens

import (
	"testing"
)

func TestTokenEstimator_EstimateTokens(t *testing.T) {
	estimator := NewTokenEstimator("gpt-4")
	
	tests := []struct {
		name     string
		text     string
		expected int
		tolerance int // Allow some tolerance in estimation
	}{
		{
			name:     "empty string",
			text:     "",
			expected: 0,
			tolerance: 0,
		},
		{
			name:     "simple sentence",
			text:     "Hello world",
			expected: 2,
			tolerance: 1,
		},
		{
			name:     "longer text",
			text:     "This is a longer sentence with multiple words to test token estimation.",
			expected: 14,
			tolerance: 3,
		},
		{
			name:     "punctuation heavy",
			text:     "Hello, world! How are you? I'm fine, thanks.",
			expected: 12,
			tolerance: 3,
		},
	}
	
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := estimator.EstimateTokens(tt.text)
			
			// Check if result is within tolerance
			diff := result - tt.expected
			if diff < 0 {
				diff = -diff
			}
			
			if diff > tt.tolerance {
				t.Errorf("EstimateTokens() = %v, expected %v (±%v)", result, tt.expected, tt.tolerance)
			}
		})
	}
}

func TestNewTokenEstimator(t *testing.T) {
	estimator := NewTokenEstimator("gpt-4")
	if estimator == nil {
		t.Error("NewTokenEstimator() returned nil")
	}
	if estimator.model != "gpt-4" {
		t.Errorf("NewTokenEstimator() model = %v, expected %v", estimator.model, "gpt-4")
	}
}
