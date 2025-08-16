package features

import (
	"strings"
)

// TokenCounter provides simple token counting
type TokenCounter struct {
	modelID string
}

// NewTokenCounter creates a new token counter
func NewTokenCounter(modelID string) *TokenCounter {
	return &TokenCounter{modelID: modelID}
}

// CountTokens estimates token count for text (simple word-based approximation)
func (tc *TokenCounter) CountTokens(text string) int {
	if text == "" {
		return 0
	}
	
	// Simple approximation: split on whitespace and punctuation
	words := strings.Fields(text)
	
	// Rough estimate: 1.3 tokens per word (accounting for subword tokenization)
	tokenCount := int(float64(len(words)) * 1.3)
	
	// Minimum 1 token for non-empty text
	if tokenCount == 0 && len(strings.TrimSpace(text)) > 0 {
		tokenCount = 1
	}
	
	return tokenCount
}
