package tokens

import (
	"strings"
	"unicode"
)

// TokenEstimator provides token counting functionality
type TokenEstimator struct {
	model string
}

// NewTokenEstimator creates a new token estimator
func NewTokenEstimator(model string) *TokenEstimator {
	return &TokenEstimator{
		model: model,
	}
}

// EstimateTokens estimates the number of tokens in the given text
// This is a simple approximation - in production this would use
// the actual tokenizer for the specified model
func (te *TokenEstimator) EstimateTokens(text string) int {
	if text == "" {
		return 0
	}
	
	// Simple heuristic: ~4 characters per token for English text
	// This approximates GPT-style tokenization
	charCount := len(text)
	
	// Account for whitespace and punctuation
	wordCount := len(strings.Fields(text))
	punctCount := countPunctuation(text)
	
	// Rough estimation: 0.75 tokens per word + punctuation tokens
	estimatedTokens := int(float64(wordCount)*0.75) + punctCount
	
	// Character-based fallback for edge cases
	charBasedEstimate := charCount / 4
	
	// Use the higher of the two estimates to be conservative
	if charBasedEstimate > estimatedTokens {
		return charBasedEstimate
	}
	
	return estimatedTokens
}

// countPunctuation counts punctuation characters that might be separate tokens
func countPunctuation(text string) int {
	count := 0
	for _, r := range text {
		if unicode.IsPunct(r) {
			count++
		}
	}
	return count
}
