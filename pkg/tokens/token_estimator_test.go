package tokens

import (
	"strings"
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

func TestTokenEstimator_DifferentModels(t *testing.T) {
	models := []string{"gpt-4", "gpt-3.5-turbo", "claude-3", "text-davinci-003"}
	
	for _, model := range models {
		t.Run(model, func(t *testing.T) {
			estimator := NewTokenEstimator(model)
			if estimator == nil {
				t.Errorf("NewTokenEstimator() returned nil for model %s", model)
			}
			if estimator.model != model {
				t.Errorf("NewTokenEstimator() model = %v, expected %v", estimator.model, model)
			}
			
			// Test basic functionality
			result := estimator.EstimateTokens("test text")
			if result <= 0 {
				t.Errorf("EstimateTokens() should return positive value, got %d", result)
			}
		})
	}
}

func TestTokenEstimator_CodeSamples(t *testing.T) {
	estimator := NewTokenEstimator("gpt-4")
	
	codeSnippets := []struct {
		name string
		code string
	}{
		{
			name: "go_function",
			code: `func main() {
				fmt.Println("Hello, World!")
			}`,
		},
		{
			name: "json_data",
			code: `{
				"name": "test",
				"value": 123,
				"items": ["a", "b", "c"]
			}`,
		},
		{
			name: "sql_query",
			code: "SELECT * FROM users WHERE id = 1 AND name LIKE '%test%'",
		},
		{
			name: "markdown_text",
			code: `# Title
			
			This is a **bold** text with [link](http://example.com).
			
			- Item 1
			- Item 2`,
		},
	}
	
	for _, snippet := range codeSnippets {
		t.Run(snippet.name, func(t *testing.T) {
			tokens := estimator.EstimateTokens(snippet.code)
			if tokens <= 0 {
				t.Errorf("Expected positive token count for code snippet, got %d", tokens)
			}
		})
	}
}

func TestTokenEstimator_EdgeCases(t *testing.T) {
	estimator := NewTokenEstimator("gpt-4")
	
	tests := []struct {
		name string
		text string
	}{
		{
			name: "only_whitespace",
			text: "   \n\t   ",
		},
		{
			name: "only_punctuation",
			text: "!@#$%^&*()",
		},
		{
			name: "mixed_languages",
			text: "Hello 世界 مرحبا",
		},
		{
			name: "very_long_word",
			text: strings.Repeat("a", 1000),
		},
		{
			name: "unicode_chars",
			text: "🚀 🌟 ✨ 💫",
		},
	}
	
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			tokens := estimator.EstimateTokens(test.text)
			// Should not panic and should return non-negative count
			if tokens < 0 {
				t.Errorf("Token count should not be negative, got %d", tokens)
			}
		})
	}
}

func TestTokenEstimator_LargeText(t *testing.T) {
	estimator := NewTokenEstimator("gpt-4")
	
	// Generate large text
	baseText := "This is a sample sentence with multiple words and punctuation. "
	largeText := strings.Repeat(baseText, 1000) // ~60k characters
	
	tokens := estimator.EstimateTokens(largeText)
	if tokens <= 0 {
		t.Errorf("Expected positive token count for large text, got %d", tokens)
	}
}

func TestTokenEstimator_Consistency(t *testing.T) {
	estimator := NewTokenEstimator("gpt-4")
	
	text := "This is a test sentence for consistency checking."
	
	// Multiple calls should return the same result
	result1 := estimator.EstimateTokens(text)
	result2 := estimator.EstimateTokens(text)
	result3 := estimator.EstimateTokens(text)
	
	if result1 != result2 || result2 != result3 {
		t.Errorf("Token estimation should be consistent: %d, %d, %d", result1, result2, result3)
	}
}

func TestTokenEstimator_Scaling(t *testing.T) {
	estimator := NewTokenEstimator("gpt-4")
	
	// Test scaling behavior
	single := estimator.EstimateTokens("word")
	double := estimator.EstimateTokens("word word")
	triple := estimator.EstimateTokens("word word word")
	
	if double <= single {
		t.Errorf("Double text should have more tokens than single: single=%d, double=%d", single, double)
	}
	
	if triple <= double {
		t.Errorf("Triple text should have more tokens than double: double=%d, triple=%d", double, triple)
	}
}

func TestTokenEstimator_EmptyModel(t *testing.T) {
	estimator := NewTokenEstimator("")
	if estimator == nil {
		t.Error("NewTokenEstimator() should handle empty model string")
	}
	
	result := estimator.EstimateTokens("test text")
	if result < 0 {
		t.Errorf("EstimateTokens() should not return negative value, got %d", result)
	}
}

func TestTokenEstimator_BoundaryConditions(t *testing.T) {
	estimator := NewTokenEstimator("gpt-4")
	
	tests := []struct {
		name string
		text string
	}{
		{
			name: "single_character",
			text: "a",
		},
		{
			name: "single_space",
			text: " ",
		},
		{
			name: "single_newline",
			text: "\n",
		},
		{
			name: "single_punctuation",
			text: ".",
		},
		{
			name: "single_number",
			text: "5",
		},
	}
	
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			tokens := estimator.EstimateTokens(test.text)
			if tokens < 0 {
				t.Errorf("Token count should not be negative for '%s', got %d", test.name, tokens)
			}
		})
	}
}

// Benchmark tests
func BenchmarkTokenEstimator_SmallText(b *testing.B) {
	estimator := NewTokenEstimator("gpt-4")
	text := "This is a small test text with a few words."
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		estimator.EstimateTokens(text)
	}
}

func BenchmarkTokenEstimator_MediumText(b *testing.B) {
	estimator := NewTokenEstimator("gpt-4")
	text := strings.Repeat("This is a medium-sized test text. ", 50)
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		estimator.EstimateTokens(text)
	}
}

func BenchmarkTokenEstimator_LargeText(b *testing.B) {
	estimator := NewTokenEstimator("gpt-4")
	text := strings.Repeat("This is a large test text. ", 500)
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		estimator.EstimateTokens(text)
	}
}
