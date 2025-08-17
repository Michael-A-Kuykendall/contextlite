package features

import "testing"

func TestNewTokenCounter(t *testing.T) {
	counter := NewTokenCounter("test-model")
	if counter == nil {
		t.Fatal("NewTokenCounter returned nil")
	}
}

func TestTokenCounter_CountTokens(t *testing.T) {
	counter := NewTokenCounter("test-model")
	
	// Test normal text
	count := counter.CountTokens("Hello world, how are you?")
	if count <= 0 {
		t.Errorf("Expected positive token count for normal text, got %d", count)
	}
	
	// Test empty text
	count = counter.CountTokens("")
	if count != 0 {
		t.Errorf("Expected 0 tokens for empty text, got %d", count)
	}
	
	// Test single word
	count = counter.CountTokens("Hello")
	if count <= 0 {
		t.Errorf("Expected positive token count for single word, got %d", count)
	}
	
	// Test whitespace only
	count = counter.CountTokens("   \n\t   ")
	if count != 0 {
		t.Errorf("Expected 0 tokens for whitespace only, got %d", count)
	}
	
	// Test with very long text
	longText := ""
	for i := 0; i < 1000; i++ {
		longText += "word "
	}
	count = counter.CountTokens(longText)
	if count <= 100 {
		t.Errorf("Expected large token count for long text, got %d", count)
	}
}

func TestTokenCounter_CountTokensSpecificCoverage(t *testing.T) {
	counter := NewTokenCounter("test-model")
	
	// Test the specific case where:
	// 1. tokenCount becomes 0 after multiplication
	// 2. len(strings.TrimSpace(text)) > 0
	// This happens when strings.Fields returns empty but content exists
	
	// Test with only punctuation (no whitespace fields but has content)
	testCases := []string{
		"!@#",        // Just punctuation
		"...",        // Just dots  
		"===",        // Just equals
		"+++",        // Just plus
		"###",        // Just hash
		"***",        // Just asterisk
		"^^^",        // Just caret
		"&&&",        // Just ampersand
		"|||",        // Just pipe
		"$$$",        // Just dollar
	}
	
	for _, testCase := range testCases {
		count := counter.CountTokens(testCase)
		// These should all trigger the minimum 1 token condition
		// because strings.Fields(testCase) returns [] (empty slice)
		// so len(words) = 0, tokenCount = int(0 * 1.3) = 0
		// but len(strings.TrimSpace(testCase)) > 0, so tokenCount becomes 1
		if count != 1 {
			t.Errorf("Expected 1 token for '%s', got %d", testCase, count)
		}
	}
	
	// Also test case where tokenCount > 0 initially (normal path)
	normalCase := "hello world"
	count := counter.CountTokens(normalCase)
	// strings.Fields("hello world") = ["hello", "world"], len = 2
	// tokenCount = int(2 * 1.3) = int(2.6) = 2
	// condition "tokenCount == 0" is false, so doesn't enter if
	wordsInNormal := 2
	expectedNormal := int(float64(wordsInNormal) * 1.3)
	if count != expectedNormal {
		t.Errorf("Expected %d tokens for normal case, got %d", expectedNormal, count)
	}
}