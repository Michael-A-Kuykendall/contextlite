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