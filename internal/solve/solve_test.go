package solve

import (
	"testing"
)

func TestZ3Optimizer_Creation(t *testing.T) {
	// Test Z3 optimizer creation (should work even without Z3 binary)
	optimizer := NewZ3Optimizer("", 5000)
	if optimizer == nil {
		t.Fatal("Z3 optimizer is nil")
	}
}

func TestCheckZ3Available_NoBinary(t *testing.T) {
	// Test Z3 availability check with no binary path
	err := CheckZ3Available("")
	if err == nil {
		t.Error("Expected error when Z3 binary path is empty")
	}
}

func TestBruteForceVerifier_Creation(t *testing.T) {
	// Test brute force verifier creation
	verifier := NewBruteForceVerifier()
	if verifier == nil {
		t.Fatal("Brute force verifier is nil")
	}
}
