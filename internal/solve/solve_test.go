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

func TestZ3Optimizer_ParseZ3OutputComprehensive(t *testing.T) {
	optimizer := NewZ3Optimizer("", 5000)
	
	// Test case 1: SAT result with solution
	t.Run("sat_with_solution", func(t *testing.T) {
		output := `sat
(obj 1500000)
(define-fun x0 () Int
  1)
(define-fun x1 () Int
  1)
(define-fun x2 () Int
  0)`
		
		result, err := optimizer.parseZ3Output(output)
		if err != nil {
			t.Fatalf("parseZ3Output failed: %v", err)
		}
		
		if result.Status != "sat" {
			t.Errorf("Expected status 'sat', got '%s'", result.Status)
		}
		
		if result.ObjectiveValue != 1500000 {
			t.Errorf("Expected objective 1500000, got %d", result.ObjectiveValue)
		}
		
		expectedSelected := []int{0, 1}
		if len(result.SelectedDocs) != len(expectedSelected) {
			t.Errorf("Expected %d selected docs, got %d", len(expectedSelected), len(result.SelectedDocs))
		}
		
		selectedMap := make(map[int]bool)
		for _, doc := range result.SelectedDocs {
			selectedMap[doc] = true
		}
		
		for _, expected := range expectedSelected {
			if !selectedMap[expected] {
				t.Errorf("Expected document %d to be selected", expected)
			}
		}
		
		t.Logf("SAT result: status=%s, objective=%d, selected=%v", 
			result.Status, result.ObjectiveValue, result.SelectedDocs)
	})
	
	// Test case 2: UNSAT result
	t.Run("unsat", func(t *testing.T) {
		output := `unsat`
		
		result, err := optimizer.parseZ3Output(output)
		if err != nil {
			t.Fatalf("parseZ3Output failed: %v", err)
		}
		
		if result.Status != "unsat" {
			t.Errorf("Expected status 'unsat', got '%s'", result.Status)
		}
		
		if len(result.SelectedDocs) != 0 {
			t.Errorf("Expected no selected docs for unsat, got %v", result.SelectedDocs)
		}
		
		if result.TimedOut {
			t.Error("UNSAT result should not be marked as timed out")
		}
		
		t.Logf("UNSAT result: status=%s", result.Status)
	})
	
	// Test case 3: UNKNOWN result (timeout)
	t.Run("unknown_timeout", func(t *testing.T) {
		output := `unknown`
		
		result, err := optimizer.parseZ3Output(output)
		if err != nil {
			t.Fatalf("parseZ3Output failed: %v", err)
		}
		
		if result.Status != "unknown" {
			t.Errorf("Expected status 'unknown', got '%s'", result.Status)
		}
		
		if !result.TimedOut {
			t.Error("Unknown result should be marked as timed out")
		}
		
		t.Logf("UNKNOWN result: status=%s, timedOut=%v", result.Status, result.TimedOut)
	})
	
	// Test case 4: Empty output
	t.Run("empty_output", func(t *testing.T) {
		output := ``
		
		result, err := optimizer.parseZ3Output(output)
		if err != nil {
			t.Fatalf("parseZ3Output failed: %v", err)
		}
		
		if result.Status != "" {
			t.Errorf("Expected empty status for empty output, got '%s'", result.Status)
		}
		
		t.Logf("Empty output result: status='%s'", result.Status)
	})
	
	// Test case 5: SAT with negative objective
	t.Run("sat_negative_objective", func(t *testing.T) {
		output := `sat
(obj -500000)
(define-fun x0 () Int
  0)
(define-fun x1 () Int
  1)`
		
		result, err := optimizer.parseZ3Output(output)
		if err != nil {
			t.Fatalf("parseZ3Output failed: %v", err)
		}
		
		if result.ObjectiveValue != -500000 {
			t.Errorf("Expected negative objective -500000, got %d", result.ObjectiveValue)
		}
		
		t.Logf("Negative objective result: objective=%d", result.ObjectiveValue)
	})
	
	// Test case 6: SAT with no variables selected (all zeros)
	t.Run("sat_no_selection", func(t *testing.T) {
		output := `sat
(obj 0)
(define-fun x0 () Int
  0)
(define-fun x1 () Int
  0)
(define-fun x2 () Int
  0)`
		
		result, err := optimizer.parseZ3Output(output)
		if err != nil {
			t.Fatalf("parseZ3Output failed: %v", err)
		}
		
		if len(result.SelectedDocs) != 0 {
			t.Errorf("Expected no selected docs, got %v", result.SelectedDocs)
		}
		
		if result.ObjectiveValue != 0 {
			t.Errorf("Expected objective 0, got %d", result.ObjectiveValue)
		}
		
		t.Logf("No selection result: objective=%d, selected=%v", 
			result.ObjectiveValue, result.SelectedDocs)
	})
	
	// Test case 7: Malformed objective line
	t.Run("malformed_objective", func(t *testing.T) {
		output := `sat
(obj invalid_number)
(define-fun x0 () Int
  1)`
		
		result, err := optimizer.parseZ3Output(output)
		if err != nil {
			t.Fatalf("parseZ3Output failed: %v", err)
		}
		
		// Should handle malformed objective gracefully
		if result.ObjectiveValue != 0 {
			t.Errorf("Expected default objective 0 for malformed objective, got %d", result.ObjectiveValue)
		}
		
		t.Logf("Malformed objective result: objective=%d", result.ObjectiveValue)
	})
	
	// Test case 8: Malformed variable value
	t.Run("malformed_variable", func(t *testing.T) {
		output := `sat
(obj 1000000)
(define-fun x0 () Int
  1)
(define-fun x1 () Int
  invalid_value)
(define-fun x2 () Int
  0)`
		
		result, err := optimizer.parseZ3Output(output)
		if err != nil {
			t.Fatalf("parseZ3Output failed: %v", err)
		}
		
		// Should only include valid variables
		if len(result.SelectedDocs) != 1 || result.SelectedDocs[0] != 0 {
			t.Errorf("Expected only doc 0 selected due to malformed x1, got %v", result.SelectedDocs)
		}
		
		t.Logf("Malformed variable result: selected=%v", result.SelectedDocs)
	})
	
	// Test case 9: Mixed format with extra lines
	t.Run("mixed_format_extra_lines", func(t *testing.T) {
		output := `sat
some extra line
(obj 750000)
another line
(define-fun x0 () Int
  1)
extra content
(define-fun x3 () Int
  1)
more extra content`
		
		result, err := optimizer.parseZ3Output(output)
		if err != nil {
			t.Fatalf("parseZ3Output failed: %v", err)
		}
		
		if result.ObjectiveValue != 750000 {
			t.Errorf("Expected objective 750000, got %d", result.ObjectiveValue)
		}
		
		expectedDocs := []int{0, 3}
		if len(result.SelectedDocs) != len(expectedDocs) {
			t.Errorf("Expected %d docs selected, got %d", len(expectedDocs), len(result.SelectedDocs))
		}
		
		t.Logf("Mixed format result: objective=%d, selected=%v", 
			result.ObjectiveValue, result.SelectedDocs)
	})
	
	// Test case 10: Variable with closing parenthesis handling
	t.Run("variable_with_closing_paren", func(t *testing.T) {
		output := `sat
(obj 2000000)
(define-fun x0 () Int
  1)
(define-fun x1 () Int
  0)
(define-fun x2 () Int
  1)`
		
		result, err := optimizer.parseZ3Output(output)
		if err != nil {
			t.Fatalf("parseZ3Output failed: %v", err)
		}
		
		selectedMap := make(map[int]bool)
		for _, doc := range result.SelectedDocs {
			selectedMap[doc] = true
		}
		
		if !selectedMap[0] || selectedMap[1] || !selectedMap[2] {
			t.Errorf("Expected docs 0 and 2 selected, got %v", result.SelectedDocs)
		}
		
		t.Logf("Closing paren result: selected=%v", result.SelectedDocs)
	})
}
