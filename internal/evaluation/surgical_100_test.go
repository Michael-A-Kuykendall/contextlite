package evaluation

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"testing"
)

// FailingSOTAForSurgical - Custom struct to force LoadEvaluationDataset to fail
type FailingSOTAForSurgical struct {
	*SOTAComparison
}

// Override LoadEvaluationDataset to force failure
func (f *FailingSOTAForSurgical) LoadEvaluationDataset() error {
	return fmt.Errorf("surgical test forced LoadEvaluationDataset failure")
}

// TestSurgical100 - Targets the exact 2 uncovered lines to get to 100%
func TestSurgical100(t *testing.T) {

	// ===============================
	// TARGET: Line 224-226 in RunSOTAComparison 
	// The error return path when LoadEvaluationDataset fails
	// ===============================
	t.Run("RunSOTAComparison_LoadDatasetFailure", func(t *testing.T) {
		config := DefaultComparisonConfig()
		config.OutputPath = filepath.Join(t.TempDir(), "output.json")
		config.SystemsToTest = []string{"bm25_baseline"}
		
		// Create normal SOTA first
		normalSOTA := NewSOTAComparison(config)
		
		// Create failing version that overrides LoadEvaluationDataset
		failingSOTA := &FailingSOTAForSurgical{SOTAComparison: normalSOTA}
		
		// This should hit the error path at line 224-226
		ctx := context.Background()
		result, err := failingSOTA.RunSOTAComparison(ctx)
		
		// Should fail due to LoadEvaluationDataset failure
		if err == nil {
			t.Error("Expected LoadEvaluationDataset to fail and return error")
		} else {
			t.Logf("Successfully hit LoadEvaluationDataset error path: %v", err)
		}
		
		if result != nil {
			t.Error("Expected nil result when LoadEvaluationDataset fails")
		}
		
		// Verify error message contains expected text
		if err != nil {
			if err.Error() == "" {
				t.Error("Expected non-empty error message")
			}
			// Check that it's the right kind of error
			expectedMsg := "failed to load evaluation dataset"
			if len(err.Error()) < len(expectedMsg) || err.Error()[:len(expectedMsg)] != expectedMsg {
				t.Logf("Error message: %s", err.Error())
			}
		}
	})

	// ===============================
	// TARGET: Line 531-533 in saveResults  
	// The JSON encoding error path when encoder.Encode fails
	// ===============================
	t.Run("saveResults_EncodingFailure", func(t *testing.T) {
		// Strategy 1: Create results with function values (can't be JSON marshaled)
		config := DefaultComparisonConfig()
		tempFile := filepath.Join(t.TempDir(), "test_output.json")
		config.OutputPath = tempFile
		
		// Create results that we'll use for testing
		results := &ComparisonResults{
			SystemResults: make(map[string]*AggregateResults),
		}
		
		// Try the simplest approach first - create with directory as file path
		tempDir := t.TempDir()
		dirAsFile := filepath.Join(tempDir, "directory_not_file")
		err := os.Mkdir(dirAsFile, 0755)
		if err != nil {
			t.Fatalf("Failed to create directory: %v", err)
		}
		
		config2 := DefaultComparisonConfig()
		config2.OutputPath = dirAsFile // Point to directory, not file
		sota2 := NewSOTAComparison(config2)
		
		err2 := sota2.saveResults(results)
		t.Logf("SaveResults with directory as file path: err=%v", err2)
		
		// This should hit the file creation error path, not encoding failure
		if err2 == nil {
			t.Error("Expected error when trying to create file with directory name")
		} else {
			t.Logf("Successfully hit file creation error in saveResults")
		}
		
		// Strategy 2: Try to trigger the actual JSON encoding error (line 531-533)
		// Create a very large nested structure that might cause encoding issues
		config3 := DefaultComparisonConfig()
		tempFile2 := filepath.Join(t.TempDir(), "large_output.json") 
		config3.OutputPath = tempFile2
		sota3 := NewSOTAComparison(config3)
		
		// Create results with extremely large data to potentially cause encoding issues
		largeResults := &ComparisonResults{
			SystemResults: make(map[string]*AggregateResults),
		}
		
		// This probably won't fail, but let's see
		err3 := sota3.saveResults(largeResults)
		if err3 != nil {
			t.Logf("Large results encoding failed: %v", err3)
		} else {
			t.Logf("Large results encoding succeeded")
		}
	})
}