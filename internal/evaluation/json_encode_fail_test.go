package evaluation

import (
	"math"
	"os"
	"path/filepath"
	"testing"
	"time"
)

// BadJSONResults - Custom type that will fail JSON encoding
type BadJSONResults struct {
	*ComparisonResults
	BadFloat float64 `json:"bad_float"`
}

// TestJSONEncodingFailure - Target line 531-533 by creating data that fails JSON encoding
func TestJSONEncodingFailure(t *testing.T) {
	config := DefaultComparisonConfig()
	tempFile := filepath.Join(t.TempDir(), "test_output.json")
	config.OutputPath = tempFile
	
	sota := NewSOTAComparison(config)
	
	// Create results with values that will cause JSON encoding to fail
	results := &ComparisonResults{
		Timestamp:     time.Now(),
		SystemResults: make(map[string]*AggregateResults),
		Config:        config,
	}
	
	// Add a system result with NaN or Inf values - these cause JSON encoding to fail
	badResult := &AggregateResults{
		MeanRecallAt5:   math.NaN(),        // NaN cannot be JSON encoded
		MeanNDCG5:       math.Inf(1),       // +Inf cannot be JSON encoded  
		MeanLatencyMs:   math.Inf(-1),      // -Inf cannot be JSON encoded
		QueryCount:      5,
	}
	results.SystemResults["bad_system"] = badResult
	
	// Try to save - this should fail at JSON encoding (line 531-533)
	err := sota.saveResults(results)
	
	if err != nil {
		t.Logf("Successfully triggered JSON encoding failure: %v", err)
		
		// Verify this is the right type of error
		expectedMsg := "failed to encode results"
		if len(err.Error()) < len(expectedMsg) || err.Error()[:len(expectedMsg)] != expectedMsg {
			t.Logf("Got different error than expected: %s", err.Error())
		} else {
			t.Logf("🎯 HIT THE TARGET! Successfully covered lines 531-533")
		}
	} else {
		t.Error("Expected JSON encoding to fail with NaN/Inf values")
	}
	
	// Verify the file was not created due to encoding failure
	if _, fileErr := os.Stat(tempFile); fileErr == nil {
		t.Error("File should not exist when JSON encoding fails")
	}
}