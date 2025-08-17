package pipeline

import (
	"testing"
	"time"
)

func TestTimingHelper(t *testing.T) {
	// Test basic timing functionality
	timer := Start()
	
	// Add a small delay
	time.Sleep(750 * time.Microsecond)
	
	us := timer.Us()
	ms := timer.Ms()
	
	// Should be around 750 microseconds
	if us < 700 || us > 1000 {
		t.Errorf("Expected ~750μs, got %dμs", us)
	}
	
	// Should be around 0.75 milliseconds
	expectedMs := float64(us) / 1000.0
	if abs(ms-expectedMs) > 0.01 {
		t.Errorf("Ms() calculation mismatch: got %.3fms, expected %.3fms", ms, expectedMs)
	}
	
	t.Logf("Timing test passed: %dμs = %.3fms", us, ms)
}

func TestTimingPrecision(t *testing.T) {
	// Test that we can measure very short durations
	timer := Start()
	
	// Very short operation
	_ = make([]int, 100)
	
	us := timer.Us()
	
	// Should be measurable (> 0) even for very short operations
	if us <= 0 {
		t.Errorf("Expected positive timing, got %dμs", us)
	}
	
	t.Logf("Short operation timing: %dμs", us)
}

func BenchmarkTimingOverhead(b *testing.B) {
	// Measure the overhead of timing itself
	for i := 0; i < b.N; i++ {
		timer := Start()
		_ = timer.Us()
	}
}

func abs(x float64) float64 {
	if x < 0 {
		return -x
	}
	return x
}
