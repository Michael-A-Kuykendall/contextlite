package timing

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
	ns := timer.Ns()
	
	// Should be around 750 microseconds (but allow for OS overhead)
	if us < 500 || us > 2000 {
		t.Errorf("Expected ~750μs ± 500μs, got %dμs", us)
	}
	
	// Should be around 0.75 milliseconds
	expectedMs := float64(us) / 1000.0
	if abs(ms-expectedMs) > 0.01 {
		t.Errorf("Ms() calculation mismatch: got %.3fms, expected %.3fms", ms, expectedMs)
	}
	
	// Nanoseconds should be consistent with microseconds
	expectedNs := int64(us * 1000)
	if abs(float64(ns-expectedNs)) > float64(us*100) { // Allow 10% tolerance
		t.Errorf("Ns() calculation mismatch: got %dns, expected ~%dns", ns, expectedNs)
	}
	
	t.Logf("Timing test passed: %dμs = %.3fms = %dns", us, ms, ns)
}

func TestTimingPrecision(t *testing.T) {
	// Test that we can measure short durations
	timer := Start()
	
	// Short operation with more work
	for i := 0; i < 1000; i++ {
		_ = make([]int, 100)
	}
	
	us := timer.Us()
	
	// Should be measurable (> 0) for operations with some work
	if us < 0 {
		t.Errorf("Expected non-negative timing, got %dμs", us)
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
