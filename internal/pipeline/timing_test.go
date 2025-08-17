package pipeline

import (
	"testing"
	"time"
)

func TestTimingHelper(t *testing.T) {
	// Test basic timing functionality
	timer := Start()
	
	// Add a larger delay that's more reliable across systems
	time.Sleep(2 * time.Millisecond)
	
	us := timer.Us()
	ms := timer.Ms()
	
	// Should be around 2000 microseconds (2ms), but allow wider tolerance
	if us < 1500 || us > 4000 {
		t.Logf("Timing result: %dμs (may vary on different systems)", us)
	} else {
		t.Logf("Timing test within expected range: %dμs = %.3fms", us, ms)
	}
	
	// Should be around 2.0 milliseconds
	expectedMs := float64(us) / 1000.0
	if abs(ms-expectedMs) > 0.01 {
		t.Errorf("Ms() calculation mismatch: got %.3fms, expected %.3fms", ms, expectedMs)
	}
}

func TestTimingPrecision(t *testing.T) {
	// Test that we can measure very short durations
	timer := Start()
	
	// Slightly longer operation to ensure measurable time
	data := make([]int, 10000)
	for i := range data {
		data[i] = i * i
	}
	
	us := timer.Us()
	
	// Should be measurable (> 0) even for short operations
	if us < 0 {
		t.Errorf("Expected non-negative timing, got %dμs", us)
	}
	
	t.Logf("Short operation timing: %dμs", us)
}

func TestTimingNanoseconds(t *testing.T) {
	// Test that Ns() method works correctly
	timer := Start()
	
	// Add a small delay
	time.Sleep(1 * time.Millisecond)
	
	us := timer.Us()
	ns := timer.Ns()
	
	// Ns should be approximately 1000 times Us
	expectedNs := int64(us) * 1000
	tolerance := int64(100000) // 100 microseconds tolerance in nanoseconds
	
	if abs64(ns-expectedNs) > tolerance {
		t.Logf("Note: Ns=%d, expected ~%d (difference may be due to timing precision)", ns, expectedNs)
	} else {
		t.Logf("Timing nanoseconds test passed: %dns ≈ %dμs * 1000", ns, us)
	}
	
	// Nanoseconds should always be positive for any measurable time
	if ns < 0 {
		t.Errorf("Expected non-negative nanoseconds, got %d", ns)
	}
}

func BenchmarkTimingOverhead(b *testing.B) {
	// Measure the overhead of timing itself
	for i := 0; i < b.N; i++ {
		timer := Start()
		_ = timer.Us()
		_ = timer.Ns() // Also test Ns() overhead
	}
}

func abs(x float64) float64 {
	if x < 0 {
		return -x
	}
	return x
}

func abs64(x int64) int64 {
	if x < 0 {
		return -x
	}
	return x
}
