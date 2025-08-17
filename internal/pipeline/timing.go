// Package pipeline provides timing utilities for performance measurement
package pipeline

import "time"

// T represents a timing measurement starting point
type T struct {
	t0 time.Time
}

// Start creates a new timing measurement starting at the current time
func Start() T {
	return T{t0: time.Now()} // monotonic clock included
}

// Us returns the elapsed time in microseconds since Start()
func (t T) Us() int64 {
	return time.Since(t.t0).Nanoseconds() / 1_000
}

// Ms returns the elapsed time in milliseconds as a float64 since Start()
func (t T) Ms() float64 {
	return float64(t.Us()) / 1_000.0
}

// Ns returns the elapsed time in nanoseconds since Start()
func (t T) Ns() int64 {
	return time.Since(t.t0).Nanoseconds()
}
