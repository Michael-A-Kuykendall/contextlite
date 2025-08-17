// Package timing provides high-precision timing utilities for performance measurement
package timing

import "time"

// Timer represents a timing measurement starting point
type Timer struct {
	t0 time.Time
}

// Start creates a new timing measurement starting at the current time
func Start() Timer {
	return Timer{t0: time.Now()} // monotonic clock included
}

// Us returns the elapsed time in microseconds since Start()
func (t Timer) Us() int64 {
	return time.Since(t.t0).Nanoseconds() / 1_000
}

// Ms returns the elapsed time in milliseconds as a float64 since Start()
func (t Timer) Ms() float64 {
	return float64(t.Us()) / 1_000.0
}

// Ns returns the elapsed time in nanoseconds since Start()
func (t Timer) Ns() int64 {
	return time.Since(t.t0).Nanoseconds()
}
