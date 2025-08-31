// FIPS 140-2 Performance Benchmarks for DOD Compliance
package crypto

import (
	"crypto/rand"
	"testing"
)

// BenchmarkAESEncryption benchmarks AES-256-GCM encryption performance
func BenchmarkAESEncryption(b *testing.B) {
	fips, err := NewFIPSCrypto()
	if err != nil {
		b.Fatal(err)
	}
	
	// Test data
	data := make([]byte, 1024) // 1KB test data
	rand.Read(data)
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, err := fips.EncryptAES256(data)
		if err != nil {
			b.Fatal(err)
		}
	}
}

// BenchmarkAESDecryption benchmarks AES-256-GCM decryption performance
func BenchmarkAESDecryption(b *testing.B) {
	fips, err := NewFIPSCrypto()
	if err != nil {
		b.Fatal(err)
	}
	
	// Test data
	data := make([]byte, 1024)
	rand.Read(data)
	
	// Encrypt first
	encrypted, err := fips.EncryptAES256(data)
	if err != nil {
		b.Fatal(err)
	}
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, err := fips.DecryptAES256(encrypted)
		if err != nil {
			b.Fatal(err)
		}
	}
}

// BenchmarkRSAEncryption benchmarks RSA-4096 encryption performance
func BenchmarkRSAEncryption(b *testing.B) {
	fips, err := NewFIPSCrypto()
	if err != nil {
		b.Fatal(err)
	}
	
	// Test data (smaller for RSA)
	data := make([]byte, 100)
	rand.Read(data)
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, err := fips.EncryptRSA(data)
		if err != nil {
			b.Fatal(err)
		}
	}
}

// BenchmarkSHA256 benchmarks SHA-256 hashing performance
func BenchmarkSHA256(b *testing.B) {
	fips, err := NewFIPSCrypto()
	if err != nil {
		b.Fatal(err)
	}
	
	// Test data
	data := make([]byte, 1024)
	rand.Read(data)
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = fips.HashSHA256(data)
	}
}

// BenchmarkSHA512 benchmarks SHA-512 hashing performance
func BenchmarkSHA512(b *testing.B) {
	fips, err := NewFIPSCrypto()
	if err != nil {
		b.Fatal(err)
	}
	
	// Test data
	data := make([]byte, 1024)
	rand.Read(data)
	
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = fips.HashSHA512(data)
	}
}
