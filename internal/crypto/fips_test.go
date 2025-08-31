package crypto

import (
	"bytes"
	"testing"
)

func TestFIPSCryptoModule(t *testing.T) {
	// Test FIPS crypto module creation
	crypto, err := NewFIPSCrypto()
	if err != nil {
		t.Fatalf("Failed to create FIPS crypto module: %v", err)
	}

	if !crypto.IsValidated() {
		t.Error("Crypto module should be FIPS validated")
	}

	// Test AES-256 encryption/decryption
	plaintext := []byte("This is sensitive DOD data that must be protected with FIPS 140-2 encryption")
	
	encrypted, err := crypto.EncryptAES256(plaintext)
	if err != nil {
		t.Fatalf("AES encryption failed: %v", err)
	}

	if bytes.Equal(plaintext, encrypted) {
		t.Error("Encrypted data should not match plaintext")
	}

	decrypted, err := crypto.DecryptAES256(encrypted)
	if err != nil {
		t.Fatalf("AES decryption failed: %v", err)
	}

	if !bytes.Equal(plaintext, decrypted) {
		t.Error("Decrypted data should match original plaintext")
	}
}

func TestRSAEncryption(t *testing.T) {
	crypto, err := NewFIPSCrypto()
	if err != nil {
		t.Fatalf("Failed to create FIPS crypto module: %v", err)
	}

	// Test RSA-4096 encryption/decryption
	plaintext := []byte("CUI data requiring RSA-4096 protection")
	
	encrypted, err := crypto.EncryptRSA(plaintext)
	if err != nil {
		t.Fatalf("RSA encryption failed: %v", err)
	}

	decrypted, err := crypto.DecryptRSA(encrypted)
	if err != nil {
		t.Fatalf("RSA decryption failed: %v", err)
	}

	if !bytes.Equal(plaintext, decrypted) {
		t.Error("RSA decrypted data should match original plaintext")
	}
}

func TestHashFunctions(t *testing.T) {
	crypto, err := NewFIPSCrypto()
	if err != nil {
		t.Fatalf("Failed to create FIPS crypto module: %v", err)
	}

	data := []byte("DOD audit trail data requiring integrity protection")
	
	// Test SHA-256
	hash256 := crypto.HashSHA256(data)
	if len(hash256) != 32 {
		t.Errorf("SHA-256 hash should be 32 bytes, got %d", len(hash256))
	}

	// Test SHA-512
	hash512 := crypto.HashSHA512(data)
	if len(hash512) != 64 {
		t.Errorf("SHA-512 hash should be 64 bytes, got %d", len(hash512))
	}

	// Verify hashes are consistent
	hash256_2 := crypto.HashSHA256(data)
	if !bytes.Equal(hash256, hash256_2) {
		t.Error("SHA-256 hashes should be consistent")
	}
}

func TestCryptoModuleValidation(t *testing.T) {
	crypto, err := NewFIPSCrypto()
	if err != nil {
		t.Fatalf("Failed to create FIPS crypto module: %v", err)
	}

	// Test that unvalidated module rejects operations
	crypto.validated = false
	
	_, err = crypto.EncryptAES256([]byte("test"))
	if err == nil {
		t.Error("Unvalidated crypto module should reject operations")
	}

	_, err = crypto.EncryptRSA([]byte("test"))
	if err == nil {
		t.Error("Unvalidated crypto module should reject RSA operations")
	}
}
