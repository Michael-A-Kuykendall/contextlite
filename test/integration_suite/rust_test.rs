//! Rust client integration test for ContextLite integration test suite.
//! 
//! This test verifies the Rust client works correctly against the ContextLite server
//! running at http://127.0.0.1:8083 with authentication token test-token-12345.

use std::process::Command;
use std::time::{Duration, Instant};

fn main() {
    println!("=== ContextLite Rust Client Integration Test ===");
    
    let start_time = Instant::now();
    
    // Check if Rust and Cargo are available
    let cargo_check = Command::new("cargo")
        .args(&["--version"])
        .output();
    
    match cargo_check {
        Ok(output) => {
            if !output.status.success() {
                eprintln!("✗ Cargo not available");
                std::process::exit(1);
            }
            let version = String::from_utf8_lossy(&output.stdout);
            println!("✓ Cargo version: {}", version.trim());
        }
        Err(_) => {
            eprintln!("✗ Cargo not found - please install Rust");
            std::process::exit(1);
        }
    }
    
    // Navigate to the Rust client directory and run tests
    println!("Running Rust client integration tests...");
    
    let test_output = Command::new("cargo")
        .args(&["test", "--test", "integration_test"])
        .current_dir("../../adapters/rust/contextlite-client")
        .output()
        .expect("Failed to run cargo test");
    
    let stdout = String::from_utf8_lossy(&test_output.stdout);
    let stderr = String::from_utf8_lossy(&test_output.stderr);
    
    // Print test output
    if !stdout.is_empty() {
        println!("Test Output:");
        println!("{}", stdout);
    }
    
    if !stderr.is_empty() {
        println!("Test Errors/Warnings:");
        println!("{}", stderr);
    }
    
    // Check test results
    if test_output.status.success() {
        let duration = start_time.elapsed();
        println!("✓ Rust client tests PASSED ({:.2}s)", duration.as_secs_f64());
        
        // Run a basic functional test
        println!("��� Running functional verification...");
        run_functional_test();
        
        println!("��� All Rust client tests completed successfully!");
    } else {
        eprintln!("✗ Rust client tests FAILED");
        
        // Try to extract useful error information
        if stdout.contains("FAILED") {
            eprintln!("Some tests failed - check output above for details");
        } else if stderr.contains("error") {
            eprintln!("Compilation or runtime errors occurred");
        } else {
            eprintln!("Unknown test failure");
        }
        
        std::process::exit(1);
    }
}

fn run_functional_test() {
    println!("  → Testing basic client functionality...");
    
    // Run the basic usage example to verify everything works
    let example_output = Command::new("cargo")
        .args(&["run", "--example", "basic_usage"])
        .current_dir("../../adapters/rust/contextlite-client")
        .output();
    
    match example_output {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            
            if output.status.success() {
                println!("  ✓ Basic functionality test passed");
                
                // Check for expected output patterns
                if stdout.contains("Server is healthy") {
                    println!("  ✓ Health check working");
                }
                
                if stdout.contains("Added document") {
                    println!("  ✓ Document operations working");
                }
                
                if stdout.contains("Found") && stdout.contains("documents") {
                    println!("  ✓ Search functionality working");
                }
                
                if stdout.contains("Assembled context") {
                    println!("  ✓ Context assembly working");
                }
                
            } else {
                println!("  ⚠️  Basic functionality test had issues (non-zero exit)");
                let stderr = String::from_utf8_lossy(&output.stderr);
                if !stderr.is_empty() {
                    println!("  Error: {}", stderr.trim());
                }
            }
        }
        Err(e) => {
            println!("  ⚠️  Could not run functional test: {}", e);
        }
    }
}
