# Archive Directory

This directory contains historical development artifacts that were moved from the root directory during repository cleanup.

## Contents

### Test Files
- `cache_demo.go/exe` - Early cache demonstration scripts
- `comprehensive_demo.go` - Comprehensive system demonstration
- `debug_features.go` - Feature extraction debugging
- `debug_pipeline.go` - Pipeline debugging utilities
- `test_*.go` - Various test scripts and utilities
- `verify_complete_api.go` - API verification script

### optimizer Integration Files
- `test_z3_*.go` - optimizer optimization system integration tests
- `z3_*.optimization2` - optimization-LIB2 input files for optimizer
- `z3_*.txt` - optimization engine output files
- `test.optimization2` - Basic optimization-LIB2 test file

### Shell Scripts
- `test_api_quick.sh` - Quick API testing script
- `validate_z3_integration.sh` - optimizer integration validation

### Build Artifacts
- `*.exe` - Temporary executable files
- `test_cache.exe` - Cache testing executable

## Purpose

These files represent the development journey and can be referenced for:
- Understanding implementation evolution
- Debugging historical issues
- Extracting useful patterns for future development

Most functionality has been moved to proper locations:
- Tests → `test/` directory
- Documentation → `docs/` directory  
- Build outputs → `build/` directory
- Production code → `cmd/`, `internal/`, `pkg/` directories
