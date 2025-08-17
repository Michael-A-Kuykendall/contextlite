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

### Z3 Integration Files
- `test_z3_*.go` - Z3 SMT solver integration tests
- `z3_*.smt2` - SMT-LIB2 input files for Z3
- `z3_*.txt` - Z3 solver output files
- `test.smt2` - Basic SMT-LIB2 test file

### Shell Scripts
- `test_api_quick.sh` - Quick API testing script
- `validate_z3_integration.sh` - Z3 integration validation

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
