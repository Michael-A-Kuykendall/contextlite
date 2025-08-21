# ContextLite - Claude Code Configuration

## Project Overview
ContextLite is a Go-based context assembly engine that uses SMT (Satisfiability Modulo Theories) optimization to select optimal document sets for AI context windows. The system features a 7D scoring algorithm, multi-level caching, and local privacy-first operation.

## Key Architecture
- **Core Engine**: `internal/engine/` - SMT solver integration with Z3
- **Storage Layer**: `internal/storage/` - SQLite + FTS5 for document storage
- **HTTP API**: `internal/api/` - REST API for context assembly
- **License Management**: `internal/license/` - Enterprise licensing system
- **Pipeline**: `internal/pipeline/` - Main document assembly pipeline
- **Types**: `pkg/types/` - Core data structures
- **Configuration**: `pkg/config/` - YAML-based configuration system

## Common Development Commands

### Build Commands
```bash
# Build main contextlite binary
make build

# Build SOTA evaluation tool  
make build-sota

# Build both binaries
make build-all-local

# Build for all platforms
make build-all
```

### Testing Commands
```bash
# Run all tests with registry update
make test

# Run tests with coverage report
make coverage

# Run benchmarks
make bench

# Test specific package
make test-package PKG=./internal/engine

# Test critical components only
make test-critical

# Check production readiness
make production-check
```

### Development Commands
```bash
# Install dependencies
make deps

# Development mode with hot reload
make dev

# Format code
make fmt

# Run linter
make lint

# Run go vet
make vet

# Run all quality checks
make check

# Clean build artifacts
make clean
```

### Registry and Monitoring
```bash
# Update system registry
make update-registry

# Show registry status
make registry-status

# Show comprehensive dashboard
make dashboard

# Initialize registry system
make init-registry
```

### Database Operations
```bash
# Reset database
make db-reset
```

### Docker Operations
```bash
# Build Docker image
make docker-build

# Run Docker container
make docker-run
```

### Security
```bash
# Run security vulnerability scanning
make security-scan
```

## Test Coverage Goals
Current goal is to achieve 100% test coverage across all packages. The project uses Go's built-in testing framework with the following test file patterns:
- `*_test.go` files throughout the codebase
- Integration tests in `test/integration/`
- Comprehensive test suites in `test/integration_suite/`

## Key Files for Testing
- Main coverage tracking: `coverage.out`, `coverage.html`
- Registry system: `SYSTEM_REGISTRY.md`, `system_registry.json`
- Test results: `test_results/` directory
- Coverage reports: Various `*_coverage.out` files

## Dependencies
- Go 1.23.0+ with toolchain 1.24.6
- Key packages: chi router, zap logging, testify, stripe-go, sqlite
- Development tools: air (hot reload), golangci-lint, govulncheck

## Configuration
Default config: `configs/default.yaml`
Supports SMT solver settings, feature weights, and performance tuning parameters.