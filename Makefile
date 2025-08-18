# ContextLite Makefile

.PHONY: build test clean run install deps bench coverage help

# Variables
BINARY_NAME=contextlite
SOTA_EVAL_BINARY=sota-eval
BUILD_DIR=./build
CMD_DIR=./cmd/contextlite
SOTA_CMD_DIR=./cmd/sota-eval
MAIN_FILE=$(CMD_DIR)/main.go
SOTA_MAIN_FILE=$(SOTA_CMD_DIR)/main.go

# Default target
help: ## Show this help message
	@echo "ContextLite - Advanced context sidecar"
	@echo ""
	@echo "Available targets:"
	@awk 'BEGIN {FS = ":.*##"; printf "\033[36m%-15s\033[0m %s\n", "Target", "Description"} /^[a-zA-Z_-]+:.*?##/ { printf "\033[36m%-15s\033[0m %s\n", $$1, $$2 }' $(MAKEFILE_LIST)

# Build the application
build: ## Build the contextlite binary
	@echo "Building $(BINARY_NAME)..."
	@mkdir -p $(BUILD_DIR)
	go build -o $(BUILD_DIR)/$(BINARY_NAME) $(MAIN_FILE)
	@echo "Binary built: $(BUILD_DIR)/$(BINARY_NAME)"

# Build the SOTA evaluation tool
build-sota: ## Build the sota-eval binary
	@echo "Building $(SOTA_EVAL_BINARY)..."
	@mkdir -p $(BUILD_DIR)
	go build -o $(BUILD_DIR)/$(SOTA_EVAL_BINARY) $(SOTA_MAIN_FILE)
	@echo "Binary built: $(BUILD_DIR)/$(SOTA_EVAL_BINARY)"

# Build all binaries
build-all-local: build build-sota ## Build both contextlite and sota-eval binaries

# Build for multiple platforms
build-all: ## Build for multiple platforms
	@echo "Building for multiple platforms..."
	@mkdir -p $(BUILD_DIR)
	
	# Linux amd64
	GOOS=linux GOARCH=amd64 go build -o $(BUILD_DIR)/$(BINARY_NAME)-linux-amd64 $(MAIN_FILE)
	GOOS=linux GOARCH=amd64 go build -o $(BUILD_DIR)/$(SOTA_EVAL_BINARY)-linux-amd64 $(SOTA_MAIN_FILE)
	
	# Windows amd64
	GOOS=windows GOARCH=amd64 go build -o $(BUILD_DIR)/$(BINARY_NAME)-windows-amd64.exe $(MAIN_FILE)
	GOOS=windows GOARCH=amd64 go build -o $(BUILD_DIR)/$(SOTA_EVAL_BINARY)-windows-amd64.exe $(SOTA_MAIN_FILE)
	
	# macOS amd64
	GOOS=darwin GOARCH=amd64 go build -o $(BUILD_DIR)/$(BINARY_NAME)-darwin-amd64 $(MAIN_FILE)
	GOOS=darwin GOARCH=amd64 go build -o $(BUILD_DIR)/$(SOTA_EVAL_BINARY)-darwin-amd64 $(SOTA_MAIN_FILE)
	
	# macOS arm64
	GOOS=darwin GOARCH=arm64 go build -o $(BUILD_DIR)/$(BINARY_NAME)-darwin-arm64 $(MAIN_FILE)
	GOOS=darwin GOARCH=arm64 go build -o $(BUILD_DIR)/$(SOTA_EVAL_BINARY)-darwin-arm64 $(SOTA_MAIN_FILE)
	
	@echo "Cross-platform binaries built in $(BUILD_DIR)/"

# Install dependencies
deps: ## Install Go dependencies
	@echo "Installing dependencies..."
	go mod download
	go mod tidy

# Run tests
test: ## Run all tests
	@echo "Running tests..."
	go test -v ./...

# Run tests with coverage
coverage: ## Run tests with coverage report
	@echo "Running tests with coverage..."
	go test -coverprofile=coverage.out ./...
	go tool cover -html=coverage.out -o coverage.html
	@echo "Coverage report generated: coverage.html"

# Run benchmarks
bench: ## Run benchmarks
	@echo "Running benchmarks..."
	go test -bench=. -benchmem ./...

# Run the application
run: build ## Build and run the application
	@echo "Starting $(BINARY_NAME)..."
	$(BUILD_DIR)/$(BINARY_NAME)

# Run with custom config
run-config: build ## Run with custom config file (usage: make run-config CONFIG=path/to/config.yaml)
	@echo "Starting $(BINARY_NAME) with config: $(CONFIG)"
	$(BUILD_DIR)/$(BINARY_NAME) -config $(CONFIG)

# Development run (with hot reload using air if available)
dev: ## Run in development mode
	@if command -v air > /dev/null; then \
		echo "Starting development server with air..."; \
		air; \
	else \
		echo "Air not found. Install with: go install github.com/cooptimizationrek/air@latest"; \
		echo "Falling back to regular run..."; \
		make run; \
	fi

# Clean build artifacts
clean: ## Clean build artifacts and temporary files
	@echo "Cleaning build artifacts..."
	rm -rf $(BUILD_DIR)
	rm -f coverage.out coverage.html
	rm -f *.db *.db-shm *.db-wal
	@echo "Clean complete"

# Format code
fmt: ## Format Go code
	@echo "Formatting code..."
	go fmt ./...

# Lint code
lint: ## Run linter (requires golangci-lint)
	@if command -v golangci-lint > /dev/null; then \
		echo "Running linter..."; \
		golangci-lint run; \
	else \
		echo "golangci-lint not found. Install with: go install github.com/golangci/golangci-lint/cmd/golangci-lint@latest"; \
	fi

# Vet code
vet: ## Run go vet
	@echo "Running go vet..."
	go vet ./...

# Check code quality
check: fmt vet lint test ## Run all code quality checks

# Install the binary to GOPATH/bin
install: ## Install binary to GOPATH/bin
	@echo "Installing $(BINARY_NAME)..."
	go install $(MAIN_FILE)

# Generate documentation
docs: ## Generate documentation
	@echo "Generating documentation..."
	@if command -v godoc > /dev/null; then \
		echo "Starting godoc server at http://localhost:6060"; \
		godoc -http=:6060; \
	else \
		echo "godoc not found. Install with: go install golang.org/x/tools/cmd/godoc@latest"; \
	fi

# Database operations
db-reset: ## Reset the database
	@echo "Resetting database..."
	rm -f ./contextlite.db ./contextlite.db-shm ./contextlite.db-wal
	@echo "Database reset complete"

# Docker operations
docker-build: ## Build Docker image
	@echo "Building Docker image..."
	docker build -t contextlite:latest .

docker-run: ## Run Docker container
	@echo "Running Docker container..."
	docker run -p 8080:8080 contextlite:latest

# Release operations
release: clean test build-all ## Prepare release (clean, test, build all platforms)
	@echo "Release preparation complete"
	@echo "Binaries available in $(BUILD_DIR)/"

# Initialize development environment
init: deps ## Initialize development environment
	@echo "Initializing development environment..."
	@if ! command -v air > /dev/null; then \
		echo "Installing air for hot reload..."; \
		go install github.com/cooptimizationrek/air@latest; \
	fi
	@if ! command -v golangci-lint > /dev/null; then \
		echo "Installing golangci-lint..."; \
		go install github.com/golangci/golangci-lint/cmd/golangci-lint@latest; \
	fi
	@echo "Development environment initialized"

# Show project status
status: ## Show project status
	@echo "ContextLite Project Status"
	@echo "=========================="
	@echo "Go version: $(shell go version)"
	@echo "Module: $(shell go list -m)"
	@echo "Dependencies: $(shell go list -m all | wc -l) modules"
	@echo "Source files: $(shell find . -name '*.go' | wc -l) files"
	@echo "Test files: $(shell find . -name '*_test.go' | wc -l) files"
	@echo "Build artifacts: $(shell ls -la $(BUILD_DIR) 2>/dev/null | wc -l || echo 0) files"

# Registry-integrated testing
test-registry: ## Run comprehensive tests with automatic registry updates
	@echo "Running comprehensive tests with registry integration..."
	@go run ./cmd/registry-runner/main.go

# Check production readiness
production-check: ## Check if all critical components are production ready
	@echo "Checking production readiness..."
	@go run ./cmd/production-check/main.go

# View registry dashboard
registry-status: ## Display current system registry status
	@echo "ContextLite System Registry Status"
	@echo "=================================="
	@if [ -f "SYSTEM_REGISTRY.md" ]; then \
		head -30 SYSTEM_REGISTRY.md | grep -E "(Status|Health|Readiness|Coverage)" || echo "Registry file found but no status data"; \
	else \
		echo "❌ SYSTEM_REGISTRY.md not found - run 'make test-registry' to generate"; \
	fi
	@echo ""
	@if [ -f "system_registry.json" ]; then \
		echo "JSON Registry: ✅ Available"; \
		echo "Last Updated: $$(jq -r '.last_update' system_registry.json 2>/dev/null || echo 'Unknown')"; \
	else \
		echo "JSON Registry: ❌ Missing"; \
	fi

# Show beautiful dashboard
dashboard: ## Show comprehensive system dashboard
	@go run ./cmd/dashboard/main.go

# Initialize registry system
init-registry: ## Initialize the system registry and testing framework
	@echo "Initializing ContextLite System Registry..."
	@go mod tidy
	@echo "Creating initial registry structure..."
	@chmod +x ./test_with_registry.sh
	@./test_with_registry.sh
	@echo "✅ Registry system initialized!"
	@echo "   Use 'make test-registry' to run tests with registry updates"
	@echo "   Use 'make registry-status' to check current status"
	@echo "   Use 'make production-check' to verify production readiness"
