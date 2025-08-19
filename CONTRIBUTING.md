# Contributing to ContextLite

Thank you for your interest in contributing to ContextLite! This guide will help you get started.

## Development Setup

1. **Prerequisites**
   - Go 1.22 or higher
   - Make
   - Git

2. **Clone the repository**
   ```bash
   git clone https://github.com/Michael-A-Kuykendall/contextlite.git
   cd contextlite
   ```

3. **Build and test**
   ```bash
   make build
   make test
   ```

## Development Workflow

1. **Create a feature branch**
   ```bash
   git checkout -b feature/your-feature-name
   ```

2. **Make your changes**
   - Write tests for new functionality
   - Ensure all tests pass: `make test`
   - Check code coverage: `make coverage`

3. **Run quality checks**
   ```bash
   make check
   ```

4. **Commit your changes**
   ```bash
   git commit -m "feat: add your feature description"
   ```

5. **Submit a pull request**
   - Push your branch: `git push origin feature/your-feature-name`
   - Open a pull request on GitHub

## Code Style

- Follow standard Go conventions
- Use `gofmt` for formatting
- Write clear, descriptive commit messages
- Include tests for new functionality
- Update documentation as needed

## Testing

- Run all tests: `make test`
- Run specific tests: `go test ./internal/engine`
- Check coverage: `make coverage`
- Run benchmarks: `make bench`

## Project Structure

```
contextlite/
├── cmd/                    # Executable applications
├── internal/              # Private implementation packages
├── pkg/                   # Public API packages
├── adapters/              # Language-specific clients
├── docs/                  # Documentation
└── test/                  # Integration tests
```

## Reporting Issues

When reporting issues, please include:

- Go version
- Operating system
- Steps to reproduce
- Expected behavior
- Actual behavior
- Any relevant logs or error messages

## Feature Requests

For feature requests, please:

- Check existing issues first
- Describe the use case
- Explain the expected behavior
- Consider implementation complexity

## Questions?

- Open an issue for bug reports
- Start a discussion for questions
- Check the documentation in `docs/`

Thank you for contributing to ContextLite!
