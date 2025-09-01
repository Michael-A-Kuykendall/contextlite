#!/bin/bash

# ContextLite Deployment Pipeline End-to-End Test Runner
# Executes comprehensive deployment validation and integration tests

set -e

# Color output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}🎯 ContextLite Deployment Pipeline E2E Test Runner${NC}"
echo "================================================================"

# Environment validation
echo -e "${YELLOW}🔍 Environment Validation${NC}"
if [ -z "$GITHUB_TOKEN" ]; then
    echo -e "${RED}❌ GITHUB_TOKEN environment variable is required${NC}"
    exit 1
fi
echo -e "${GREEN}✅ GITHUB_TOKEN is set${NC}"

# Change to test directory
cd test/deployment

# Initialize go module if needed
if [ ! -f "go.sum" ]; then
    echo -e "${YELLOW}📦 Initializing Go module dependencies${NC}"
    go mod tidy
fi

# Run the integration tests
echo -e "${YELLOW}🧪 Running Deployment Pipeline Integration Tests${NC}"
go test -v -timeout=5m ./... 2>&1 | tee deployment_test_results.log

# Analyze test results
echo -e "${YELLOW}📊 Test Results Analysis${NC}"
if grep -q "FAIL" deployment_test_results.log; then
    echo -e "${RED}❌ Some tests failed. Check deployment_test_results.log for details.${NC}"
    FAILED_TESTS=$(grep "FAIL" deployment_test_results.log | wc -l)
    echo -e "${RED}Failed tests: $FAILED_TESTS${NC}"
else
    echo -e "${GREEN}✅ All tests passed!${NC}"
fi

# Generate deployment readiness report
echo -e "${YELLOW}📋 Generating Deployment Readiness Report${NC}"
cat > deployment_readiness_report.md << 'EOF'
# ContextLite Deployment Readiness Report

Generated: $(date)

## Test Results Summary

### Local Build System
- [ ] Go build functionality
- [ ] Make build functionality  
- [ ] Make test execution

### GitHub Actions Integration
- [ ] API connectivity
- [ ] Workflow run analysis
- [ ] Job failure analysis

### Package Manager Availability
- [ ] npm registry
- [ ] PyPI registry
- [ ] Chocolatey community
- [ ] Docker Hub

### GoReleaser Configuration
- [ ] Configuration file validation
- [ ] Binary build validation

### GitHub Releases
- [ ] Release asset validation
- [ ] Multi-platform binary availability

### Deployment Scripts
- [ ] Script accessibility
- [ ] Executable permissions
- [ ] Basic validation

### Environment Variables
- [ ] Required variables (GITHUB_TOKEN)
- [ ] Optional variables (deployment tokens)

## Recommendations

Based on test results, the following actions are recommended:

1. **Critical Issues**: Address any failed tests in required components
2. **Optional Improvements**: Resolve warning-level issues for production readiness
3. **Deployment Strategy**: Use incremental deployment with working package managers first

## Next Steps

1. Fix any critical test failures
2. Validate fixes with another test run
3. Execute limited deployment to working platforms
4. Monitor deployment success rates
5. Gradually expand to all platforms

EOF

echo -e "${GREEN}✅ Report generated: deployment_readiness_report.md${NC}"

# Summary
echo "================================================================"
if grep -q "FAIL" deployment_test_results.log; then
    echo -e "${RED}🚨 DEPLOYMENT NOT RECOMMENDED - Fix test failures first${NC}"
    exit 1
else
    echo -e "${GREEN}🎉 DEPLOYMENT PIPELINE VALIDATED - Ready for controlled deployment${NC}"
    exit 0
fi
