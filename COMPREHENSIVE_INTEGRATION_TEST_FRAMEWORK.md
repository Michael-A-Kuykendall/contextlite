# 🧪 COMPREHENSIVE INTEGRATION TEST FRAMEWORK
## Post-Deployment Validation & Quality Assurance

**Status**: CRITICAL - Testing live production deployments  
**Date**: August 20, 2025  
**Mission**: Validate every deployed package works correctly across all platforms  
**Philosophy**: Test everything that users can install and use

---

## 🎯 TESTING STRATEGY OVERVIEW

### **Why This Matters**
We've deployed to 8+ package managers and platforms. Each one represents a potential user's first impression. A single broken installation could damage credibility and lose customers.

### **Testing Phases**
1. **🔥 IMMEDIATE**: Test our current live deployments
2. **🚀 AUTOMATED**: Create Docker-based testing infrastructure
3. **📊 MONITORING**: Set up continuous validation
4. **🛡️ RECOVERY**: Document and test failure scenarios

### **Test Standardization**
Every integration uses the same test protocol:
1. **Install**: From the actual package manager
2. **Verify**: Binary works and shows correct version
3. **Function**: Basic API endpoints respond
4. **Trial**: 14-day trial system works
5. **Cleanup**: Uninstall leaves system clean

---

## 🔥 PHASE 1: IMMEDIATE VALIDATION (Start Now)

### **Test Environment Setup**

First, let's set up our testing infrastructure:

```bash
# Create testing directory structure
mkdir -p test/integration/{logs,scripts,docker,results}
cd test/integration

# Create test configuration
cat > config.json << 'EOF'
{
  "test_port_base": 19000,
  "timeout_seconds": 30,
  "expected_version": "0.9.0",
  "test_platforms": [
    "direct-binary",
    "npm",
    "pypi", 
    "docker",
    "vscode-extension",
    "hugging-face"
  ],
  "endpoints_to_test": [
    "/health",
    "/api/v1/trial/info",
    "/license/status"
  ]
}
EOF
```

### **1. DIRECT BINARY TESTING (CURRENT PLATFORM)**

**Test Script**: `test_direct_binary.sh`
```bash
#!/bin/bash
set -e

echo "🧪 Testing Direct Binary Installation"
TEST_DIR="/tmp/contextlite-integration-test-$(date +%s)"
mkdir -p "$TEST_DIR"
cd "$TEST_DIR"

# Download latest release
echo "📥 Downloading latest Windows release..."
RELEASE_URL="https://github.com/Michael-A-Kuykendall/contextlite/releases/latest/download/contextlite_windows_amd64.zip"
curl -L -o contextlite.zip "$RELEASE_URL"

# Extract and verify
echo "📦 Extracting..."
unzip -q contextlite.zip
chmod +x contextlite.exe 2>/dev/null || true

# Test version
echo "🔍 Testing version..."
VERSION=$(./contextlite.exe --version 2>&1 || echo "FAILED")
echo "Version output: $VERSION"

# Test server startup
echo "🚀 Testing server startup..."
PORT=19001
timeout 15s ./contextlite.exe --port $PORT &
SERVER_PID=$!
sleep 10

# Test endpoints
echo "🌐 Testing endpoints..."
curl -f "http://localhost:$PORT/health" || echo "❌ Health check failed"
curl -f "http://localhost:$PORT/api/v1/trial/info" || echo "❌ Trial info failed"
curl -f "http://localhost:$PORT/license/status" || echo "❌ License status failed"

# Cleanup
kill $SERVER_PID 2>/dev/null || true
cd /
rm -rf "$TEST_DIR"

echo "✅ Direct binary test completed"
```

### **2. NPM PACKAGE TESTING**

**Test Script**: `test_npm_package.sh`
```bash
#!/bin/bash
set -e

echo "🧪 Testing npm Package Installation"

# Test global installation
echo "📥 Installing contextlite via npm..."
npm install -g contextlite || {
    echo "❌ npm install failed"
    exit 1
}

# Test command availability
echo "🔍 Testing command availability..."
which contextlite || {
    echo "❌ contextlite command not found in PATH"
    exit 1
}

# Test version
echo "🔍 Testing version..."
VERSION=$(contextlite --version 2>&1 || echo "FAILED")
echo "Version output: $VERSION"

# Test server functionality
echo "🚀 Testing server functionality..."
PORT=19002
timeout 15s contextlite --port $PORT &
SERVER_PID=$!
sleep 10

# Test endpoints
echo "🌐 Testing endpoints..."
curl -f "http://localhost:$PORT/health" || echo "❌ Health check failed"
curl -f "http://localhost:$PORT/api/v1/trial/info" || echo "❌ Trial info failed"

# Cleanup
kill $SERVER_PID 2>/dev/null || true
npm uninstall -g contextlite

echo "✅ npm package test completed"
```

### **3. PYPI PACKAGE TESTING**

**Test Script**: `test_pypi_package.sh`
```bash
#!/bin/bash
set -e

echo "🧪 Testing PyPI Package Installation"

# Create virtual environment
echo "🏗️ Creating virtual environment..."
python -m venv /tmp/contextlite-pypi-test
source /tmp/contextlite-pypi-test/bin/activate 2>/dev/null || \
source /tmp/contextlite-pypi-test/Scripts/activate

# Install package
echo "📥 Installing contextlite via pip..."
pip install contextlite || {
    echo "❌ pip install failed"
    exit 1
}

# Test command availability
echo "🔍 Testing command availability..."
which contextlite || {
    echo "❌ contextlite command not found"
    exit 1
}

# Test version
echo "🔍 Testing version..."
VERSION=$(contextlite --version 2>&1 || echo "FAILED")
echo "Version output: $VERSION"

# Test Python import
echo "🐍 Testing Python import..."
python -c "import contextlite; print('Python import successful')" || {
    echo "❌ Python import failed"
}

# Test server functionality
echo "🚀 Testing server functionality..."
PORT=19003
timeout 15s contextlite --port $PORT &
SERVER_PID=$!
sleep 10

# Test endpoints
echo "🌐 Testing endpoints..."
curl -f "http://localhost:$PORT/health" || echo "❌ Health check failed"
curl -f "http://localhost:$PORT/api/v1/trial/info" || echo "❌ Trial info failed"

# Cleanup
kill $SERVER_PID 2>/dev/null || true
deactivate
rm -rf /tmp/contextlite-pypi-test

echo "✅ PyPI package test completed"
```

### **4. DOCKER CONTAINER TESTING**

**Test Script**: `test_docker_container.sh`
```bash
#!/bin/bash
set -e

echo "🧪 Testing Docker Container"

# Test docker pull
echo "📥 Pulling Docker image..."
docker pull michaelakuykendall/contextlite:latest || {
    echo "❌ Docker pull failed"
    exit 1
}

# Test version
echo "🔍 Testing version..."
VERSION=$(docker run --rm michaelakuykendall/contextlite:latest --version 2>&1 || echo "FAILED")
echo "Version output: $VERSION"

# Test server in container
echo "🚀 Testing containerized server..."
PORT=19004
docker run -d --name contextlite-test -p $PORT:8080 michaelakuykendall/contextlite:latest
sleep 15

# Test endpoints
echo "🌐 Testing endpoints..."
curl -f "http://localhost:$PORT/health" || echo "❌ Health check failed"
curl -f "http://localhost:$PORT/api/v1/trial/info" || echo "❌ Trial info failed"

# Test logs
echo "📋 Checking logs..."
docker logs contextlite-test

# Cleanup
docker stop contextlite-test
docker rm contextlite-test

echo "✅ Docker container test completed"
```

### **5. HUGGING FACE SPACES TESTING**

**Test Script**: `test_hugging_face.sh`
```bash
#!/bin/bash
set -e

echo "🧪 Testing Hugging Face Spaces"

# Test page accessibility
echo "🌐 Testing Hugging Face page..."
RESPONSE=$(curl -s -o /dev/null -w "%{http_code}" "https://huggingface.co/spaces/MikeKuykendall/contextlite-download")
if [ "$RESPONSE" = "200" ]; then
    echo "✅ Hugging Face page accessible"
else
    echo "❌ Hugging Face page returned $RESPONSE"
fi

# Test download links
echo "🔗 Testing download links..."
curl -s "https://huggingface.co/spaces/MikeKuykendall/contextlite-download" | grep -q "GitHub API" && \
    echo "✅ GitHub API integration working" || \
    echo "❌ GitHub API integration not found"

# Test direct API call to HF space
echo "🤖 Testing Gradio API..."
curl -s "https://mikekuykendall-contextlite-download.hf.space/" > /dev/null && \
    echo "✅ Gradio app accessible" || \
    echo "❌ Gradio app not accessible"

echo "✅ Hugging Face test completed"
```

---

## 🚀 PHASE 2: AUTOMATED TESTING INFRASTRUCTURE

### **Master Test Runner**

Create `run_all_tests.sh`:
```bash
#!/bin/bash
set -e

echo "🧪 ContextLite Integration Test Suite"
echo "======================================="
echo "Date: $(date)"
echo "Testing all deployment channels..."
echo ""

# Create results directory
RESULTS_DIR="test/integration/results/$(date +%Y%m%d-%H%M%S)"
mkdir -p "$RESULTS_DIR"

# Test each channel
TESTS=(
    "test_direct_binary.sh"
    "test_npm_package.sh" 
    "test_pypi_package.sh"
    "test_docker_container.sh"
    "test_hugging_face.sh"
)

PASSED=0
FAILED=0

for test in "${TESTS[@]}"; do
    echo "🔄 Running $test..."
    if bash "test/integration/scripts/$test" > "$RESULTS_DIR/$test.log" 2>&1; then
        echo "✅ $test PASSED"
        ((PASSED++))
    else
        echo "❌ $test FAILED"
        ((FAILED++))
        echo "   Check log: $RESULTS_DIR/$test.log"
    fi
done

echo ""
echo "📊 RESULTS SUMMARY"
echo "=================="
echo "✅ Passed: $PASSED"
echo "❌ Failed: $FAILED"
echo "📁 Logs: $RESULTS_DIR"

if [ $FAILED -eq 0 ]; then
    echo "🎉 ALL TESTS PASSED!"
    exit 0
else
    echo "⚠️  SOME TESTS FAILED - REVIEW REQUIRED"
    exit 1
fi
```

### **Docker-Based Cross-Platform Testing**

Create `docker/test-environments/`:

**Ubuntu Test Environment** (`Dockerfile.ubuntu`):
```dockerfile
FROM ubuntu:22.04

RUN apt-get update && apt-get install -y \
    curl \
    python3 \
    python3-pip \
    nodejs \
    npm \
    docker.io \
    unzip \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /test
COPY scripts/ ./scripts/
RUN chmod +x scripts/*.sh

CMD ["bash", "scripts/test_all_ubuntu.sh"]
```

**Alpine Test Environment** (`Dockerfile.alpine`):
```dockerfile
FROM alpine:latest

RUN apk add --no-cache \
    curl \
    python3 \
    py3-pip \
    nodejs \
    npm \
    docker \
    unzip \
    bash

WORKDIR /test
COPY scripts/ ./scripts/
RUN chmod +x scripts/*.sh

CMD ["bash", "scripts/test_all_alpine.sh"]
```

### **Multi-Platform Test Runner**

Create `test_all_platforms.sh`:
```bash
#!/bin/bash
set -e

echo "🧪 Multi-Platform Integration Testing"
echo "====================================="

PLATFORMS=("ubuntu" "alpine")
RESULTS_BASE="test/integration/results/multiplatform-$(date +%Y%m%d-%H%M%S)"

for platform in "${PLATFORMS[@]}"; do
    echo "🐳 Testing on $platform..."
    
    # Build test environment
    docker build -f "docker/test-environments/Dockerfile.$platform" \
        -t "contextlite-test-$platform" \
        test/integration/
    
    # Run tests
    RESULTS_DIR="$RESULTS_BASE/$platform"
    mkdir -p "$RESULTS_DIR"
    
    if docker run --rm \
        -v "$PWD/$RESULTS_DIR:/test/results" \
        "contextlite-test-$platform" > "$RESULTS_DIR/output.log" 2>&1; then
        echo "✅ $platform tests PASSED"
    else
        echo "❌ $platform tests FAILED"
        echo "   Check: $RESULTS_DIR/output.log"
    fi
done

echo "📊 Multi-platform testing completed"
echo "📁 Results in: $RESULTS_BASE"
```

---

## 📊 PHASE 3: CONTINUOUS MONITORING

### **Automated Health Check System**

Create `monitor_deployments.sh`:
```bash
#!/bin/bash

echo "🔍 ContextLite Deployment Health Monitor"
echo "======================================="

# Check all critical endpoints
ENDPOINTS=(
    "https://huggingface.co/spaces/MikeKuykendall/contextlite-download"
    "https://registry.npmjs.org/contextlite"
    "https://pypi.org/project/contextlite/"
    "https://hub.docker.com/r/michaelakuykendall/contextlite"
)

for endpoint in "${ENDPOINTS[@]}"; do
    echo -n "🌐 Checking $endpoint... "
    if curl -s -o /dev/null -w "%{http_code}" "$endpoint" | grep -q "200"; then
        echo "✅"
    else
        echo "❌"
        echo "   ALERT: $endpoint is not responding correctly"
    fi
done

# Check GitHub releases
echo -n "📦 Checking GitHub releases... "
LATEST_RELEASE=$(curl -s "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases/latest" | grep -o '"tag_name": "[^"]*' | cut -d'"' -f4)
if [ -n "$LATEST_RELEASE" ]; then
    echo "✅ Latest: $LATEST_RELEASE"
else
    echo "❌ Could not fetch latest release"
fi

echo "🔍 Health check completed at $(date)"
```

### **Daily Integration Test Cron Job**

Create `setup_monitoring.sh`:
```bash
#!/bin/bash

echo "⚙️ Setting up continuous monitoring..."

# Create daily test script
cat > daily_integration_test.sh << 'EOF'
#!/bin/bash
cd /path/to/contextlite
./test/integration/run_all_tests.sh > "test/integration/results/daily-$(date +%Y%m%d).log" 2>&1

if [ $? -eq 0 ]; then
    echo "✅ Daily integration tests passed" | mail -s "ContextLite Tests: PASS" admin@contextlite.com
else
    echo "❌ Daily integration tests failed - check logs" | mail -s "ContextLite Tests: FAIL" admin@contextlite.com
fi
EOF

chmod +x daily_integration_test.sh

# Add to crontab (run daily at 2 AM)
echo "0 2 * * * /path/to/contextlite/daily_integration_test.sh" >> mycron
crontab mycron
rm mycron

echo "✅ Monitoring setup completed"
echo "   Daily tests will run at 2:00 AM"
echo "   Results will be emailed to admin@contextlite.com"
```

---

## 🛡️ PHASE 4: FAILURE RECOVERY & DOCUMENTATION

### **Test Failure Investigation Protocol**

Create `investigate_failure.sh`:
```bash
#!/bin/bash

FAILURE_TYPE="$1"
TEST_NAME="$2"

echo "🔍 Investigating test failure: $TEST_NAME"
echo "========================================="

case "$FAILURE_TYPE" in
    "npm")
        echo "📦 NPM Package Issues:"
        npm view contextlite
        npm audit contextlite
        ;;
    "pypi")
        echo "🐍 PyPI Package Issues:"
        pip show contextlite
        pip install --dry-run contextlite
        ;;
    "docker")
        echo "🐳 Docker Issues:"
        docker images | grep contextlite
        docker history michaelakuykendall/contextlite:latest
        ;;
    "direct")
        echo "💾 Direct Binary Issues:"
        curl -I "https://github.com/Michael-A-Kuykendall/contextlite/releases/latest"
        ;;
    *)
        echo "❓ Unknown failure type: $FAILURE_TYPE"
        ;;
esac

echo ""
echo "🔧 Suggested recovery steps:"
echo "1. Check the specific error logs"
echo "2. Verify GitHub Actions are working"
echo "3. Test manual deployment process"
echo "4. Update documentation if needed"
```

### **Emergency Rollback Procedures**

Create `emergency_rollback.md`:
```markdown
# 🚨 EMERGENCY ROLLBACK PROCEDURES

## When to Use
- Critical installation failures across multiple platforms
- Security vulnerabilities discovered in deployed packages
- License server failures affecting trial system

## Immediate Actions

### 1. GitHub Releases
```bash
# Delete problematic release
gh release delete v0.9.0 --yes
# Restore previous working release
gh release create v0.8.9 --title "Emergency Rollback" --notes "Rollback due to critical issues"
```

### 2. NPM Package
```bash
npm unpublish contextlite@0.9.0
npm publish ./contextlite-0.8.9.tgz
```

### 3. PyPI Package
```bash
# Contact PyPI support for emergency unpublish
# Usually requires support ticket
```

### 4. Docker Hub
```bash
docker push michaelakuykendall/contextlite:0.8.9
docker tag michaelakuykendall/contextlite:0.8.9 michaelakuykendall/contextlite:latest
docker push michaelakuykendall/contextlite:latest
```

### 5. Hugging Face
```bash
cd contextlite-download
git revert HEAD
git push
```
```

---

## 📋 IMMEDIATE ACTION PLAN

### **Step 1: Run Current Platform Tests (5 minutes)**
```bash
# Create the directory structure
mkdir -p test/integration/{scripts,logs,results}

# Run immediate validation
bash test/integration/scripts/test_direct_binary.sh
bash test/integration/scripts/test_npm_package.sh
bash test/integration/scripts/test_pypi_package.sh
bash test/integration/scripts/test_docker_container.sh
bash test/integration/scripts/test_hugging_face.sh
```

### **Step 2: Document Current Status (10 minutes)**
Create a test results log with:
- What works correctly
- What has issues  
- What needs immediate fixes
- Performance metrics (response times, etc.)

### **Step 3: Setup Automated Testing (30 minutes)**
1. Create all the test scripts above
2. Set up Docker environments
3. Configure monitoring system
4. Test the complete framework

### **Step 4: Cross-Platform Validation (1-2 hours)**
- Spin up Docker Desktop if needed
- Test Ubuntu and Alpine environments
- Validate on actual different platforms if available
- Document platform-specific issues

---

## 🎯 SUCCESS CRITERIA

**Must Pass Before Continuing:**
- [ ] All 5 main deployment channels work correctly
- [ ] Version numbers are consistent across all packages
- [ ] Trial system works on all platforms
- [ ] Health endpoints respond < 500ms on all platforms
- [ ] No authentication/permission issues
- [ ] Clean uninstall process works

**Quality Gates:**
- [ ] Automated test suite runs successfully
- [ ] Multi-platform Docker tests pass
- [ ] Monitoring system operational
- [ ] Failure recovery procedures tested
- [ ] Documentation is complete and accurate

---

**CURRENT STATUS**: Framework designed - ready for implementation  
**NEXT STEP**: Create test scripts and run immediate validation  
**PRIORITY**: HIGH - Production systems are live and need validation
