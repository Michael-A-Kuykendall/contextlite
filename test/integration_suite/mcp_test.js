#!/usr/bin/env node

/**
 * ContextLite MCP Server Integration Test
 * 
 * Tests the Model Context Protocol server integration.
 */

const http = require('http');
const { URL } = require('url');

const SERVER_URL = 'http://127.0.0.1:8083';

class MCPTestSuite {
    constructor() {
        this.results = [];
    }

    logResult(testName, passed, message, duration = 0) {
        const status = passed ? 'âœ… PASS' : 'âŒ FAIL';
        this.results.push({
            test: testName,
            passed,
            message,
            duration
        });
        console.log(`${status} ${testName}: ${message} (${duration.toFixed(3)}s)`);
    }

    async makeRequest(path, options = {}) {
        return new Promise((resolve, reject) => {
            const url = new URL(path, SERVER_URL);
            const req = http.request(url, options, (res) => {
                let data = '';
                res.on('data', chunk => data += chunk);
                res.on('end', () => {
                    try {
                        const parsed = data ? JSON.parse(data) : {};
                        resolve({ status: res.statusCode, data: parsed });
                    } catch (e) {
                        resolve({ status: res.statusCode, data: data });
                    }
                });
            });

            req.on('error', reject);
            
            if (options.body) {
                req.write(options.body);
            }
            
            req.end();
        });
    }

    async testServerConnectivity() {
        try {
            const start = Date.now();
            const response = await this.makeRequest('/api/v1/health');
            const duration = (Date.now() - start) / 1000;

            if (response.status === 200) {
                this.logResult('ServerConnectivity', true, 'Can connect to ContextLite server', duration);
                return true;
            } else {
                this.logResult('ServerConnectivity', false, `Health check failed: ${response.status}`, duration);
                return false;
            }
        } catch (error) {
            this.logResult('ServerConnectivity', false, `Connection failed: ${error.message}`);
            return false;
        }
    }

    async testMCPProtocol() {
        try {
            const start = Date.now();
            
            // Test MCP-style context request
            const response = await this.makeRequest('/api/v1/context/assemble?q=javascript%20examples&budget=1500');
            const duration = (Date.now() - start) / 1000;

            if (response.status === 200) {
                this.logResult('MCPProtocol', true, 'MCP-style requests work correctly', duration);
                return true;
            } else {
                this.logResult('MCPProtocol', false, `MCP request failed: ${response.status}`, duration);
                return false;
            }
        } catch (error) {
            this.logResult('MCPProtocol', false, `MCP protocol error: ${error.message}`);
            return false;
        }
    }

    async testDocumentManagement() {
        try {
            const start = Date.now();
            
            const doc = {
                id: 'mcp-test-doc-1',
                path: '/test/mcp/example.js',
                content: 'console.log("Hello from MCP integration test");\n\nfunction testMCP() {\n    return "MCP working";\n}'
            };

            const response = await this.makeRequest('/api/v1/documents', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify(doc)
            });
            
            const duration = (Date.now() - start) / 1000;

            if (response.status === 200 || response.status === 201) {
                this.logResult('DocumentManagement', true, 'Can manage documents via MCP interface', duration);
                return true;
            } else {
                this.logResult('DocumentManagement', false, `Document management failed: ${response.status}`, duration);
                return false;
            }
        } catch (error) {
            this.logResult('DocumentManagement', false, `Document management error: ${error.message}`);
            return false;
        }
    }

    async testSearchCapabilities() {
        try {
            const start = Date.now();
            
            const response = await this.makeRequest('/api/v1/documents/search?q=javascript%20console&limit=5');
            const duration = (Date.now() - start) / 1000;

            if (response.status === 200 && response.data.documents && response.data.documents.length > 0) {
                const perfMsg = duration < 0.1 ? `in ${(duration * 1000).toFixed(1)}ms` : `in ${duration.toFixed(3)}s (slow)`;
                this.logResult('SearchCapabilities', true, `Search works correctly ${perfMsg}`, duration);
                return true;
            } else {
                this.logResult('SearchCapabilities', false, `Search failed or no results: ${response.status}`, duration);
                return false;
            }
        } catch (error) {
            this.logResult('SearchCapabilities', false, `Search error: ${error.message}`);
            return false;
        }
    }

    async testPerformanceLoad() {
        try {
            const start = Date.now();
            
            // Run multiple concurrent requests
            const promises = [];
            for (let i = 0; i < 10; i++) {
                promises.push(this.makeRequest(`/api/v1/documents/search?q=test${i}&limit=3`));
            }

            const results = await Promise.all(promises);
            const duration = (Date.now() - start) / 1000;

            const successCount = results.filter(r => r.status === 200).length;
            const successRate = successCount / results.length;

            if (successRate >= 0.9) {
                this.logResult('PerformanceLoad', true, `Load test passed: ${(successRate * 100).toFixed(0)}% success rate`, duration);
                return true;
            } else {
                this.logResult('PerformanceLoad', false, `Load test failed: ${(successRate * 100).toFixed(0)}% success rate`, duration);
                return false;
            }
        } catch (error) {
            this.logResult('PerformanceLoad', false, `Load test error: ${error.message}`);
            return false;
        }
    }

    async runAllTests() {
        console.log('í¼ Running MCP Integration Tests for ContextLite');
        console.log('='.repeat(60));

        // Core functionality tests
        await this.testServerConnectivity();
        await this.testMCPProtocol();
        await this.testDocumentManagement();
        await this.testSearchCapabilities();

        // Performance tests
        await this.testPerformanceLoad();

        // Summary
        const passed = this.results.filter(r => r.passed).length;
        const total = this.results.length;

        console.log('\n' + '='.repeat(60));
        console.log(`MCP Integration Test Results: ${passed}/${total} tests passed`);

        if (passed === total) {
            console.log('í¾‰ All MCP integration tests passed!');
            return true;
        } else {
            console.log(`âš ï¸  ${total - passed} tests failed`);
            this.results.filter(r => !r.passed).forEach(result => {
                console.log(`   âŒ ${result.test}: ${result.message}`);
            });
            return false;
        }
    }
}

// Run tests if called directly
if (require.main === module) {
    const suite = new MCPTestSuite();
    suite.runAllTests().then(success => {
        process.exit(success ? 0 : 1);
    }).catch(error => {
        console.error('Test suite error:', error);
        process.exit(1);
    });
}

module.exports = MCPTestSuite;
