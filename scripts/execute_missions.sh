#!/bin/bash

# ContextLite Mission Execution Script
# Execute comprehensive testing and security missions using Rustchain/Shimmy

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MISSION_DIR="$REPO_ROOT/docs/mission-stacks/current"

echo "🚀 ContextLite Mission Execution Starting..."
echo "📁 Repository: $REPO_ROOT"
echo "🎯 Mission Directory: $MISSION_DIR"

# Check prerequisites
check_prerequisites() {
    echo "🔍 Checking prerequisites..."
    
    # Check for rustchain.exe
    if [[ ! -f "$REPO_ROOT/rustchain.exe" ]]; then
        echo "❌ Error: rustchain.exe not found in repository root"
        exit 1
    fi
    
    # Check for shimmy.exe
    if [[ ! -f "$REPO_ROOT/shimmy.exe" ]]; then
        echo "❌ Error: shimmy.exe not found in repository root"
        exit 1
    fi
    
    # Check if ContextLite server is running
    if ! curl -s http://localhost:8084/health > /dev/null 2>&1; then
        echo "⚠️  Warning: ContextLite server not running on port 8084"
        echo "   Starting server..."
        cd "$REPO_ROOT"
        ./contextlite.exe > contextlite.log 2>&1 &
        sleep 3
        
        if ! curl -s http://localhost:8084/health > /dev/null 2>&1; then
            echo "❌ Error: Failed to start ContextLite server"
            exit 1
        fi
    fi
    
    echo "✅ Prerequisites check passed"
}

# Validate mission files
validate_missions() {
    echo "📋 Validating mission files..."
    
    local missions=(
        "mission_3.1_security_audit.yaml"
        "mission_3.2_test_coverage_fixes.yaml" 
        "mission_3.3_database_import.yaml"
        "mission_3.4_security_hardening.yaml"
    )
    
    for mission in "${missions[@]}"; do
        local mission_file="$MISSION_DIR/$mission"
        if [[ ! -f "$mission_file" ]]; then
            echo "❌ Error: Mission file not found: $mission"
            exit 1
        fi
        
        echo "🔍 Validating: $mission"
        cd "$REPO_ROOT"
        if ! ./rustchain.exe mission validate "$mission_file"; then
            echo "❌ Error: Mission validation failed for $mission"
            exit 1
        fi
    done
    
    echo "✅ All missions validated successfully"
}

# Execute missions in sequence
execute_missions() {
    echo "🎯 Starting mission execution sequence..."
    
    local missions=(
        "mission_3.1_security_audit.yaml"
        "mission_3.2_test_coverage_fixes.yaml"
        "mission_3.3_database_import.yaml"
        "mission_3.4_security_hardening.yaml"
    )
    
    local success_count=0
    local total_missions=${#missions[@]}
    
    for mission in "${missions[@]}"; do
        local mission_file="$MISSION_DIR/$mission"
        local mission_name=$(basename "$mission" .yaml)
        
        echo ""
        echo "🚀 Executing Mission: $mission_name"
        echo "📄 File: $mission_file"
        echo "⏰ Started: $(date)"
        
        # Dry run first
        echo "🔍 Running dry-run validation..."
        cd "$REPO_ROOT"
        if ! ./rustchain.exe run --dry-run "$mission_file"; then
            echo "❌ Dry-run failed for $mission_name"
            echo "   Skipping execution to prevent issues"
            continue
        fi
        
        # Execute the mission
        echo "▶️  Executing mission..."
        if ./rustchain.exe run "$mission_file"; then
            echo "✅ Mission completed successfully: $mission_name"
            success_count=$((success_count + 1))
            
            # Move completed mission to done folder
            local done_dir="$REPO_ROOT/docs/mission-stacks/done"
            mkdir -p "$done_dir"
            local timestamp=$(date +"%Y%m%d_%H%M%S")
            mv "$mission_file" "$done_dir/${mission_name}_completed_${timestamp}.yaml"
            
        else
            echo "❌ Mission failed: $mission_name"
            echo "   Check logs for details"
            
            # Move failed mission to a failed subdirectory
            local failed_dir="$REPO_ROOT/docs/mission-stacks/failed"
            mkdir -p "$failed_dir"
            local timestamp=$(date +"%Y%m%d_%H%M%S")
            mv "$mission_file" "$failed_dir/${mission_name}_failed_${timestamp}.yaml"
        fi
        
        echo "⏰ Completed: $(date)"
    done
    
    echo ""
    echo "📊 Mission Execution Summary:"
    echo "   ✅ Successful: $success_count/$total_missions"
    echo "   ❌ Failed: $((total_missions - success_count))/$total_missions"
    
    if [[ $success_count -eq $total_missions ]]; then
        echo "🎉 All missions completed successfully!"
        return 0
    else
        echo "⚠️  Some missions failed. Review logs and retry failed missions."
        return 1
    fi
}

# Generate post-mission report
generate_report() {
    echo "📋 Generating post-mission execution report..."
    
    local report_file="$REPO_ROOT/MISSION_EXECUTION_REPORT_$(date +"%Y%m%d_%H%M%S").md"
    
    cat > "$report_file" << EOF
# ContextLite Mission Execution Report

**Execution Date:** $(date)
**Repository:** ContextLite
**Mission Count:** 4 missions

## Mission Results

### Security Audit (Mission 3.1)
- **Status:** $(check_mission_status "mission_3.1_security_audit")
- **Objective:** Comprehensive security testing and vulnerability assessment
- **Critical Issues:** Authentication, encryption, rate limiting

### Test Coverage Fixes (Mission 3.2)
- **Status:** $(check_mission_status "mission_3.2_test_coverage_fixes")
- **Objective:** Fix failing tests and achieve 95%+ coverage
- **Target:** 11/11 packages passing

### Database Import (Mission 3.3)
- **Status:** $(check_mission_status "mission_3.3_database_import")
- **Objective:** Complete project knowledge base population
- **Target:** 500+ documents imported

### Security Hardening (Mission 3.4)
- **Status:** $(check_mission_status "mission_3.4_security_hardening")
- **Objective:** Production-ready security implementation
- **Critical:** GDPR/CCPA compliance

## System Status After Missions

### Test Results
\`\`\`bash
$(cd "$REPO_ROOT" && make test 2>&1 | tail -20)
\`\`\`

### Database Status
\`\`\`bash
$(curl -s http://localhost:8084/api/v1/storage/info 2>/dev/null || echo "Server not responding")
\`\`\`

### Security Status
- Authentication: $(check_auth_status)
- Rate Limiting: $(check_rate_limit_status)
- Encryption: $(check_encryption_status)

## Recommendations

$(generate_recommendations)

---
Generated by ContextLite Mission Execution System
EOF

    echo "📄 Report generated: $report_file"
}

# Helper functions
check_mission_status() {
    local mission_name="$1"
    if [[ -f "$REPO_ROOT/docs/mission-stacks/done/${mission_name}_completed_"* ]]; then
        echo "✅ COMPLETED"
    elif [[ -f "$REPO_ROOT/docs/mission-stacks/failed/${mission_name}_failed_"* ]]; then
        echo "❌ FAILED"
    else
        echo "⏸️ NOT EXECUTED"
    fi
}

check_auth_status() {
    if curl -s -f http://localhost:8084/api/v1/documents > /dev/null 2>&1; then
        echo "⚠️ No authentication required"
    else
        echo "✅ Authentication required"
    fi
}

check_rate_limit_status() {
    # Simple rate limit test
    local responses=0
    for i in {1..10}; do
        if curl -s http://localhost:8084/health > /dev/null 2>&1; then
            responses=$((responses + 1))
        fi
    done
    
    if [[ $responses -eq 10 ]]; then
        echo "⚠️ No rate limiting detected"
    else
        echo "✅ Rate limiting active"
    fi
}

check_encryption_status() {
    # Check if database contains encrypted content
    if [[ -f "$REPO_ROOT/contextlite.db" ]]; then
        if strings "$REPO_ROOT/contextlite.db" | grep -q "BEGIN PUBLIC KEY\|AES\|encrypted" 2>/dev/null; then
            echo "✅ Encryption detected"
        else
            echo "⚠️ No encryption detected"
        fi
    else
        echo "❓ Database not found"
    fi
}

generate_recommendations() {
    echo "Based on mission execution results:"
    echo ""
    echo "### Immediate Actions Required"
    echo "- [ ] Verify all security implementations are working"
    echo "- [ ] Run comprehensive test suite"
    echo "- [ ] Validate database import completeness"
    echo "- [ ] Test production deployment scenario"
    echo ""
    echo "### Follow-up Tasks"
    echo "- [ ] Set up automated security monitoring"
    echo "- [ ] Implement regular security audits"
    echo "- [ ] Create deployment automation"
    echo "- [ ] Document security procedures"
}

# Main execution
main() {
    echo "🎯 ContextLite Mission Control System"
    echo "======================================"
    
    check_prerequisites
    validate_missions
    
    if execute_missions; then
        generate_report
        echo ""
        echo "🎉 Mission execution completed successfully!"
        echo "📋 Check the generated report for detailed results."
        exit 0
    else
        generate_report
        echo ""
        echo "⚠️ Mission execution completed with failures."
        echo "📋 Check the generated report and retry failed missions."
        exit 1
    fi
}

# Execute main function
main "$@"
