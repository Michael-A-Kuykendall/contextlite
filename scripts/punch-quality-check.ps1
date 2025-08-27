# PUNCH Quality Analysis Integration (PowerShell)
# Runs comprehensive code quality analysis using PUNCH discovery

param(
    [switch]$Verbose = $false
)

function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

Write-ColorOutput "🥊 PUNCH Quality Analysis" -Color Blue
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Create results directory
if (-not (Test-Path "punch_results\quality")) {
    New-Item -ItemType Directory -Path "punch_results\quality" -Force | Out-Null
}

Write-ColorOutput "🔍 Discovering all components..." -Color Cyan
$componentData = & ".\.punch-tool\punch.exe" discover . --languages go --output json | ConvertFrom-Json
$componentCount = if ($componentData.components) { $componentData.components.Count } else { 0 }

Write-ColorOutput "📊 Analyzing function complexity..." -Color Cyan
& ".\.punch-tool\punch.exe" list --type=function --output table | Out-File -FilePath "punch_results\quality\functions.txt" -Encoding UTF8

Write-ColorOutput "🔗 Checking dependency complexity..." -Color Cyan
& ".\.punch-tool\punch.exe" list --type=struct --output table | Out-File -FilePath "punch_results\quality\structs.txt" -Encoding UTF8

Write-ColorOutput "⚡ Performance hotspot detection..." -Color Cyan
& ".\.punch-tool\punch.exe" query "benchmark|performance|optimize" --output table | Out-File -FilePath "punch_results\quality\performance.txt" -Encoding UTF8

Write-ColorOutput "🛡️ Security pattern analysis..." -Color Cyan
& ".\.punch-tool\punch.exe" query "auth|security|crypto|license" --output table | Out-File -FilePath "punch_results\quality\security.txt" -Encoding UTF8

Write-ColorOutput "🧪 Test coverage analysis..." -Color Cyan
& ".\.punch-tool\punch.exe" query "Test*|*_test.go" --output table | Out-File -FilePath "punch_results\quality\tests.txt" -Encoding UTF8

# Generate summary
Write-ColorOutput "✅ Quality Analysis Complete!" -Color Green
Write-Host ""
Write-ColorOutput "📋 Quality Report Summary:" -Color Yellow
Write-Host "   Total Components: $componentCount"

$functionLines = if (Test-Path "punch_results\quality\functions.txt") { (Get-Content "punch_results\quality\functions.txt").Count } else { 0 }
$structLines = if (Test-Path "punch_results\quality\structs.txt") { (Get-Content "punch_results\quality\structs.txt").Count } else { 0 }
$performanceLines = if (Test-Path "punch_results\quality\performance.txt") { (Get-Content "punch_results\quality\performance.txt").Count } else { 0 }
$securityLines = if (Test-Path "punch_results\quality\security.txt") { (Get-Content "punch_results\quality\security.txt").Count } else { 0 }
$testLines = if (Test-Path "punch_results\quality\tests.txt") { (Get-Content "punch_results\quality\tests.txt").Count } else { 0 }

Write-Host "   Functions:        $functionLines analyzed"
Write-Host "   Structs:          $structLines analyzed" 
Write-Host "   Performance:      $performanceLines hotspots"
Write-Host "   Security:         $securityLines patterns"
Write-Host "   Tests:            $testLines test files"
Write-Host ""
Write-ColorOutput "📁 Results saved to: punch_results\quality\" -Color Yellow