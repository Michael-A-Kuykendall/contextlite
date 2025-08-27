# PUNCH-powered Architecture Analysis Script (PowerShell)
# Analyzes ContextLite codebase and generates comprehensive documentation

param(
    [switch]$Verbose = $false
)

# Colors for output
$Colors = @{
    Red = "Red"
    Green = "Green" 
    Yellow = "Yellow"
    Blue = "Blue"
    Cyan = "Cyan"
}

function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

Write-ColorOutput "╔══════════════════════════════════════════════════════════════╗" -Color $Colors.Blue
Write-ColorOutput "║          🥊 PUNCH-POWERED ARCHITECTURE ANALYSIS             ║" -Color $Colors.Blue
Write-ColorOutput "║                    ContextLite Codebase                     ║" -Color $Colors.Blue
Write-ColorOutput "╚══════════════════════════════════════════════════════════════╝" -Color $Colors.Blue

# Create output directory
if (-not (Test-Path "punch_results")) {
    New-Item -ItemType Directory -Path "punch_results" | Out-Null
}

Write-ColorOutput "🔍 Discovering components..." -Color $Colors.Cyan
& ".\.punch-tool\punch.exe" discover . --languages go --verbose --output json | Out-File -FilePath "punch_results\components.json" -Encoding UTF8

Write-ColorOutput "📊 Analyzing architecture patterns..." -Color $Colors.Cyan
& ".\.punch-tool\punch.exe" query "HTTP handlers" --output table | Out-File -FilePath "punch_results\http_handlers.txt" -Encoding UTF8

Write-ColorOutput "📈 Generating statistics..." -Color $Colors.Cyan
& ".\.punch-tool\punch.exe" stats --output json | Out-File -FilePath "punch_results\stats.json" -Encoding UTF8

Write-ColorOutput "🔗 Mapping functions..." -Color $Colors.Cyan
& ".\.punch-tool\punch.exe" list --type=function --output table | Out-File -FilePath "punch_results\functions.txt" -Encoding UTF8

Write-ColorOutput "✅ Analysis complete! Results saved to punch_results\" -Color $Colors.Green
Write-Host ""
Write-ColorOutput "📋 Generated Files:" -Color $Colors.Yellow
Write-Host "   • punch_results\components.json     - All discovered components"
Write-Host "   • punch_results\http_handlers.txt   - HTTP handler analysis"
Write-Host "   • punch_results\stats.json          - Codebase statistics"
Write-Host "   • punch_results\functions.txt       - All discovered functions"
Write-Host ""
Write-ColorOutput "🚀 Quick Actions:" -Color $Colors.Yellow
Write-Host "   View components:  Get-Content punch_results\components.json | ConvertFrom-Json"
Write-Host "   View stats:       Get-Content punch_results\stats.json"
Write-Host "   View handlers:    Get-Content punch_results\http_handlers.txt"