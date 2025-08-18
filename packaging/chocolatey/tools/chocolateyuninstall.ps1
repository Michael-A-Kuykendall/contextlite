$ErrorActionPreference = 'Stop'

$packageName = 'contextlite'

# Remove from PATH if it was added during installation
$toolsDir = "$(Split-Path -parent $MyInvocation.MyCommand.Definition)"
$exePath = Get-ChildItem -Path $toolsDir -Recurse -Filter "contextlite.exe" | Select-Object -First 1

if ($exePath) {
    $binDir = Split-Path $exePath.FullName -Parent
    
    # Remove from PATH
    Install-ChocolateyPath -PathToInstall $binDir -PathType 'Machine' -Remove
    
    Write-Host "ContextLite has been uninstalled successfully!" -ForegroundColor Green
}
