$ErrorActionPreference = 'Stop'

$packageName = 'contextlite'

# Remove the shim
Uninstall-ChocolateyShim -Name 'contextlite'

Write-Host "ContextLite has been uninstalled." -ForegroundColor Green
