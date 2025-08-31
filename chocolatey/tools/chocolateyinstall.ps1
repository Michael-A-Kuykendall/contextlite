$ErrorActionPreference = 'Stop'

$packageName = 'contextlite'
$toolsDir = "$(Split-Path -parent $MyInvocation.MyCommand.Definition)"
$url64 = "RELEASE_URL_PLACEHOLDER"

# Package parameters
$packageArgs = @{
  packageName   = $packageName
  unzipLocation = $toolsDir
  fileType      = 'zip'
  url64bit      = $url64
  softwareName  = 'ContextLite*'
  
  # Checksums will be updated by workflow
  checksum64    = "RELEASE_CHECKSUM_PLACEHOLDER"
  checksumType64= 'sha256'
  
  # Silent install arguments (not needed for single exe)
  silentArgs    = ""
  validExitCodes= @(0)
}

# Download and install ZIP package
Install-ChocolateyZipPackage @packageArgs

# Create shims for both executables
$contextliteExe = Join-Path $toolsDir 'contextlite.exe'
$onboardExe = Join-Path $toolsDir 'contextlite-onboard.exe'

if (Test-Path $contextliteExe) {
    Install-BinFile -Name 'contextlite' -Path $contextliteExe
    Write-Host "ContextLite 2.0 installed successfully!" -ForegroundColor Green
    
    if (Test-Path $onboardExe) {
        Install-BinFile -Name 'contextlite-onboard' -Path $onboardExe
        Write-Host "ContextLite Onboarding tool installed!" -ForegroundColor Green
        Write-Host "Run 'contextlite --onboard' for 30-second auto-discovery setup!" -ForegroundColor Cyan
    } else {
        Write-Host "Note: contextlite-onboard.exe not found, using integrated onboarding" -ForegroundColor Yellow
        Write-Host "Run 'contextlite --onboard' for auto-discovery setup!" -ForegroundColor Cyan
    }
    
    Write-Host "Use 'contextlite --help' for all options." -ForegroundColor Yellow
} else {
    Write-Error "Installation failed - contextlite.exe not found at $contextliteExe"
}
