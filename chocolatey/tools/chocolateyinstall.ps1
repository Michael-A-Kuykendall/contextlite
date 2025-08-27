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

# Create a shim for the executable
$exePath = Join-Path $toolsDir 'contextlite.exe'
if (Test-Path $exePath) {
    Install-BinFile -Name 'contextlite' -Path $exePath
    Write-Host "ContextLite installed successfully!" -ForegroundColor Green
    Write-Host "Use 'contextlite --help' to get started." -ForegroundColor Yellow
} else {
    Write-Error "Installation failed - executable not found at $exePath"
}
