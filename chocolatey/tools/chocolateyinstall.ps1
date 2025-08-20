$ErrorActionPreference = 'Stop'

$packageName = 'contextlite'
$toolsDir = "$(Split-Path -parent $MyInvocation.MyCommand.Definition)"
$url64 = 'RELEASE_URL_PLACEHOLDER'

# Package parameters
$packageArgs = @{
  packageName   = $packageName
  unzipLocation = $toolsDir
  fileType      = 'zip'
  url64bit      = $url64
  softwareName  = 'ContextLite*'
  
  # Checksums - Dynamic replacement by CI
  checksum64    = 'RELEASE_CHECKSUM_PLACEHOLDER'
  checksumType64= 'sha256'
  
  # Silent install arguments (not needed for single exe)
  silentArgs    = ""
  validExitCodes= @(0)
}

# Download and extract
Install-ChocolateyZipPackage @packageArgs

# Create a shim for the executable
$exePath = Join-Path $toolsDir 'contextlite-windows-amd64'
if (Test-Path $exePath) {
    Install-ChocolateyShim -Name 'contextlite' -Path $exePath
    Write-Host "ContextLite installed successfully!" -ForegroundColor Green
    Write-Host "Use 'contextlite --help' to get started." -ForegroundColor Yellow
} else {
    Write-Error "Installation failed - executable not found at $exePath"
}
