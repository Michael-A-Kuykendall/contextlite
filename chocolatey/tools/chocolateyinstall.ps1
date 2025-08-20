$ErrorActionPreference = 'Stop'

$packageName = 'contextlite'
$toolsDir = "$(Split-Path -parent $MyInvocation.MyCommand.Definition)"
$url64 = 'https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v1.0.8/contextlite-1.0.8-windows-amd64.zip'

# Package parameters
$packageArgs = @{
  packageName   = $packageName
  unzipLocation = $toolsDir
  fileType      = 'zip'
  url64bit      = $url64
  softwareName  = 'ContextLite*'
  
  # Checksums
  checksum64    = 'YOUR_CHECKSUM_HERE'
  checksumType64= 'sha256'
  
  # Silent install arguments (not needed for single exe)
  silentArgs    = ""
  validExitCodes= @(0)
}

# Download and extract
Install-ChocolateyZipPackage @packageArgs

# Create a shim for the executable
$exePath = Join-Path $toolsDir 'contextlite.exe'
if (Test-Path $exePath) {
    Install-ChocolateyShim -Name 'contextlite' -Path $exePath
    Write-Host "ContextLite installed successfully!" -ForegroundColor Green
    Write-Host "Use 'contextlite --help' to get started." -ForegroundColor Yellow
} else {
    Write-Error "Installation failed - executable not found at $exePath"
}
