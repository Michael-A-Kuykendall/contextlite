$ErrorActionPreference = 'Stop'

$packageName = 'contextlite'
$toolsDir = "$(Split-Path -parent $MyInvocation.MyCommand.Definition)"
$url64 = 'RELEASE_URL_PLACEHOLDER'

# Package parameters
$packageArgs = @{
  packageName    = $packageName
  unzipLocation  = $toolsDir
  fileType       = 'zip'
  url64bit       = $url64
  softwareName   = 'ContextLite*'
  
  # Checksums - Dynamic replacement by CI
  checksum64     = 'RELEASE_CHECKSUM_PLACEHOLDER'
  checksumType64 = 'sha256'
  
  validExitCodes = @(0)
}

Install-ChocolateyZipPackage @packageArgs

# After extraction, the Windows archive contains contextlite.exe
# Support potential future naming (contextlite-windows-*.exe) by probing.
$candidateNames = @('contextlite.exe','contextlite-windows-amd64.exe','contextlite-windows-arm64.exe')
$exePath = $null
foreach ($name in $candidateNames) {
  $p = Join-Path $toolsDir $name
  if (Test-Path $p) { $exePath = $p; break }
}

if (-not $exePath) {
  Write-Error "Installation failed - no executable found in $toolsDir"
  exit 1
}

# Create shim named 'contextlite'
Install-ChocolateyShim -Name 'contextlite' -Path $exePath
Write-Host "ContextLite installed successfully!" -ForegroundColor Green
Write-Host "Binary: $exePath" -ForegroundColor DarkGray
Write-Host "Use 'contextlite --help' to get started." -ForegroundColor Yellow
