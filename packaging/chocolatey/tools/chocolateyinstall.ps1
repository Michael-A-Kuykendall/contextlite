$ErrorActionPreference = 'Stop'

$packageName = 'contextlite'
$toolsDir = "$(Split-Path -parent $MyInvocation.MyCommand.Definition)"
$url64 = 'https://github.com/Michael-A-Kuykendall/contextlite/releases/latest/download/contextlite_windows_amd64.zip'

$packageArgs = @{
  packageName   = $packageName
  unzipLocation = $toolsDir
  url64bit      = $url64
  
  softwareName  = 'ContextLite*'
  
  checksum64    = ''
  checksumType64= 'sha256'
  
  validExitCodes= @(0)
}

# Download and extract the binary
Install-ChocolateyZipPackage @packageArgs

# Find the contextlite.exe binary in the extracted files
$exePath = Get-ChildItem -Path $toolsDir -Recurse -Filter "contextlite.exe" | Select-Object -First 1

if ($exePath) {
    # Create a shim for the binary
    Install-ChocolateyPath -PathToInstall (Split-Path $exePath.FullName -Parent)
    
    Write-Host "ContextLite has been installed successfully!" -ForegroundColor Green
    Write-Host "You can now use 'contextlite' command from anywhere in the command line." -ForegroundColor Green
    Write-Host ""
    Write-Host "Try: contextlite --version" -ForegroundColor Yellow
} else {
    throw "Could not find contextlite.exe in the downloaded package"
}
