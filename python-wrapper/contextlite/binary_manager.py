"""
ContextLite Binary Manager

Handles detection, download, and management of ContextLite binaries
across different platforms and installation methods.
"""

import os
import platform
import shutil
import subprocess
from pathlib import Path
from typing import Optional, List
import requests
from platformdirs import user_data_dir

from .exceptions import BinaryNotFoundError, ContextLiteError


class BinaryManager:
    """Manages ContextLite binary detection and installation."""
    
    BINARY_NAME = "contextlite.exe" if platform.system() == "Windows" else "contextlite"
    GITHUB_REPO = "Michael-A-Kuykendall/contextlite"
    
    def __init__(self):
        self.platform = self._detect_platform()
        self.arch = self._detect_architecture()
        
    def get_binary_path(self) -> Optional[Path]:
        """
        Find ContextLite binary using multiple detection strategies.
        
        Returns:
            Path to binary if found, None otherwise
        """
        # Strategy 1: Check PATH
        path_binary = self._find_in_path()
        if path_binary:
            return path_binary
            
        # Strategy 2: Check common install locations
        system_binary = self._find_in_system_locations()
        if system_binary:
            return system_binary
            
        # Strategy 3: Check package data directory
        package_binary = self._find_in_package_data()
        if package_binary:
            return package_binary
            
        # Strategy 4: Check user data directory
        user_binary = self._find_in_user_data()
        if user_binary:
            return user_binary
            
        return None
        
    def download_binary(self, version: str = "latest") -> Path:
        """
        Download ContextLite binary from GitHub releases.
        
        Args:
            version: Version to download (default: latest)
            
        Returns:
            Path to downloaded binary
            
        Raises:
            ContextLiteError: If download fails
        """
        import zipfile
        import tarfile
        import tempfile
        
        try:
            download_url = self._get_download_url(version)
            dest_path = self._get_user_binary_path()
            
            print(f"📥 Downloading ContextLite {version} for {self.platform}-{self.arch}...")
            
            response = requests.get(download_url, stream=True)
            response.raise_for_status()
            
            # Create directory if it doesn't exist
            dest_path.parent.mkdir(parents=True, exist_ok=True)
            
            # Download to temporary file first
            with tempfile.NamedTemporaryFile(delete=False) as temp_file:
                for chunk in response.iter_content(chunk_size=8192):
                    temp_file.write(chunk)
                temp_path = Path(temp_file.name)
            
            try:
                # Extract binary from archive
                if download_url.endswith('.zip'):
                    with zipfile.ZipFile(temp_path, 'r') as zip_ref:
                        # Find the binary in the zip
                        for file_info in zip_ref.filelist:
                            if file_info.filename.endswith('.exe') or 'contextlite' in file_info.filename:
                                # Extract the binary
                                binary_data = zip_ref.read(file_info.filename)
                                with open(dest_path, 'wb') as f:
                                    f.write(binary_data)
                                break
                        else:
                            raise ContextLiteError("Binary not found in zip archive")
                            
                elif download_url.endswith('.tar.gz'):
                    with tarfile.open(temp_path, 'r:gz') as tar_ref:
                        # Find the binary in the tar
                        for member in tar_ref.getmembers():
                            if member.isfile() and ('contextlite' in member.name and not member.name.endswith('.txt')):
                                # Extract the binary
                                binary_file = tar_ref.extractfile(member)
                                if binary_file:
                                    with open(dest_path, 'wb') as f:
                                        f.write(binary_file.read())
                                    break
                        else:
                            raise ContextLiteError("Binary not found in tar archive")
                else:
                    # Direct binary download (fallback)
                    with open(dest_path, 'wb') as f:
                        with open(temp_path, 'rb') as temp_f:
                            f.write(temp_f.read())
                    
                # Make executable on Unix systems
                if platform.system() != "Windows":
                    dest_path.chmod(0o755)
                    
                print(f"✅ ContextLite downloaded and extracted to: {dest_path}")
                return dest_path
                
            finally:
                # Clean up temporary file
                temp_path.unlink()
            
        except requests.RequestException as e:
            raise ContextLiteError(f"Failed to download binary: {e}")
        except Exception as e:
            raise ContextLiteError(f"Unexpected error during download: {e}")
            
    def _find_in_path(self) -> Optional[Path]:
        """Find binary in system PATH."""
        binary_path = shutil.which(self.BINARY_NAME)
        return Path(binary_path) if binary_path else None
        
    def _find_in_system_locations(self) -> Optional[Path]:
        """Find binary in common system installation locations."""
        if platform.system() == "Windows":
            locations = [
                Path(os.environ.get("PROGRAMFILES", "C:\\Program Files")) / "ContextLite" / self.BINARY_NAME,
                Path(os.environ.get("PROGRAMFILES(X86)", "C:\\Program Files (x86)")) / "ContextLite" / self.BINARY_NAME,
                Path(os.environ.get("LOCALAPPDATA", "")) / "Programs" / "ContextLite" / self.BINARY_NAME,
            ]
        elif platform.system() == "Darwin":  # macOS
            locations = [
                Path("/usr/local/bin") / self.BINARY_NAME,
                Path("/opt/homebrew/bin") / self.BINARY_NAME,
                Path("/Applications/ContextLite.app/Contents/MacOS") / self.BINARY_NAME,
                Path.home() / "Applications" / "ContextLite.app" / "Contents" / "MacOS" / self.BINARY_NAME,
            ]
        else:  # Linux and other Unix-like
            locations = [
                Path("/usr/local/bin") / self.BINARY_NAME,
                Path("/usr/bin") / self.BINARY_NAME,
                Path("/opt/contextlite") / self.BINARY_NAME,
                Path.home() / ".local" / "bin" / self.BINARY_NAME,
            ]
            
        for location in locations:
            if location.exists() and location.is_file():
                return location
                
        return None
        
    def _find_in_package_data(self) -> Optional[Path]:
        """Find binary in Python package data directory."""
        # This would be used if we bundle the binary with the Python package
        package_dir = Path(__file__).parent
        binary_path = package_dir / "bin" / self.BINARY_NAME
        
        return binary_path if binary_path.exists() else None
        
    def _find_in_user_data(self) -> Optional[Path]:
        """Find binary in user data directory."""
        user_binary = self._get_user_binary_path()
        return user_binary if user_binary.exists() else None
        
    def _get_user_binary_path(self) -> Path:
        """Get the path where user-specific binary should be stored."""
        data_dir = Path(user_data_dir("contextlite", "ContextLite"))
        return data_dir / "bin" / self.BINARY_NAME
        
    def _detect_platform(self) -> str:
        """Detect the current platform."""
        system = platform.system().lower()
        if system == "darwin":
            return "darwin"
        elif system == "windows":
            return "windows"
        else:
            return "linux"
            
    def _detect_architecture(self) -> str:
        """Detect the current architecture."""
        machine = platform.machine().lower()
        if machine in ("x86_64", "amd64"):
            return "amd64"
        elif machine in ("aarch64", "arm64"):
            return "arm64"
        elif machine.startswith("arm"):
            return "arm64"  # Assume arm64 for ARM
        else:
            return "amd64"  # Default fallback
            
    def _get_download_url(self, version: str) -> str:
        """
        Get download URL for the specified version and platform.
        
        Args:
            version: Version to download
            
        Returns:
            Download URL
        """
        if version == "latest":
            # Get latest release (including prereleases) from GitHub API
            api_url = f"https://api.github.com/repos/{self.GITHUB_REPO}/releases"
            response = requests.get(api_url)
            response.raise_for_status()
            releases = response.json()
            if not releases:
                raise ContextLiteError("No releases found")
            # Get the first release (most recent)
            version = releases[0]["tag_name"].lstrip("v")
            
        # Construct binary filename based on platform and architecture
        # Use the actual naming convention from our releases
        if self.platform == "windows":
            filename = f"contextlite-{version}-windows-{self.arch}.zip"
        else:
            filename = f"contextlite-{version}-{self.platform}-{self.arch}.tar.gz"
            
        return f"https://github.com/{self.GITHUB_REPO}/releases/download/v{version}/{filename}"
