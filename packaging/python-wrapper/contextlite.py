"""
ContextLite Python Wrapper
A lightweight wrapper around the ContextLite binary for semantic context search.
"""

import os
import sys
import subprocess
import platform
import urllib.request
import zipfile
import tarfile
import tempfile
import shutil
from pathlib import Path
import json
import requests


class ContextLiteError(Exception):
    """Base exception for ContextLite errors."""
    pass


class ContextLite:
    """Python wrapper for ContextLite binary."""
    
    def __init__(self, binary_path=None, auto_download=True):
        """
        Initialize ContextLite wrapper.
        
        Args:
            binary_path: Path to contextlite binary. If None, will search for it.
            auto_download: If True, will automatically download binary if not found.
        """
        self.binary_path = binary_path or self._find_binary()
        
        if not self.binary_path and auto_download:
            self.binary_path = self._download_binary()
        
        if not self.binary_path:
            raise ContextLiteError("ContextLite binary not found and auto_download=False")
    
    def _find_binary(self):
        """Find contextlite binary in common locations."""
        binary_name = "contextlite.exe" if platform.system() == "Windows" else "contextlite"
        
        # Check PATH
        if shutil.which(binary_name):
            return shutil.which(binary_name)
        
        # Check common installation locations
        possible_paths = [
            Path.home() / ".local" / "bin" / binary_name,
            Path.home() / ".contextlite" / binary_name,
            Path("/usr/local/bin") / binary_name,
            Path("/usr/bin") / binary_name,
        ]
        
        if platform.system() == "Windows":
            possible_paths.extend([
                Path.home() / ".contextlite" / "contextlite.exe",
                Path("C:/Program Files/ContextLite/contextlite.exe"),
            ])
        
        for path in possible_paths:
            if path.exists() and path.is_file():
                return str(path)
        
        return None
    
    def _download_binary(self):
        """Download contextlite binary from GitHub releases."""
        try:
            # Get latest release info
            api_url = "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases/latest"
            response = requests.get(api_url)
            response.raise_for_status()
            release_data = response.json()
            
            # Determine platform-specific asset
            system = platform.system().lower()
            arch = platform.machine().lower()
            
            # Map Python arch names to Go arch names
            arch_map = {
                'x86_64': 'amd64',
                'amd64': 'amd64',
                'aarch64': 'arm64',
                'arm64': 'arm64',
            }
            go_arch = arch_map.get(arch, 'amd64')
            
            # Find matching asset
            asset_name = None
            download_url = None
            
            for asset in release_data['assets']:
                name = asset['name']
                if system in name and go_arch in name:
                    if system == 'windows' and name.endswith('.zip'):
                        asset_name = name
                        download_url = asset['browser_download_url']
                        break
                    elif system in ['linux', 'darwin'] and name.endswith('.tar.gz'):
                        asset_name = name
                        download_url = asset['browser_download_url']
                        break
            
            if not download_url:
                raise ContextLiteError(f"No binary found for {system}/{go_arch}")
            
            # Download and extract
            install_dir = Path.home() / ".contextlite"
            install_dir.mkdir(exist_ok=True)
            
            binary_name = "contextlite.exe" if system == "windows" else "contextlite"
            binary_path = install_dir / binary_name
            
            print(f"Downloading ContextLite {release_data['tag_name']}...")
            
            with tempfile.TemporaryDirectory() as temp_dir:
                temp_file = Path(temp_dir) / asset_name
                
                urllib.request.urlretrieve(download_url, temp_file)
                
                # Extract archive
                if asset_name.endswith('.zip'):
                    with zipfile.ZipFile(temp_file, 'r') as zip_file:
                        zip_file.extractall(temp_dir)
                elif asset_name.endswith('.tar.gz'):
                    with tarfile.open(temp_file, 'r:gz') as tar_file:
                        tar_file.extractall(temp_dir)
                
                # Find and copy binary
                for file_path in Path(temp_dir).rglob(binary_name):
                    shutil.copy2(file_path, binary_path)
                    binary_path.chmod(0o755)  # Make executable
                    break
                else:
                    raise ContextLiteError(f"Binary {binary_name} not found in archive")
            
            print(f"ContextLite installed to {binary_path}")
            return str(binary_path)
            
        except Exception as e:
            raise ContextLiteError(f"Failed to download ContextLite binary: {e}")
    
    def _run_command(self, args, check=True):
        """Run contextlite command with given arguments."""
        cmd = [self.binary_path] + args
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                check=check
            )
            return result
        except subprocess.CalledProcessError as e:
            raise ContextLiteError(f"Command failed: {e.stderr}")
        except FileNotFoundError:
            raise ContextLiteError(f"Binary not found: {self.binary_path}")
    
    def version(self):
        """Get ContextLite version."""
        result = self._run_command(["--version"])
        return result.stdout.strip()
    
    def add_document(self, content, doc_id=None, metadata=None):
        """
        Add a document to the context database.
        
        Args:
            content: Document content as string
            doc_id: Optional document ID
            metadata: Optional metadata dict
        """
        args = ["add"]
        if doc_id:
            args.extend(["--id", doc_id])
        if metadata:
            args.extend(["--metadata", json.dumps(metadata)])
        args.append(content)
        
        result = self._run_command(args)
        return result.stdout.strip()
    
    def query(self, query_text, max_results=10, no_cache=False):
        """
        Query the context database.
        
        Args:
            query_text: Query string
            max_results: Maximum number of results
            no_cache: If True, bypass cache
            
        Returns:
            Query results as dict
        """
        args = ["query", "--format", "json"]
        if max_results != 10:
            args.extend(["--max-results", str(max_results)])
        if no_cache:
            args.append("--no-cache")
        args.append(query_text)
        
        result = self._run_command(args)
        try:
            return json.loads(result.stdout)
        except json.JSONDecodeError as e:
            raise ContextLiteError(f"Failed to parse JSON response: {e}")
    
    def index_directory(self, directory, recursive=True):
        """
        Index all files in a directory.
        
        Args:
            directory: Directory path to index
            recursive: If True, index recursively
        """
        args = ["index"]
        if recursive:
            args.append("--recursive")
        args.append(str(directory))
        
        result = self._run_command(args)
        return result.stdout.strip()
    
    def stats(self):
        """Get database statistics."""
        result = self._run_command(["stats", "--format", "json"])
        try:
            return json.loads(result.stdout)
        except json.JSONDecodeError as e:
            raise ContextLiteError(f"Failed to parse JSON response: {e}")
    
    def clear_cache(self):
        """Clear the query cache."""
        result = self._run_command(["cache", "clear"])
        return result.stdout.strip()


# Convenience functions for quick usage
def query(query_text, **kwargs):
    """Quick query function."""
    client = ContextLite()
    return client.query(query_text, **kwargs)


def add_document(content, **kwargs):
    """Quick add document function."""
    client = ContextLite()
    return client.add_document(content, **kwargs)


def index_directory(directory, **kwargs):
    """Quick index directory function."""
    client = ContextLite()
    return client.index_directory(directory, **kwargs)


if __name__ == "__main__":
    # CLI interface
    import argparse
    
    parser = argparse.ArgumentParser(description="ContextLite Python Wrapper")
    parser.add_argument("--version", action="store_true", help="Show version")
    parser.add_argument("--download", action="store_true", help="Download binary")
    
    args = parser.parse_args()
    
    if args.version:
        try:
            client = ContextLite()
            print(client.version())
        except ContextLiteError as e:
            print(f"Error: {e}", file=sys.stderr)
            sys.exit(1)
    elif args.download:
        try:
            client = ContextLite(auto_download=True)
            print("ContextLite binary downloaded successfully")
        except ContextLiteError as e:
            print(f"Error: {e}", file=sys.stderr)
            sys.exit(1)
    else:
        parser.print_help()
