#!/usr/bin/env python3
"""
ContextLite Download Tracker
Aggregates download statistics from all distribution channels
"""

import requests
import json
import sys
from datetime import datetime, timedelta
from typing import Dict, List, Any

class DownloadTracker:
    def __init__(self):
        self.stats = {
            'github_releases': 0,
            'npm': 0,
            'pypi': 0,
            'crates_io': 0,
            'docker_hub': 0,
            'chocolatey': 0,
            'vscode_marketplace': 0,
            'total': 0,
            'last_updated': datetime.now().isoformat()
        }
    
    def get_github_releases_downloads(self) -> int:
        """Get total downloads from GitHub releases"""
        try:
            url = "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases"
            response = requests.get(url, timeout=10)
            response.raise_for_status()
            
            total = 0
            releases = response.json()
            
            for release in releases:
                for asset in release.get('assets', []):
                    total += asset.get('download_count', 0)
            
            print(f"✅ GitHub Releases: {total:,} downloads")
            return total
            
        except Exception as e:
            print(f"❌ GitHub Releases: Error - {e}")
            return 0
    
    def get_npm_downloads(self) -> int:
        """Get total downloads from npm"""
        try:
            # Get last 30 days of npm downloads
            url = "https://api.npmjs.org/downloads/point/last-month/contextlite"
            response = requests.get(url, timeout=10)
            
            if response.status_code == 404:
                print("ℹ️  npm: Package not yet published")
                return 0
                
            response.raise_for_status()
            data = response.json()
            downloads = data.get('downloads', 0)
            
            print(f"✅ npm (last 30 days): {downloads:,} downloads")
            return downloads
            
        except Exception as e:
            print(f"❌ npm: Error - {e}")
            return 0
    
    def get_pypi_downloads(self) -> int:
        """Get total downloads from PyPI"""
        try:
            # PyPI doesn't provide public download stats API anymore
            # This would require pypistats or BigQuery access
            print("ℹ️  PyPI: Download stats require pypistats package")
            return 0
            
        except Exception as e:
            print(f"❌ PyPI: Error - {e}")
            return 0
    
    def get_crates_io_downloads(self) -> int:
        """Get total downloads from crates.io"""
        try:
            url = "https://crates.io/api/v1/crates/contextlite-client"
            response = requests.get(url, timeout=10)
            
            if response.status_code == 404:
                print("ℹ️  Crates.io: Package not yet published")
                return 0
                
            response.raise_for_status()
            data = response.json()
            downloads = data.get('crate', {}).get('downloads', 0)
            
            print(f"✅ Crates.io: {downloads:,} downloads")
            return downloads
            
        except Exception as e:
            print(f"❌ Crates.io: Error - {e}")
            return 0
    
    def get_docker_hub_downloads(self) -> int:
        """Get total pulls from Docker Hub"""
        try:
            url = "https://hub.docker.com/v2/repositories/michaelkuykendall/contextlite/"
            response = requests.get(url, timeout=10)
            
            if response.status_code == 404:
                print("ℹ️  Docker Hub: Repository not yet published")
                return 0
                
            response.raise_for_status()
            data = response.json()
            pulls = data.get('pull_count', 0)
            
            print(f"✅ Docker Hub: {pulls:,} pulls")
            return pulls
            
        except Exception as e:
            print(f"❌ Docker Hub: Error - {e}")
            return 0
    
    def get_chocolatey_downloads(self) -> int:
        """Get total downloads from Chocolatey"""
        try:
            # Chocolatey API requires parsing from web page or special access
            print("ℹ️  Chocolatey: Download stats require web scraping")
            return 0
            
        except Exception as e:
            print(f"❌ Chocolatey: Error - {e}")
            return 0
    
    def get_vscode_downloads(self) -> int:
        """Get total installs from VS Code Marketplace"""
        try:
            # VS Code Marketplace API requires special access
            print("ℹ️  VS Code Marketplace: Install stats require publisher access")
            return 0
            
        except Exception as e:
            print(f"❌ VS Code Marketplace: Error - {e}")
            return 0
    
    def collect_all_stats(self) -> Dict[str, Any]:
        """Collect download statistics from all channels"""
        print("🔍 Collecting download statistics from all channels...\n")
        
        self.stats['github_releases'] = self.get_github_releases_downloads()
        self.stats['npm'] = self.get_npm_downloads()
        self.stats['pypi'] = self.get_pypi_downloads()
        self.stats['crates_io'] = self.get_crates_io_downloads()
        self.stats['docker_hub'] = self.get_docker_hub_downloads()
        self.stats['chocolatey'] = self.get_chocolatey_downloads()
        self.stats['vscode_marketplace'] = self.get_vscode_downloads()
        
        # Calculate total (excluding platforms without stats)
        self.stats['total'] = (
            self.stats['github_releases'] + 
            self.stats['npm'] + 
            self.stats['crates_io'] + 
            self.stats['docker_hub']
        )
        
        return self.stats
    
    def print_summary(self):
        """Print a formatted summary of all download statistics"""
        print("\n" + "="*60)
        print("📊 CONTEXTLITE DOWNLOAD STATISTICS SUMMARY")
        print("="*60)
        
        print(f"GitHub Releases:     {self.stats['github_releases']:>10,}")
        print(f"npm (30 days):       {self.stats['npm']:>10,}")
        print(f"PyPI:                {self.stats['pypi']:>10,} (manual check required)")
        print(f"Crates.io:           {self.stats['crates_io']:>10,}")
        print(f"Docker Hub:          {self.stats['docker_hub']:>10,}")
        print(f"Chocolatey:          {self.stats['chocolatey']:>10,} (manual check required)")
        print(f"VS Code Marketplace: {self.stats['vscode_marketplace']:>10,} (manual check required)")
        print("-" * 60)
        print(f"TOTAL (trackable):   {self.stats['total']:>10,}")
        print(f"Last Updated:        {self.stats['last_updated']}")
        print("="*60)
    
    def save_to_file(self, filename: str = "download_stats.json"):
        """Save statistics to JSON file"""
        with open(filename, 'w') as f:
            json.dump(self.stats, f, indent=2)
        print(f"\n💾 Statistics saved to {filename}")

def main():
    """Main function to run download tracking"""
    tracker = DownloadTracker()
    stats = tracker.collect_all_stats()
    tracker.print_summary()
    tracker.save_to_file()
    
    return stats['total']

if __name__ == "__main__":
    total_downloads = main()
    sys.exit(0 if total_downloads >= 0 else 1)
