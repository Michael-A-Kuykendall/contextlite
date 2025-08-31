#!/usr/bin/env python3
"""
ContextLite PyPI Stats Collector
Uses pypistats CLI tool to get detailed PyPI download analytics

Installation: pip install pypistats
Usage: python pypi_stats_collector.py
"""

import subprocess
import json
import sys
from datetime import datetime, timedelta

class PyPIStatsCollector:
    def __init__(self, package_name: str = "contextlite"):
        self.package_name = package_name
        
    def check_pypistats_installed(self) -> bool:
        """Check if pypistats CLI is available"""
        try:
            subprocess.run(['pypistats', '--help'], 
                         capture_output=True, check=True)
            return True
        except (subprocess.CalledProcessError, FileNotFoundError):
            return False
    
    def install_pypistats(self):
        """Install pypistats if not available"""
        print("📦 Installing pypistats...")
        try:
            subprocess.run([sys.executable, '-m', 'pip', 'install', 'pypistats'], 
                         check=True)
            print("✅ pypistats installed successfully")
        except subprocess.CalledProcessError as e:
            print(f"❌ Failed to install pypistats: {e}")
            raise
    
    def get_recent_downloads(self, days: int = 30) -> dict:
        """Get recent download statistics"""
        try:
            end_date = datetime.now()
            start_date = end_date - timedelta(days=days)
            
            cmd = [
                'pypistats', 'recent',
                self.package_name,
                '--start-date', start_date.strftime('%Y-%m-%d'),
                '--end-date', end_date.strftime('%Y-%m-%d'),
                '--format', 'json'
            ]
            
            result = subprocess.run(cmd, capture_output=True, text=True, check=True)
            return json.loads(result.stdout)
        except subprocess.CalledProcessError as e:
            print(f"❌ Error getting recent downloads: {e}")
            return {}
    
    def get_overall_stats(self) -> dict:
        """Get overall package statistics"""
        try:
            cmd = ['pypistats', 'overall', self.package_name, '--format', 'json']
            result = subprocess.run(cmd, capture_output=True, text=True, check=True)
            return json.loads(result.stdout)
        except subprocess.CalledProcessError as e:
            print(f"❌ Error getting overall stats: {e}")
            return {}
    
    def get_system_stats(self, days: int = 30) -> dict:
        """Get downloads by operating system"""
        try:
            end_date = datetime.now()
            start_date = end_date - timedelta(days=days)
            
            cmd = [
                'pypistats', 'system',
                self.package_name,
                '--start-date', start_date.strftime('%Y-%m-%d'),
                '--end-date', end_date.strftime('%Y-%m-%d'),
                '--format', 'json'
            ]
            
            result = subprocess.run(cmd, capture_output=True, text=True, check=True)
            return json.loads(result.stdout)
        except subprocess.CalledProcessError as e:
            print(f"❌ Error getting system stats: {e}")
            return {}
    
    def print_pypi_report(self):
        """Generate comprehensive PyPI analytics report"""
        print("🐍 CONTEXTLITE PYPI ANALYTICS REPORT")
        print("="*60)
        
        # Recent downloads
        recent = self.get_recent_downloads(30)
        if recent and 'data' in recent:
            total_month = sum(item['downloads'] for item in recent['data'])
            weekly_avg = total_month / 4.3  # Approximate weeks in month
            daily_avg = total_month / 30
            
            print(f"📊 DOWNLOAD STATISTICS (Last 30 days)")
            print(f"   Total Downloads: {total_month:,}")
            print(f"   Weekly Average: {weekly_avg:,.0f}")
            print(f"   Daily Average: {daily_avg:,.0f}")
        
        # Overall stats
        overall = self.get_overall_stats()
        if overall and 'data' in overall:
            total_all_time = sum(item['downloads'] for item in overall['data'])
            print(f"   All-time Downloads: {total_all_time:,}")
        
        # System breakdown
        system_stats = self.get_system_stats(30)
        if system_stats and 'data' in system_stats:
            print(f"\n💻 DOWNLOADS BY OPERATING SYSTEM")
            systems = {}
            for item in system_stats['data']:
                system = item['system_name']
                systems[system] = systems.get(system, 0) + item['downloads']
            
            for system, downloads in sorted(systems.items(), key=lambda x: x[1], reverse=True):
                if downloads > 0:
                    print(f"   {system}: {downloads:,}")
        
        print("="*60)
    
    def run(self):
        """Main execution method"""
        if not self.check_pypistats_installed():
            print("⚠️  pypistats not found. Installing...")
            self.install_pypistats()
        
        try:
            self.print_pypi_report()
        except Exception as e:
            print(f"❌ Error running PyPI analytics: {e}")
            print("💡 Try installing manually: pip install pypistats")

def main():
    collector = PyPIStatsCollector()
    collector.run()

if __name__ == "__main__":
    main()
