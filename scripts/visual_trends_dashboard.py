#!/usr/bin/env python3
"""
ContextLite Visual Trends Dashboard
Creates graphs showing download trends across all platforms over time

This tool gathers time-series data from all available sources and creates
visual charts to show if downloads are trending up or down.
"""

import requests
import json
import os
import sys
from datetime import datetime, timedelta
from typing import Dict, List, Any, Tuple
import subprocess

try:
    import matplotlib.pyplot as plt
    import matplotlib.dates as mdates
    from matplotlib.ticker import MaxNLocator
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False

try:
    import pandas as pd
    PANDAS_AVAILABLE = True
except ImportError:
    PANDAS_AVAILABLE = False

class TrendsDataCollector:
    def __init__(self):
        self.github_token = os.getenv('GITHUB_TOKEN')
        self.headers = {
            'Authorization': f'token {self.github_token}',
            'Accept': 'application/vnd.github.v3+json',
            'User-Agent': 'ContextLite-Trends-Monitor'
        } if self.github_token else {}
        
        self.repo = "Michael-A-Kuykendall/contextlite"
    
    def get_npm_download_trends(self, days: int = 365) -> List[Dict[str, Any]]:
        """Get npm download trends over time"""
        try:
            end_date = datetime.now()
            start_date = end_date - timedelta(days=days)
            
            # Get daily downloads for the period
            url = f"https://api.npmjs.org/downloads/range/{start_date.strftime('%Y-%m-%d')}:{end_date.strftime('%Y-%m-%d')}/contextlite"
            response = requests.get(url)
            
            if response.status_code == 200:
                data = response.json()
                return data.get('downloads', [])
            else:
                print(f"   ⚠️  npm API returned {response.status_code}")
                return []
        except Exception as e:
            print(f"   ❌ npm trends error: {e}")
            return []
    
    def get_pypi_download_trends(self, days: int = 90) -> List[Dict[str, Any]]:
        """Get PyPI download trends using pypistats"""
        try:
            end_date = datetime.now()
            start_date = end_date - timedelta(days=days)
            
            # Check if pypistats is available - try multiple possible locations
            pypistats_paths = [
                'pypistats',
                'py -m pypistats',
                sys.executable + ' -m pypistats'
            ]
            
            working_cmd = None
            for cmd_base in pypistats_paths:
                try:
                    test_cmd = cmd_base.split() + ['--help']
                    result = subprocess.run(test_cmd, capture_output=True, check=True, timeout=10)
                    working_cmd = cmd_base
                    break
                except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
                    continue
            
            if not working_cmd:
                print("   ⚠️  pypistats not accessible, installing...")
                subprocess.run([sys.executable, '-m', 'pip', 'install', 'pypistats'], check=True, timeout=60)
                working_cmd = sys.executable + ' -m pypistats'
            
            # Get PyPI download data with timeout
            cmd = working_cmd.split() + [
                'recent', 'contextlite',
                '--start-date', start_date.strftime('%Y-%m-%d'),
                '--end-date', end_date.strftime('%Y-%m-%d'),
                '--format', 'json'
            ]
            
            result = subprocess.run(cmd, capture_output=True, text=True, check=True, timeout=30)
            data = json.loads(result.stdout)
            
            # Convert to consistent format
            trends = []
            for item in data.get('data', []):
                trends.append({
                    'day': item['date'],
                    'downloads': item['downloads']
                })
            
            return sorted(trends, key=lambda x: x['day'])
            
        except subprocess.TimeoutExpired:
            print(f"   ⚠️  PyPI request timed out - skipping detailed stats")
            return []
        except Exception as e:
            print(f"   ⚠️  PyPI trends limited: {str(e)[:50]}...")
            return []
    
    def get_github_releases_history(self) -> List[Dict[str, Any]]:
        """Get GitHub releases timeline to estimate distribution start"""
        try:
            url = f"https://api.github.com/repos/{self.repo}/releases"
            response = requests.get(url, headers=self.headers)
            response.raise_for_status()
            
            releases = response.json()
            
            # Process releases to show cumulative downloads over time
            timeline = []
            for release in reversed(releases):  # Oldest first
                total_downloads = sum(asset['download_count'] for asset in release['assets'])
                timeline.append({
                    'day': release['published_at'][:10],
                    'downloads': total_downloads,
                    'version': release['tag_name'],
                    'cumulative': True  # These are cumulative, not daily
                })
            
            return timeline
            
        except Exception as e:
            print(f"   ❌ GitHub releases history error: {e}")
            return []
    
    def get_crates_download_history(self) -> List[Dict[str, Any]]:
        """Get Crates.io download history"""
        try:
            # Crates.io doesn't provide historical data via API
            # But we can get current stats and estimate timeline
            url = "https://crates.io/api/v1/crates/contextlite"
            response = requests.get(url)
            
            if response.status_code == 200:
                data = response.json()
                crate_info = data['crate']
                
                # Get versions to estimate timeline
                versions_url = f"https://crates.io/api/v1/crates/contextlite/versions"
                versions_response = requests.get(versions_url)
                
                if versions_response.status_code == 200:
                    versions_data = versions_response.json()
                    timeline = []
                    
                    for version in versions_data['versions']:
                        timeline.append({
                            'day': version['created_at'][:10],
                            'downloads': version.get('downloads', 0),
                            'version': version['num'],
                            'cumulative': False
                        })
                    
                    return sorted(timeline, key=lambda x: x['day'])
                
            return []
            
        except Exception as e:
            print(f"   ❌ Crates.io history error: {e}")
            return []
    
    def estimate_project_timeline(self) -> Tuple[datetime, int]:
        """Estimate when the project started based on available data"""
        earliest_dates = []
        
        # Check GitHub repo creation
        try:
            repo_url = f"https://api.github.com/repos/{self.repo}"
            response = requests.get(repo_url, headers=self.headers)
            if response.status_code == 200:
                repo_data = response.json()
                created_date = datetime.fromisoformat(repo_data['created_at'].replace('Z', '+00:00'))
                earliest_dates.append(created_date)
        except:
            pass
        
        # Check first release
        try:
            releases_url = f"https://api.github.com/repos/{self.repo}/releases"
            response = requests.get(releases_url, headers=self.headers)
            if response.status_code == 200:
                releases = response.json()
                if releases:
                    first_release = min(releases, key=lambda x: x['published_at'])
                    release_date = datetime.fromisoformat(first_release['published_at'].replace('Z', '+00:00'))
                    earliest_dates.append(release_date)
        except:
            pass
        
        if earliest_dates:
            start_date = min(earliest_dates)
            days_active = (datetime.now() - start_date.replace(tzinfo=None)).days
            return start_date.replace(tzinfo=None), days_active
        else:
            # Fallback estimate
            return datetime.now() - timedelta(days=90), 90
    
    def collect_all_trends(self) -> Dict[str, Any]:
        """Collect trends data from all available sources"""
        print("📈 COLLECTING DOWNLOAD TRENDS DATA")
        print("="*60)
        
        trends_data = {
            'npm': [],
            'pypi': [],
            'github_releases': [],
            'crates': [],
            'project_start': None,
            'days_active': 0
        }
        
        # Get project timeline
        start_date, days_active = self.estimate_project_timeline()
        trends_data['project_start'] = start_date
        trends_data['days_active'] = days_active
        
        print(f"📅 Project Timeline:")
        print(f"   Started: {start_date.strftime('%Y-%m-%d')}")
        print(f"   Days Active: {days_active}")
        print()
        
        # Collect npm data
        print("📦 Collecting npm download trends...")
        npm_data = self.get_npm_download_trends(min(days_active + 30, 365))
        trends_data['npm'] = npm_data
        print(f"   Found {len(npm_data)} days of npm data")
        
        # Collect PyPI data
        print("🐍 Collecting PyPI download trends...")
        pypi_data = self.get_pypi_download_trends(min(days_active + 30, 90))
        trends_data['pypi'] = pypi_data
        print(f"   Found {len(pypi_data)} days of PyPI data")
        
        # Collect GitHub releases data
        print("📋 Collecting GitHub releases history...")
        github_data = self.get_github_releases_history()
        trends_data['github_releases'] = github_data
        print(f"   Found {len(github_data)} GitHub releases")
        
        # Collect Crates data
        print("🦀 Collecting Crates.io history...")
        crates_data = self.get_crates_download_history()
        trends_data['crates'] = crates_data
        print(f"   Found {len(crates_data)} Crates releases")
        
        return trends_data

class TrendsVisualizer:
    def __init__(self):
        self.colors = {
            'npm': '#CB3837',
            'pypi': '#3776AB', 
            'github_releases': '#24292E',
            'crates': '#000000'
        }
    
    def install_dependencies(self):
        """Install required visualization libraries"""
        print("📦 Installing visualization dependencies...")
        try:
            subprocess.run([sys.executable, '-m', 'pip', 'install', 'matplotlib', 'pandas'], check=True)
            print("✅ Dependencies installed successfully")
            return True
        except subprocess.CalledProcessError:
            print("❌ Failed to install dependencies")
            return False
    
    def create_trends_charts(self, trends_data: Dict[str, Any]):
        """Create visual charts of download trends"""
        if not MATPLOTLIB_AVAILABLE:
            print("⚠️  matplotlib not available, installing...")
            if not self.install_dependencies():
                self.create_text_charts(trends_data)
                return
        
        # Re-import after potential installation
        try:
            import matplotlib.pyplot as plt
            import matplotlib.dates as mdates
            from matplotlib.ticker import MaxNLocator
        except ImportError:
            self.create_text_charts(trends_data)
            return
        
        # Create figure with subplots
        fig, axes = plt.subplots(2, 2, figsize=(15, 10))
        fig.suptitle('ContextLite Download Trends Analysis', fontsize=16, fontweight='bold')
        
        # Configure plot style
        plt.style.use('default')
        
        # Plot npm trends
        if trends_data['npm']:
            ax = axes[0, 0]
            npm_data = trends_data['npm']
            dates = [datetime.strptime(item['day'], '%Y-%m-%d') for item in npm_data]
            downloads = [item['downloads'] for item in npm_data]
            
            ax.plot(dates, downloads, color=self.colors['npm'], linewidth=2, marker='o', markersize=3)
            ax.set_title('npm Daily Downloads', fontweight='bold')
            ax.set_ylabel('Downloads per Day')
            ax.grid(True, alpha=0.3)
            
            # Format dates
            ax.xaxis.set_major_formatter(mdates.DateFormatter('%m/%d'))
            ax.xaxis.set_major_locator(mdates.WeekdayLocator(interval=2))
            plt.setp(ax.xaxis.get_majorticklabels(), rotation=45)
            
            # Add trend indicator
            if len(downloads) > 7:
                recent_avg = sum(downloads[-7:]) / 7
                earlier_avg = sum(downloads[-14:-7]) / 7 if len(downloads) > 14 else downloads[0]
                trend = "↗️" if recent_avg > earlier_avg else "↘️"
                ax.text(0.02, 0.98, f"Trend: {trend}", transform=ax.transAxes, 
                       verticalalignment='top', fontweight='bold')
        
        # Plot PyPI trends
        if trends_data['pypi']:
            ax = axes[0, 1]
            pypi_data = trends_data['pypi']
            dates = [datetime.strptime(item['day'], '%Y-%m-%d') for item in pypi_data]
            downloads = [item['downloads'] for item in pypi_data]
            
            ax.plot(dates, downloads, color=self.colors['pypi'], linewidth=2, marker='s', markersize=3)
            ax.set_title('PyPI Daily Downloads', fontweight='bold')
            ax.set_ylabel('Downloads per Day')
            ax.grid(True, alpha=0.3)
            
            ax.xaxis.set_major_formatter(mdates.DateFormatter('%m/%d'))
            ax.xaxis.set_major_locator(mdates.WeekdayLocator(interval=2))
            plt.setp(ax.xaxis.get_majorticklabels(), rotation=45)
            
            # Add trend indicator
            if len(downloads) > 7:
                recent_avg = sum(downloads[-7:]) / 7
                earlier_avg = sum(downloads[-14:-7]) / 7 if len(downloads) > 14 else downloads[0]
                trend = "↗️" if recent_avg > earlier_avg else "↘️"
                ax.text(0.02, 0.98, f"Trend: {trend}", transform=ax.transAxes, 
                       verticalalignment='top', fontweight='bold')
        
        # Plot GitHub releases timeline
        if trends_data['github_releases']:
            ax = axes[1, 0]
            github_data = trends_data['github_releases']
            dates = [datetime.strptime(item['day'], '%Y-%m-%d') for item in github_data]
            downloads = [item['downloads'] for item in github_data]
            
            ax.bar(dates, downloads, color=self.colors['github_releases'], alpha=0.7, width=3)
            ax.set_title('GitHub Releases Downloads', fontweight='bold')
            ax.set_ylabel('Total Downloads per Release')
            ax.grid(True, alpha=0.3)
            
            ax.xaxis.set_major_formatter(mdates.DateFormatter('%m/%d'))
            plt.setp(ax.xaxis.get_majorticklabels(), rotation=45)
        
        # Plot combined overview
        ax = axes[1, 1]
        
        # Show recent npm trend with moving average
        if trends_data['npm']:
            npm_data = trends_data['npm']
            if len(npm_data) > 7:
                recent_data = npm_data[-21:]  # Last 3 weeks
                dates = [datetime.strptime(item['day'], '%Y-%m-%d') for item in recent_data]
                downloads = [item['downloads'] for item in recent_data]
                
                # Calculate 3-day moving average
                moving_avg = []
                for i in range(len(downloads)):
                    start_idx = max(0, i-2)
                    avg = sum(downloads[start_idx:i+1]) / (i - start_idx + 1)
                    moving_avg.append(avg)
                
                ax.plot(dates, downloads, color=self.colors['npm'], alpha=0.3, label='npm daily')
                ax.plot(dates, moving_avg, color=self.colors['npm'], linewidth=2, label='npm trend')
                
                # Add trend arrow
                if len(moving_avg) > 7:
                    recent_trend = sum(moving_avg[-3:]) / 3
                    earlier_trend = sum(moving_avg[-7:-4]) / 3
                    if recent_trend > earlier_trend:
                        trend_text = "↗️ Trending Up"
                    elif recent_trend < earlier_trend * 0.8:
                        trend_text = "↘️ Trending Down"  
                    else:
                        trend_text = "➡️ Stable"
                    
                    ax.text(0.02, 0.98, trend_text, transform=ax.transAxes, 
                           verticalalignment='top', fontweight='bold')
        else:
            # If no npm data, show project timeline
            start_date = trends_data.get('project_start')
            days_active = trends_data.get('days_active', 0)
            if start_date:
                ax.text(0.5, 0.5, f'Project started:\n{start_date.strftime("%Y-%m-%d")}\n\n{days_active} days active', 
                       transform=ax.transAxes, ha='center', va='center', 
                       fontsize=12, bbox=dict(boxstyle="round,pad=0.5", facecolor="lightblue"))
        
        ax.set_title('Recent Trend Analysis', fontweight='bold')
        ax.set_ylabel('Downloads per Day')
        ax.legend()
        ax.grid(True, alpha=0.3)
        if trends_data['npm']:
            ax.xaxis.set_major_formatter(mdates.DateFormatter('%m/%d'))
            plt.setp(ax.xaxis.get_majorticklabels(), rotation=45)
        
        # Adjust layout and save
        plt.tight_layout()
        
        # Save the chart
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        filename = f"contextlite_trends_{timestamp}.png"
        plt.savefig(filename, dpi=150, bbox_inches='tight')
        print(f"📊 Trends chart saved: {filename}")
        
        # Try to display
        try:
            plt.show()
        except:
            print("💡 Chart saved to file (display not available in this environment)")
    
    def create_text_charts(self, trends_data: Dict[str, Any]):
        """Create text-based charts when matplotlib isn't available"""
        print("\n📊 TEXT-BASED TRENDS ANALYSIS")
        print("="*60)
        
        # npm trends
        if trends_data['npm']:
            print("\n📦 NPM DOWNLOAD TRENDS (Last 30 days)")
            npm_data = trends_data['npm'][-30:]  # Last 30 days
            
            max_downloads = max(item['downloads'] for item in npm_data)
            for item in npm_data[-10:]:  # Show last 10 days
                downloads = item['downloads']
                bar_length = int((downloads / max_downloads) * 50)
                bar = "█" * bar_length + "░" * (50 - bar_length)
                print(f"   {item['day']}: {bar} {downloads:4d}")
            
            # Calculate trend
            recent = [item['downloads'] for item in npm_data[-7:]]
            earlier = [item['downloads'] for item in npm_data[-14:-7]] if len(npm_data) > 14 else [npm_data[0]['downloads']]
            
            recent_avg = sum(recent) / len(recent)
            earlier_avg = sum(earlier) / len(earlier)
            trend_pct = ((recent_avg - earlier_avg) / earlier_avg) * 100 if earlier_avg > 0 else 0
            
            trend_indicator = "↗️ UP" if trend_pct > 5 else "↘️ DOWN" if trend_pct < -5 else "➡️ STABLE"
            print(f"   Trend: {trend_indicator} ({trend_pct:+.1f}%)")
        
        # PyPI trends
        if trends_data['pypi']:
            print("\n🐍 PYPI DOWNLOAD TRENDS")
            pypi_data = trends_data['pypi'][-30:]  # Last 30 days
            
            if pypi_data:
                max_downloads = max(item['downloads'] for item in pypi_data)
                for item in pypi_data[-10:]:  # Show last 10 days
                    downloads = item['downloads']
                    bar_length = int((downloads / max_downloads) * 50) if max_downloads > 0 else 0
                    bar = "█" * bar_length + "░" * (50 - bar_length)
                    print(f"   {item['day']}: {bar} {downloads:4d}")
        
        # GitHub releases
        if trends_data['github_releases']:
            print("\n📋 GITHUB RELEASES TIMELINE")
            for release in trends_data['github_releases'][-5:]:  # Last 5 releases
                print(f"   {release['day']} - {release['version']}: {release['downloads']} downloads")
        
        # Project summary
        start_date = trends_data.get('project_start')
        days_active = trends_data.get('days_active', 0)
        
        print(f"\n📅 PROJECT TIMELINE SUMMARY")
        print(f"   Started: {start_date.strftime('%Y-%m-%d') if start_date else 'Unknown'}")
        print(f"   Days Active: {days_active}")
        print(f"   Average Age: {days_active // 30} months")

def main():
    print("📈 CONTEXTLITE VISUAL TRENDS DASHBOARD")
    print("="*80)
    
    # Check for matplotlib
    if not MATPLOTLIB_AVAILABLE:
        print("⚠️  matplotlib not installed - will show text charts and install for next time")
    
    # Collect trends data
    collector = TrendsDataCollector()
    trends_data = collector.collect_all_trends()
    
    # Create visualizations
    visualizer = TrendsVisualizer()
    
    print("\n📊 CREATING VISUAL TRENDS ANALYSIS...")
    visualizer.create_trends_charts(trends_data)
    
    # Also show text summary
    visualizer.create_text_charts(trends_data)
    
    print("\n" + "="*80)
    print("🎯 KEY INSIGHTS:")
    
    # Analyze trends
    npm_data = trends_data.get('npm', [])
    if npm_data and len(npm_data) > 14:
        recent_downloads = [item['downloads'] for item in npm_data[-7:]]
        earlier_downloads = [item['downloads'] for item in npm_data[-14:-7]]
        
        recent_avg = sum(recent_downloads) / len(recent_downloads)
        earlier_avg = sum(earlier_downloads) / len(earlier_downloads)
        
        if recent_avg > earlier_avg * 1.1:
            print("✅ npm downloads trending UP - good momentum!")
        elif recent_avg < earlier_avg * 0.9:
            print("⚠️  npm downloads trending DOWN - may need attention")
        else:
            print("➡️ npm downloads stable - consistent performance")
    
    days_active = trends_data.get('days_active', 0)
    if days_active < 30:
        print("🚀 Very early stage - focus on building initial user base")
    elif days_active < 90:
        print("📈 Early growth phase - track metrics closely")
    else:
        print("🏢 Mature project - optimize for conversion and retention")

if __name__ == "__main__":
    main()
