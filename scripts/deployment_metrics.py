#!/usr/bin/env python3
"""
ContextLite Deployment Metrics Dashboard
Comprehensive monitoring of all deployment targets with download tracking and conversion analytics

This tool handles the reality of a complex deployment ecosystem with multiple workflows,
legacy scripts, and GoReleaser attempts. It provides unified metrics regardless of how
packages were deployed.

Usage:
    python deployment_metrics.py              # Full dashboard
    python deployment_metrics.py --platform npm  # Specific platform
    python deployment_metrics.py --trends     # Weekly/daily trends
    python deployment_metrics.py --conversions # Trial conversion estimates
"""

import requests
import json
import os
import sys
import time
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional
from dataclasses import dataclass
import argparse

@dataclass
class PlatformMetrics:
    platform: str
    current_version: str
    downloads_total: int
    downloads_weekly: int
    downloads_daily: int
    last_updated: str
    status: str  # "live", "outdated", "missing", "error"
    url: str
    notes: str = ""

@dataclass
class ConversionMetrics:
    total_downloads: int
    estimated_active_trials: int
    trial_conversion_rate: float  # percentage
    estimated_sales: int
    projected_monthly_revenue: float

class DeploymentMetricsMonitor:
    def __init__(self):
        self.github_token = os.getenv('GITHUB_TOKEN')
        if not self.github_token:
            print("⚠️  GITHUB_TOKEN not set - some features will be limited")
        
        self.repo = "Michael-A-Kuykendall/contextlite"
        self.headers = {
            'Authorization': f'token {self.github_token}',
            'Accept': 'application/vnd.github.v3+json',
            'User-Agent': 'ContextLite-Metrics-Monitor'
        } if self.github_token else {}
        
        # Store metrics for trend analysis
        self.metrics_history_file = "deployment_metrics_history.json"
        
    def get_github_releases_metrics(self) -> PlatformMetrics:
        """Get GitHub Releases download statistics"""
        try:
            url = f"https://api.github.com/repos/{self.repo}/releases"
            response = requests.get(url, headers=self.headers)
            response.raise_for_status()
            
            releases = response.json()
            if not releases:
                return PlatformMetrics("GitHub Releases", "none", 0, 0, 0, "never", "missing", url)
            
            latest = releases[0]
            total_downloads = sum(asset['download_count'] for asset in latest['assets'])
            
            return PlatformMetrics(
                platform="GitHub Releases",
                current_version=latest['tag_name'],
                downloads_total=total_downloads,
                downloads_weekly=0,  # GitHub doesn't provide time-based breakdowns
                downloads_daily=0,
                last_updated=latest['published_at'][:10],
                status="live",
                url=latest['html_url'],
                notes=f"{len(latest['assets'])} assets"
            )
        except Exception as e:
            return PlatformMetrics("GitHub Releases", "error", 0, 0, 0, "error", "error", 
                                 "https://github.com/Michael-A-Kuykendall/contextlite/releases", str(e))

    def get_npm_metrics(self) -> PlatformMetrics:
        """Get npm package statistics"""
        try:
            # Get package info
            pkg_url = "https://registry.npmjs.org/contextlite"
            response = requests.get(pkg_url)
            response.raise_for_status()
            data = response.json()
            
            current_version = data['dist-tags']['latest']
            last_updated = data['time'][current_version][:10]
            
            # Get download statistics
            downloads_url = "https://api.npmjs.org/downloads/range/last-week/contextlite"
            dl_response = requests.get(downloads_url)
            dl_response.raise_for_status()
            dl_data = dl_response.json()
            
            weekly_downloads = dl_data['downloads'][-1]['downloads'] if dl_data['downloads'] else 0
            
            # Get total downloads (approximate from last 30 days * estimation)
            total_url = "https://api.npmjs.org/downloads/range/last-month/contextlite"
            total_response = requests.get(total_url)
            monthly_downloads = 0
            if total_response.status_code == 200:
                monthly_data = total_response.json()
                monthly_downloads = sum(day['downloads'] for day in monthly_data['downloads'])
            
            return PlatformMetrics(
                platform="npm",
                current_version=current_version,
                downloads_total=monthly_downloads * 6,  # Rough estimate
                downloads_weekly=weekly_downloads,
                downloads_daily=weekly_downloads // 7,
                last_updated=last_updated,
                status="live",
                url=f"https://www.npmjs.com/package/contextlite",
                notes=f"Weekly: {weekly_downloads}, Monthly: {monthly_downloads}"
            )
        except Exception as e:
            return PlatformMetrics("npm", "error", 0, 0, 0, "error", "error", 
                                 "https://www.npmjs.com/package/contextlite", str(e))

    def get_pypi_metrics(self) -> PlatformMetrics:
        """Get PyPI package statistics"""
        try:
            # Get package info
            pkg_url = "https://pypi.org/pypi/contextlite/json"
            response = requests.get(pkg_url)
            response.raise_for_status()
            data = response.json()
            
            current_version = data['info']['version']
            last_updated = data['releases'][current_version][0]['upload_time'][:10]
            
            # PyPI doesn't provide download stats in the API anymore
            # We'll need to estimate or use external services
            
            return PlatformMetrics(
                platform="PyPI",
                current_version=current_version,
                downloads_total=0,  # Not available via API
                downloads_weekly=0,
                downloads_daily=0,
                last_updated=last_updated,
                status="live",
                url=f"https://pypi.org/project/contextlite/",
                notes="Download stats not available via API"
            )
        except Exception as e:
            return PlatformMetrics("PyPI", "error", 0, 0, 0, "error", "error", 
                                 "https://pypi.org/project/contextlite/", str(e))

    def get_docker_metrics(self) -> PlatformMetrics:
        """Get Docker Hub statistics"""
        try:
            # Check multiple possible Docker repositories
            repos_to_check = [
                "contextlite/contextlite",
                "makuykendall/contextlite", 
                "michaelakuykendall/contextlite"
            ]
            
            for repo in repos_to_check:
                try:
                    url = f"https://hub.docker.com/v2/repositories/{repo}"
                    response = requests.get(url)
                    if response.status_code == 200:
                        data = response.json()
                        
                        # Get tags to find latest version
                        tags_url = f"https://hub.docker.com/v2/repositories/{repo}/tags"
                        tags_response = requests.get(tags_url)
                        latest_tag = "latest"
                        if tags_response.status_code == 200:
                            tags_data = tags_response.json()
                            if tags_data['results']:
                                latest_tag = tags_data['results'][0]['name']
                        
                        return PlatformMetrics(
                            platform="Docker Hub",
                            current_version=latest_tag,
                            downloads_total=data.get('pull_count', 0),
                            downloads_weekly=0,  # Not provided by Docker Hub API
                            downloads_daily=0,
                            last_updated=data.get('last_updated', '')[:10],
                            status="live",
                            url=f"https://hub.docker.com/r/{repo}",
                            notes=f"Repository: {repo}, Stars: {data.get('star_count', 0)}"
                        )
                except:
                    continue
            
            return PlatformMetrics("Docker Hub", "none", 0, 0, 0, "never", "missing", 
                                 "https://hub.docker.com/search?q=contextlite", "No repositories found")
        except Exception as e:
            return PlatformMetrics("Docker Hub", "error", 0, 0, 0, "error", "error", 
                                 "https://hub.docker.com", str(e))

    def get_chocolatey_metrics(self) -> PlatformMetrics:
        """Get Chocolatey package statistics"""
        try:
            # Chocolatey API is more restrictive, try web scraping approach
            url = "https://community.chocolatey.org/api/v2/Packages?$filter=Id%20eq%20%27contextlite%27"
            response = requests.get(url)
            
            if "contextlite" in response.text.lower():
                # Package exists, try to extract version info
                # This is basic parsing - Chocolatey API is complex
                return PlatformMetrics(
                    platform="Chocolatey",
                    current_version="detected",
                    downloads_total=0,  # Not easily accessible
                    downloads_weekly=0,
                    downloads_daily=0,
                    last_updated="unknown",
                    status="live",
                    url="https://community.chocolatey.org/packages/contextlite",
                    notes="Package exists, detailed metrics not accessible"
                )
            else:
                return PlatformMetrics("Chocolatey", "none", 0, 0, 0, "never", "missing", 
                                     "https://community.chocolatey.org/packages/contextlite", "Package not found")
        except Exception as e:
            return PlatformMetrics("Chocolatey", "error", 0, 0, 0, "error", "error", 
                                 "https://community.chocolatey.org/packages/contextlite", str(e))

    def get_crates_metrics(self) -> PlatformMetrics:
        """Get Crates.io statistics"""
        try:
            url = "https://crates.io/api/v1/crates/contextlite"
            response = requests.get(url)
            response.raise_for_status()
            data = response.json()
            
            crate_info = data['crate']
            return PlatformMetrics(
                platform="Crates.io",
                current_version=crate_info['newest_version'],
                downloads_total=crate_info['downloads'],
                downloads_weekly=crate_info.get('recent_downloads', 0),
                downloads_daily=crate_info.get('recent_downloads', 0) // 7,
                last_updated=crate_info['updated_at'][:10],
                status="live",
                url=f"https://crates.io/crates/contextlite",
                notes=f"Total downloads: {crate_info['downloads']}"
            )
        except Exception as e:
            return PlatformMetrics("Crates.io", "error", 0, 0, 0, "error", "error", 
                                 "https://crates.io/crates/contextlite", str(e))

    def get_homebrew_metrics(self) -> PlatformMetrics:
        """Check Homebrew formula status"""
        try:
            # Check official Homebrew
            url = "https://formulae.brew.sh/api/formula/contextlite.json"
            response = requests.get(url)
            
            if response.status_code == 200:
                data = response.json()
                return PlatformMetrics(
                    platform="Homebrew",
                    current_version=data['versions']['stable'],
                    downloads_total=0,  # Homebrew doesn't provide download stats
                    downloads_weekly=0,
                    downloads_daily=0,
                    last_updated="unknown",
                    status="live",
                    url=f"https://formulae.brew.sh/formula/contextlite",
                    notes="Official Homebrew formula"
                )
            else:
                # Check custom tap
                tap_url = f"https://api.github.com/repos/{self.repo.split('/')[0]}/homebrew-contextlite"
                tap_response = requests.get(tap_url, headers=self.headers)
                
                if tap_response.status_code == 200:
                    return PlatformMetrics(
                        platform="Homebrew",
                        current_version="custom-tap",
                        downloads_total=0,
                        downloads_weekly=0,
                        downloads_daily=0,
                        last_updated="unknown",
                        status="live",
                        url=f"https://github.com/{self.repo.split('/')[0]}/homebrew-contextlite",
                        notes="Custom tap repository"
                    )
                else:
                    return PlatformMetrics("Homebrew", "none", 0, 0, 0, "never", "missing", 
                                         "https://formulae.brew.sh", "No formula found")
        except Exception as e:
            return PlatformMetrics("Homebrew", "error", 0, 0, 0, "error", "error", 
                                 "https://formulae.brew.sh", str(e))

    def get_vscode_metrics(self) -> PlatformMetrics:
        """Get VS Code Marketplace statistics"""
        try:
            # VS Code Marketplace API is complex, try basic check
            publisher = "MikeKuykendall"  # Adjust as needed
            extension = "contextlite"
            
            url = f"https://marketplace.visualstudio.com/items?itemName={publisher}.{extension}"
            response = requests.get(url)
            
            if response.status_code == 200 and "not found" not in response.text.lower():
                return PlatformMetrics(
                    platform="VS Code Marketplace",
                    current_version="detected",
                    downloads_total=0,  # Would need to parse HTML or use different API
                    downloads_weekly=0,
                    downloads_daily=0,
                    last_updated="unknown",
                    status="live",
                    url=url,
                    notes="Extension exists, metrics not easily accessible"
                )
            else:
                return PlatformMetrics("VS Code Marketplace", "none", 0, 0, 0, "never", "missing", 
                                     f"https://marketplace.visualstudio.com/search?term=contextlite", "Extension not found")
        except Exception as e:
            return PlatformMetrics("VS Code Marketplace", "error", 0, 0, 0, "error", "error", 
                                 "https://marketplace.visualstudio.com", str(e))

    def get_all_metrics(self) -> List[PlatformMetrics]:
        """Get metrics from all platforms"""
        print("🔍 Gathering metrics from all deployment targets...")
        
        platforms = [
            self.get_github_releases_metrics,
            self.get_npm_metrics,
            self.get_pypi_metrics,
            self.get_docker_metrics,
            self.get_chocolatey_metrics,
            self.get_crates_metrics,
            self.get_homebrew_metrics,
            self.get_vscode_metrics,
        ]
        
        metrics = []
        for i, platform_func in enumerate(platforms, 1):
            print(f"  📊 {i}/{len(platforms)} - {platform_func.__name__.replace('get_', '').replace('_metrics', '')}", end="... ")
            try:
                metric = platform_func()
                metrics.append(metric)
                print(f"✅ {metric.status}")
            except Exception as e:
                print(f"❌ Error: {e}")
                
        return metrics

    def calculate_conversion_metrics(self, total_downloads: int) -> ConversionMetrics:
        """Calculate trial conversion estimates based on download data"""
        # Assumptions based on typical SaaS metrics
        trial_activation_rate = 0.70  # 70% of downloads actually try the software
        trial_completion_rate = 0.85  # 85% complete the 14-day trial
        conversion_rate_range = (0.15, 0.25)  # 15-25% convert after trial
        
        estimated_active_trials = int(total_downloads * trial_activation_rate)
        avg_conversion_rate = sum(conversion_rate_range) / 2
        estimated_sales = int(estimated_active_trials * trial_completion_rate * avg_conversion_rate)
        
        # Revenue projections (assuming $99 Professional license)
        license_price = 99
        projected_monthly_revenue = estimated_sales * license_price
        
        return ConversionMetrics(
            total_downloads=total_downloads,
            estimated_active_trials=estimated_active_trials,
            trial_conversion_rate=avg_conversion_rate * 100,
            estimated_sales=estimated_sales,
            projected_monthly_revenue=projected_monthly_revenue
        )

    def save_metrics_history(self, metrics: List[PlatformMetrics]):
        """Save current metrics for trend analysis"""
        history_entry = {
            'timestamp': datetime.now().isoformat(),
            'metrics': [
                {
                    'platform': m.platform,
                    'version': m.current_version,
                    'downloads_total': m.downloads_total,
                    'downloads_weekly': m.downloads_weekly,
                    'status': m.status
                }
                for m in metrics
            ]
        }
        
        # Load existing history
        history = []
        if os.path.exists(self.metrics_history_file):
            try:
                with open(self.metrics_history_file, 'r') as f:
                    history = json.load(f)
            except:
                history = []
        
        # Add new entry
        history.append(history_entry)
        
        # Keep only last 30 days
        cutoff = datetime.now() - timedelta(days=30)
        history = [h for h in history if datetime.fromisoformat(h['timestamp']) > cutoff]
        
        # Save updated history
        with open(self.metrics_history_file, 'w') as f:
            json.dump(history, f, indent=2)

    def print_dashboard(self, metrics: List[PlatformMetrics]):
        """Print comprehensive dashboard"""
        print("\n" + "="*80)
        print("🚀 CONTEXTLITE DEPLOYMENT METRICS DASHBOARD")
        print(f"📅 Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print("="*80)
        
        # Status summary
        live_count = len([m for m in metrics if m.status == "live"])
        missing_count = len([m for m in metrics if m.status == "missing"])
        error_count = len([m for m in metrics if m.status == "error"])
        
        print(f"\n📊 PLATFORM STATUS SUMMARY")
        print(f"   ✅ Live: {live_count}/{len(metrics)} platforms")
        print(f"   ❌ Missing: {missing_count} platforms")
        print(f"   🔥 Errors: {error_count} platforms")
        
        # Detailed platform metrics
        print(f"\n📋 DETAILED PLATFORM METRICS")
        print(f"{'Platform':<20} {'Version':<12} {'Downloads':<12} {'Weekly':<8} {'Status':<10} {'Updated':<12}")
        print("-" * 80)
        
        total_downloads = 0
        for metric in sorted(metrics, key=lambda x: x.downloads_total, reverse=True):
            status_icon = {
                "live": "✅",
                "missing": "❌", 
                "error": "🔥",
                "outdated": "⚠️"
            }.get(metric.status, "❓")
            
            downloads_str = f"{metric.downloads_total:,}" if metric.downloads_total > 0 else "-"
            weekly_str = f"{metric.downloads_weekly:,}" if metric.downloads_weekly > 0 else "-"
            
            print(f"{metric.platform:<20} {metric.current_version:<12} {downloads_str:<12} {weekly_str:<8} {status_icon} {metric.status:<9} {metric.last_updated:<12}")
            
            if metric.notes:
                print(f"{'  └─':<20} {metric.notes}")
            
            if metric.downloads_total > 0:
                total_downloads += metric.downloads_total
        
        # Conversion analysis
        if total_downloads > 0:
            print(f"\n💰 CONVERSION ANALYSIS")
            conversions = self.calculate_conversion_metrics(total_downloads)
            
            print(f"   📊 Total Downloads: {conversions.total_downloads:,}")
            print(f"   🎯 Estimated Active Trials: {conversions.estimated_active_trials:,}")
            print(f"   💎 Projected Conversion Rate: {conversions.trial_conversion_rate:.1f}%")
            print(f"   💵 Estimated Sales: {conversions.estimated_sales:,}")
            print(f"   🏦 Projected Monthly Revenue: ${conversions.projected_monthly_revenue:,.2f}")
            
            print(f"\n📈 BUSINESS INSIGHTS")
            if conversions.estimated_sales == 0:
                print("   ⚠️  No conversions detected yet - still in early adoption phase")
                print("   💡 Focus on increasing download rates and trial activation")
            else:
                print(f"   🎉 Revenue potential identified: ${conversions.projected_monthly_revenue:,.2f}/month")
                print("   💡 Consider marketing optimization and conversion funnel improvements")
        else:
            print(f"\n⚠️  No download data available - deployment metrics limited")
        
        print(f"\n🔗 QUICK LINKS")
        for metric in metrics:
            if metric.status == "live":
                print(f"   {metric.platform}: {metric.url}")
        
        print("="*80)

    def run_dashboard(self, platform_filter: Optional[str] = None):
        """Run the complete metrics dashboard"""
        metrics = self.get_all_metrics()
        
        if platform_filter:
            metrics = [m for m in metrics if platform_filter.lower() in m.platform.lower()]
            
        self.save_metrics_history(metrics)
        self.print_dashboard(metrics)
        
        return metrics

def main():
    parser = argparse.ArgumentParser(description="ContextLite Deployment Metrics Dashboard")
    parser.add_argument('--platform', help='Filter by specific platform (e.g., npm, pypi)')
    parser.add_argument('--trends', action='store_true', help='Show trend analysis')
    parser.add_argument('--conversions', action='store_true', help='Focus on conversion metrics')
    parser.add_argument('--json', action='store_true', help='Output as JSON')
    
    args = parser.parse_args()
    
    monitor = DeploymentMetricsMonitor()
    
    if args.trends:
        print("📈 Trend analysis feature coming soon...")
        return
    
    if args.conversions:
        print("💰 Conversion-focused analysis feature coming soon...")
        return
    
    try:
        metrics = monitor.run_dashboard(args.platform)
        
        if args.json:
            json_output = {
                'timestamp': datetime.now().isoformat(),
                'platforms': [
                    {
                        'platform': m.platform,
                        'version': m.current_version,
                        'downloads_total': m.downloads_total,
                        'downloads_weekly': m.downloads_weekly,
                        'status': m.status,
                        'url': m.url,
                        'notes': m.notes
                    }
                    for m in metrics
                ]
            }
            print(json.dumps(json_output, indent=2))
            
    except KeyboardInterrupt:
        print("\n⚠️  Monitoring interrupted by user")
    except Exception as e:
        print(f"❌ Error running dashboard: {e}")
        return 1
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
