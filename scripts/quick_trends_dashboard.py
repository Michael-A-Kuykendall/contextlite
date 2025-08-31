#!/usr/bin/env python3
"""
ContextLite Quick Trends Dashboard
Fast visual trends analysis using only reliable APIs (no PyPI lockups)

This is the "safe" version that won't hang your system.
"""

import requests
import json
import os
import sys
from datetime import datetime, timedelta
from typing import Dict, List, Any, Tuple

try:
    import matplotlib.pyplot as plt
    import matplotlib.dates as mdates
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False

class QuickTrendsCollector:
    def __init__(self):
        self.github_token = os.getenv('GITHUB_TOKEN')
        self.headers = {
            'Authorization': f'token {self.github_token}',
            'Accept': 'application/vnd.github.v3+json',
            'User-Agent': 'ContextLite-Quick-Trends'
        } if self.github_token else {}
        
        self.repo = "Michael-A-Kuykendall/contextlite"
    
    def get_npm_trends_fast(self, days: int = 30) -> List[Dict[str, Any]]:
        """Get npm download trends quickly"""
        try:
            end_date = datetime.now()
            start_date = end_date - timedelta(days=days)
            
            url = f"https://api.npmjs.org/downloads/range/{start_date.strftime('%Y-%m-%d')}:{end_date.strftime('%Y-%m-%d')}/contextlite"
            response = requests.get(url, timeout=10)
            
            if response.status_code == 200:
                data = response.json()
                return data.get('downloads', [])
            else:
                return []
        except Exception as e:
            print(f"   ⚠️  npm error: {e}")
            return []
    
    def get_project_age(self) -> Tuple[datetime, int]:
        """Get project age from GitHub"""
        try:
            repo_url = f"https://api.github.com/repos/{self.repo}"
            response = requests.get(repo_url, headers=self.headers, timeout=10)
            if response.status_code == 200:
                repo_data = response.json()
                created_date = datetime.fromisoformat(repo_data['created_at'].replace('Z', '+00:00'))
                days_active = (datetime.now() - created_date.replace(tzinfo=None)).days
                return created_date.replace(tzinfo=None), days_active
        except:
            pass
        
        return datetime.now() - timedelta(days=14), 14
    
    def analyze_quick_trends(self) -> Dict[str, Any]:
        """Quick trends analysis"""
        print("⚡ QUICK TRENDS ANALYSIS")
        print("="*50)
        
        start_date, days_active = self.get_project_age()
        print(f"📅 Project age: {days_active} days (started {start_date.strftime('%Y-%m-%d')})")
        
        npm_data = self.get_npm_trends_fast(min(days_active + 5, 30))
        print(f"📦 npm data: {len(npm_data)} days")
        
        return {
            'npm': npm_data,
            'project_start': start_date,
            'days_active': days_active
        }

def create_quick_chart(trends_data: Dict[str, Any]):
    """Create a quick visual chart"""
    try:
        import matplotlib.pyplot as plt
        import matplotlib.dates as mdates
        matplotlib_available = True
    except ImportError:
        print("📊 Installing matplotlib for charts...")
        try:
            import subprocess
            subprocess.run([sys.executable, '-m', 'pip', 'install', 'matplotlib'], 
                         check=True, timeout=60)
            import matplotlib.pyplot as plt
            import matplotlib.dates as mdates
            matplotlib_available = True
        except Exception as e:
            print(f"⚠️  Could not install matplotlib: {e}")
            matplotlib_available = False
    
    if not matplotlib_available:
        create_text_chart(trends_data)
        return
    
    npm_data = trends_data.get('npm', [])
    if not npm_data:
        print("❌ No data to chart")
        return
    
    # Create chart
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 8))
    fig.suptitle('ContextLite Download Trends (Quick Analysis)', fontsize=14, fontweight='bold')
    
    # Daily downloads
    dates = [datetime.strptime(item['day'], '%Y-%m-%d') for item in npm_data]
    downloads = [item['downloads'] for item in npm_data]
    
    ax1.plot(dates, downloads, color='#CB3837', linewidth=2, marker='o', markersize=4)
    ax1.set_title('npm Daily Downloads', fontweight='bold')
    ax1.set_ylabel('Downloads')
    ax1.grid(True, alpha=0.3)
    
    # Calculate trend
    if len(downloads) > 7:
        recent_avg = sum(downloads[-7:]) / 7
        earlier_avg = sum(downloads[-14:-7]) / 7 if len(downloads) > 14 else downloads[0]
        trend_pct = ((recent_avg - earlier_avg) / earlier_avg) * 100 if earlier_avg > 0 else 0
        
        if trend_pct > 10:
            trend_text = f"↗️ UP {trend_pct:+.1f}%"
            color = 'green'
        elif trend_pct < -10:
            trend_text = f"↘️ DOWN {trend_pct:+.1f}%"
            color = 'red'
        else:
            trend_text = f"➡️ STABLE {trend_pct:+.1f}%"
            color = 'blue'
        
        ax1.text(0.02, 0.98, trend_text, transform=ax1.transAxes, 
                verticalalignment='top', fontweight='bold', color=color,
                bbox=dict(boxstyle="round,pad=0.3", facecolor="white", alpha=0.8))
    
    # 7-day moving average
    if len(downloads) >= 7:
        moving_avg = []
        for i in range(len(downloads)):
            start_idx = max(0, i-6)
            avg = sum(downloads[start_idx:i+1]) / (i - start_idx + 1)
            moving_avg.append(avg)
        
        ax2.plot(dates, moving_avg, color='#CB3837', linewidth=3, label='7-day average')
        ax2.fill_between(dates, moving_avg, alpha=0.3, color='#CB3837')
        ax2.set_title('Download Trend (7-day moving average)', fontweight='bold')
        ax2.set_ylabel('Average Downloads')
        ax2.grid(True, alpha=0.3)
        ax2.legend()
    
    # Format dates
    for ax in [ax1, ax2]:
        ax.xaxis.set_major_formatter(mdates.DateFormatter('%m/%d'))
        ax.xaxis.set_major_locator(mdates.DayLocator(interval=max(1, len(dates)//10)))
        plt.setp(ax.xaxis.get_majorticklabels(), rotation=45)
    
    plt.tight_layout()
    
    # Save chart
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    filename = f"quick_trends_{timestamp}.png"
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"📊 Chart saved: {filename}")
    
    try:
        plt.show()
    except:
        print("💡 Chart saved to file")

def create_text_chart(trends_data: Dict[str, Any]):
    """Text-based chart for when matplotlib isn't available"""
    npm_data = trends_data.get('npm', [])
    if not npm_data:
        print("❌ No data available")
        return
    
    print("\n📊 DOWNLOAD TRENDS (Last 2 weeks)")
    print("="*60)
    
    recent_data = npm_data[-14:] if len(npm_data) > 14 else npm_data
    max_downloads = max(item['downloads'] for item in recent_data) if recent_data else 1
    
    for item in recent_data:
        downloads = item['downloads']
        bar_length = int((downloads / max_downloads) * 40)
        bar = "█" * bar_length + "░" * (40 - bar_length)
        day_name = datetime.strptime(item['day'], '%Y-%m-%d').strftime('%a')
        print(f"{item['day']} ({day_name}): {bar} {downloads:4d}")
    
    # Calculate and show trend
    if len(npm_data) > 7:
        recent = [item['downloads'] for item in npm_data[-7:]]
        earlier = [item['downloads'] for item in npm_data[-14:-7]] if len(npm_data) > 14 else [npm_data[0]['downloads']]
        
        recent_avg = sum(recent) / len(recent)
        earlier_avg = sum(earlier) / len(earlier)
        trend_pct = ((recent_avg - earlier_avg) / earlier_avg) * 100 if earlier_avg > 0 else 0
        
        print("\n🎯 TREND ANALYSIS:")
        print(f"   Recent week average: {recent_avg:.1f} downloads/day")
        print(f"   Previous week average: {earlier_avg:.1f} downloads/day")
        
        if trend_pct > 10:
            print(f"   📈 TRENDING UP: {trend_pct:+.1f}% improvement!")
        elif trend_pct < -10:
            print(f"   📉 TRENDING DOWN: {trend_pct:+.1f}% decline")
        else:
            print(f"   ➡️  STABLE: {trend_pct:+.1f}% change")
    
    # Project insights
    days_active = trends_data.get('days_active', 0)
    total_downloads = sum(item['downloads'] for item in npm_data)
    
    print(f"\n📊 PROJECT SUMMARY:")
    print(f"   Days active: {days_active}")
    print(f"   Total npm downloads: {total_downloads:,}")
    print(f"   Average per day: {total_downloads/days_active:.1f}" if days_active > 0 else "   Average: N/A")
    
    if days_active < 30:
        print("   🚀 Early stage - focus on building user base")
    elif total_downloads > 1000:
        print("   🎉 Good traction - optimize for growth")
    else:
        print("   📈 Building momentum - monitor trends closely")

def main():
    print("⚡ CONTEXTLITE QUICK TRENDS DASHBOARD")
    print("="*60)
    print("Fast analysis without risky API calls")
    print()
    
    collector = QuickTrendsCollector()
    trends_data = collector.analyze_quick_trends()
    
    print("\n📊 CREATING VISUAL ANALYSIS...")
    create_quick_chart(trends_data)
    
    print("\n📈 TEXT SUMMARY:")
    create_text_chart(trends_data)

if __name__ == "__main__":
    main()
