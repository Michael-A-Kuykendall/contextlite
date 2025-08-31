#!/usr/bin/env python3
"""
ContextLite Master Deployment Dashboard
Unified view of deployment metrics, workflow health, and business analytics

This is your one-stop dashboard for understanding how ContextLite is performing
across all deployment channels, regardless of the chaotic deployment ecosystem.
"""

import os
import sys
import json
import subprocess
from datetime import datetime
from typing import Dict, List, Any

# Add scripts directory to path so we can import our modules
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

try:
    from deployment_metrics import DeploymentMetricsMonitor
    from workflow_health_monitor import WorkflowHealthMonitor
    from pypi_stats_collector import PyPIStatsCollector
except ImportError as e:
    print(f"❌ Import error: {e}")
    print("Make sure all script files are in the same directory")
    sys.exit(1)

class MasterDashboard:
    def __init__(self):
        self.metrics_monitor = DeploymentMetricsMonitor()
        
        # Check if GitHub token is available
        if os.getenv('GITHUB_TOKEN'):
            self.workflow_monitor = WorkflowHealthMonitor()
        else:
            self.workflow_monitor = None
            
        self.pypi_collector = PyPIStatsCollector()
        
    def run_complete_analysis(self, save_report: bool = True) -> Dict[str, Any]:
        """Run complete analysis across all systems"""
        report = {
            'timestamp': datetime.now().isoformat(),
            'deployment_metrics': None,
            'workflow_health': None,
            'pypi_stats': None,
            'business_insights': {},
            'executive_summary': {}
        }
        
        print("🚀 CONTEXTLITE MASTER DEPLOYMENT ANALYSIS")
        print("="*80)
        print("🔍 Running comprehensive analysis across all deployment channels...")
        print()
        
        # 1. Deployment Metrics
        print("📊 1/3 - GATHERING DEPLOYMENT METRICS")
        try:
            metrics = self.metrics_monitor.get_all_metrics()
            report['deployment_metrics'] = {
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
        except Exception as e:
            print(f"   ❌ Error: {e}")
            report['deployment_metrics'] = {'error': str(e)}
        
        # 2. Workflow Health
        print("\n🏥 2/3 - ANALYZING WORKFLOW HEALTH")
        if self.workflow_monitor:
            try:
                workflow_analysis = self.workflow_monitor.analyze_deployment_patterns()
                report['workflow_health'] = workflow_analysis
            except Exception as e:
                print(f"   ❌ Error: {e}")
                report['workflow_health'] = {'error': str(e)}
        else:
            print("   ⚠️  Skipped - GITHUB_TOKEN not available")
            report['workflow_health'] = {'error': 'GITHUB_TOKEN not set'}
        
        # 3. PyPI Detailed Stats
        print("\n🐍 3/3 - COLLECTING PYPI ANALYTICS")
        try:
            # This will be captured in the output
            report['pypi_stats'] = {'status': 'attempted'}
        except Exception as e:
            print(f"   ❌ Error: {e}")
            report['pypi_stats'] = {'error': str(e)}
        
        # Generate business insights
        report['business_insights'] = self.generate_business_insights(report)
        report['executive_summary'] = self.generate_executive_summary(report)
        
        # Save report
        if save_report:
            self.save_master_report(report)
        
        return report
    
    def generate_business_insights(self, report: Dict[str, Any]) -> Dict[str, Any]:
        """Generate business-focused insights from technical data"""
        insights = {
            'deployment_coverage': 'unknown',
            'download_trends': 'insufficient_data',
            'conversion_potential': 'unknown',
            'platform_performance': {},
            'critical_issues': [],
            'opportunities': []
        }
        
        # Analyze deployment coverage
        if report['deployment_metrics'] and 'platforms' in report['deployment_metrics']:
            platforms = report['deployment_metrics']['platforms']
            live_platforms = [p for p in platforms if p['status'] == 'live']
            total_platforms = len(platforms)
            
            coverage_rate = len(live_platforms) / total_platforms if total_platforms > 0 else 0
            
            if coverage_rate >= 0.8:
                insights['deployment_coverage'] = 'excellent'
            elif coverage_rate >= 0.6:
                insights['deployment_coverage'] = 'good'
            elif coverage_rate >= 0.4:
                insights['deployment_coverage'] = 'fair'
            else:
                insights['deployment_coverage'] = 'poor'
            
            # Analyze platform performance
            for platform in platforms:
                if platform['downloads_total'] > 0:
                    if platform['downloads_total'] > 1000:
                        performance = 'high'
                    elif platform['downloads_total'] > 100:
                        performance = 'medium'
                    else:
                        performance = 'low'
                    
                    insights['platform_performance'][platform['platform']] = {
                        'performance': performance,
                        'downloads': platform['downloads_total']
                    }
            
            # Identify critical issues
            missing_platforms = [p['platform'] for p in platforms if p['status'] == 'missing']
            error_platforms = [p['platform'] for p in platforms if p['status'] == 'error']
            
            if missing_platforms:
                insights['critical_issues'].append(f"Missing deployments: {', '.join(missing_platforms)}")
            if error_platforms:
                insights['critical_issues'].append(f"Deployment errors: {', '.join(error_platforms)}")
        
        # Analyze workflow health
        if report['workflow_health'] and 'overall_health' in report['workflow_health']:
            health = report['workflow_health']['overall_health']
            if health.get('average_success_rate', 0) < 70:
                insights['critical_issues'].append("Low workflow success rate - deployment instability")
        
        # Generate opportunities
        if insights['deployment_coverage'] == 'poor':
            insights['opportunities'].append("Improve deployment coverage to increase distribution reach")
        
        if not insights['platform_performance']:
            insights['opportunities'].append("Focus on increasing download rates across all platforms")
        else:
            low_performing = [p for p, data in insights['platform_performance'].items() 
                            if data['performance'] == 'low']
            if low_performing:
                insights['opportunities'].append(f"Optimize marketing for low-performing platforms: {', '.join(low_performing)}")
        
        return insights
    
    def generate_executive_summary(self, report: Dict[str, Any]) -> Dict[str, Any]:
        """Generate executive-level summary for business decisions"""
        summary = {
            'overall_status': 'unknown',
            'key_metrics': {},
            'priority_actions': [],
            'business_readiness': 'unknown'
        }
        
        # Calculate key metrics
        if report['deployment_metrics'] and 'platforms' in report['deployment_metrics']:
            platforms = report['deployment_metrics']['platforms']
            live_count = len([p for p in platforms if p['status'] == 'live'])
            total_downloads = sum(p['downloads_total'] for p in platforms if p['downloads_total'] > 0)
            
            summary['key_metrics'] = {
                'live_platforms': live_count,
                'total_platforms': len(platforms),
                'total_downloads': total_downloads,
                'deployment_coverage': f"{(live_count/len(platforms)*100):.1f}%" if platforms else "0%"
            }
            
            # Determine overall status
            if live_count >= 6 and total_downloads > 500:
                summary['overall_status'] = 'production_ready'
                summary['business_readiness'] = 'ready_for_scale'
            elif live_count >= 4 and total_downloads > 100:
                summary['overall_status'] = 'stable'
                summary['business_readiness'] = 'early_production'
            elif live_count >= 2:
                summary['overall_status'] = 'developing'
                summary['business_readiness'] = 'beta'
            else:
                summary['overall_status'] = 'early_stage'
                summary['business_readiness'] = 'alpha'
        
        # Generate priority actions
        business_insights = report.get('business_insights', {})
        
        if business_insights.get('deployment_coverage') == 'poor':
            summary['priority_actions'].append("URGENT: Fix deployment failures to improve market reach")
        
        if business_insights.get('critical_issues'):
            summary['priority_actions'].append("CRITICAL: Address deployment infrastructure issues")
        
        if summary['key_metrics'].get('total_downloads', 0) == 0:
            summary['priority_actions'].append("FOCUS: Implement download tracking across all platforms")
        
        if not summary['priority_actions']:
            summary['priority_actions'].append("OPTIMIZE: Focus on conversion rate improvement and marketing")
        
        return summary
    
    def save_master_report(self, report: Dict[str, Any]):
        """Save master report to file"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        filename = f"master_deployment_report_{timestamp}.json"
        
        with open(filename, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"\n💾 Master report saved: {filename}")
    
    def print_executive_dashboard(self, report: Dict[str, Any]):
        """Print executive-level dashboard"""
        print("\n" + "="*80)
        print("📈 CONTEXTLITE EXECUTIVE DEPLOYMENT DASHBOARD")
        print(f"📅 {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print("="*80)
        
        # Executive Summary
        exec_summary = report.get('executive_summary', {})
        print(f"\n🎯 EXECUTIVE SUMMARY")
        print(f"   Overall Status: {exec_summary.get('overall_status', 'unknown').replace('_', ' ').title()}")
        print(f"   Business Readiness: {exec_summary.get('business_readiness', 'unknown').replace('_', ' ').title()}")
        
        # Key Metrics
        key_metrics = exec_summary.get('key_metrics', {})
        if key_metrics:
            print(f"\n📊 KEY METRICS")
            print(f"   Active Platforms: {key_metrics.get('live_platforms', 0)}/{key_metrics.get('total_platforms', 0)}")
            print(f"   Deployment Coverage: {key_metrics.get('deployment_coverage', '0%')}")
            print(f"   Total Downloads: {key_metrics.get('total_downloads', 0):,}")
        
        # Business Insights
        business_insights = report.get('business_insights', {})
        if business_insights.get('platform_performance'):
            print(f"\n🏆 TOP PERFORMING PLATFORMS")
            perf = business_insights['platform_performance']
            sorted_platforms = sorted(perf.items(), key=lambda x: x[1]['downloads'], reverse=True)
            for platform, data in sorted_platforms[:5]:
                print(f"   {platform}: {data['downloads']:,} downloads ({data['performance']} performance)")
        
        # Critical Issues
        critical_issues = business_insights.get('critical_issues', [])
        if critical_issues:
            print(f"\n🚨 CRITICAL ISSUES")
            for i, issue in enumerate(critical_issues, 1):
                print(f"   {i}. {issue}")
        
        # Priority Actions
        priority_actions = exec_summary.get('priority_actions', [])
        if priority_actions:
            print(f"\n⚡ PRIORITY ACTIONS")
            for i, action in enumerate(priority_actions, 1):
                print(f"   {i}. {action}")
        
        # Opportunities
        opportunities = business_insights.get('opportunities', [])
        if opportunities:
            print(f"\n💡 GROWTH OPPORTUNITIES")
            for i, opportunity in enumerate(opportunities, 1):
                print(f"   {i}. {opportunity}")
        
        print("\n" + "="*80)
    
    def run_dashboard(self, mode: str = 'full'):
        """Run dashboard in different modes"""
        if mode == 'executive':
            # Quick executive summary
            report = self.run_complete_analysis(save_report=False)
            self.print_executive_dashboard(report)
        elif mode == 'metrics':
            # Just deployment metrics
            print("📊 DEPLOYMENT METRICS ONLY")
            self.metrics_monitor.run_dashboard()
        elif mode == 'health':
            # Just workflow health
            if self.workflow_monitor:
                print("🏥 WORKFLOW HEALTH ONLY")
                self.workflow_monitor.monitor_deployment_health()
            else:
                print("❌ Workflow health monitoring requires GITHUB_TOKEN")
        elif mode == 'pypi':
            # Just PyPI stats
            print("🐍 PYPI STATS ONLY")
            self.pypi_collector.run()
        else:
            # Full analysis
            report = self.run_complete_analysis()
            self.print_executive_dashboard(report)
            
            print("\n🔗 DETAILED REPORTS")
            print("   • Run with --mode metrics for detailed platform metrics")
            print("   • Run with --mode health for workflow health analysis")
            print("   • Run with --mode pypi for detailed PyPI analytics")

def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="ContextLite Master Deployment Dashboard")
    parser.add_argument('--mode', choices=['full', 'executive', 'metrics', 'health', 'pypi'], 
                       default='executive', help='Dashboard mode')
    
    args = parser.parse_args()
    
    try:
        dashboard = MasterDashboard()
        dashboard.run_dashboard(args.mode)
    except KeyboardInterrupt:
        print("\n⚠️  Dashboard interrupted by user")
    except Exception as e:
        print(f"❌ Error running dashboard: {e}")
        return 1
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
