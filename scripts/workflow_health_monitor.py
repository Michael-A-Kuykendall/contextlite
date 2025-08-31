#!/usr/bin/env python3
"""
ContextLite Workflow Health Monitor
Monitors all GitHub Actions workflows and identifies deployment success patterns

This tool is designed to handle a complex deployment ecosystem with multiple
overlapping workflows, legacy scripts, and mixed deployment strategies.
"""

import requests
import json
import os
from datetime import datetime, timedelta
from typing import Dict, List, Any
from collections import defaultdict

class WorkflowHealthMonitor:
    def __init__(self):
        self.github_token = os.getenv('GITHUB_TOKEN')
        if not self.github_token:
            raise ValueError("GITHUB_TOKEN environment variable required")
        
        self.repo = "Michael-A-Kuykendall/contextlite"
        self.headers = {
            'Authorization': f'token {self.github_token}',
            'Accept': 'application/vnd.github.v3+json',
            'User-Agent': 'ContextLite-Workflow-Monitor'
        }
    
    def get_workflows(self) -> List[Dict[str, Any]]:
        """Get all workflows in the repository"""
        url = f"https://api.github.com/repos/{self.repo}/actions/workflows"
        response = requests.get(url, headers=self.headers)
        response.raise_for_status()
        return response.json()['workflows']
    
    def get_workflow_runs(self, workflow_id: int, days_back: int = 7) -> List[Dict[str, Any]]:
        """Get recent runs for a specific workflow"""
        since = (datetime.now() - timedelta(days=days_back)).isoformat()
        url = f"https://api.github.com/repos/{self.repo}/actions/workflows/{workflow_id}/runs"
        params = {'created': f'>{since}', 'per_page': 50}
        
        response = requests.get(url, headers=self.headers, params=params)
        response.raise_for_status()
        return response.json()['workflow_runs']
    
    def get_run_jobs(self, run_id: int) -> List[Dict[str, Any]]:
        """Get jobs for a specific workflow run"""
        url = f"https://api.github.com/repos/{self.repo}/actions/runs/{run_id}/jobs"
        response = requests.get(url, headers=self.headers)
        response.raise_for_status()
        return response.json()['jobs']
    
    def analyze_deployment_patterns(self, days_back: int = 14) -> Dict[str, Any]:
        """Analyze deployment success patterns across all workflows"""
        workflows = self.get_workflows()
        
        # Filter deployment-related workflows
        deployment_workflows = [
            w for w in workflows 
            if any(keyword in w['name'].lower() for keyword in 
                  ['deploy', 'publish', 'release', 'package'])
        ]
        
        analysis = {
            'workflows': {},
            'platform_success_rates': defaultdict(list),
            'overall_health': {},
            'recommendations': []
        }
        
        print(f"🔍 Analyzing {len(deployment_workflows)} deployment workflows...")
        
        for workflow in deployment_workflows:
            workflow_name = workflow['name']
            workflow_id = workflow['id']
            
            print(f"  📊 {workflow_name}...")
            
            runs = self.get_workflow_runs(workflow_id, days_back)
            
            if not runs:
                analysis['workflows'][workflow_name] = {
                    'status': 'inactive',
                    'last_run': 'never',
                    'success_rate': 0,
                    'issues': ['No recent runs']
                }
                continue
            
            # Analyze run outcomes
            successes = len([r for r in runs if r['conclusion'] == 'success'])
            failures = len([r for r in runs if r['conclusion'] == 'failure'])
            total_runs = len(runs)
            success_rate = (successes / total_runs) * 100 if total_runs > 0 else 0
            
            # Get detailed job analysis for latest failed run
            issues = []
            latest_failed = next((r for r in runs if r['conclusion'] == 'failure'), None)
            if latest_failed:
                try:
                    jobs = self.get_run_jobs(latest_failed['id'])
                    failed_jobs = [j for j in jobs if j['conclusion'] == 'failure']
                    for job in failed_jobs:
                        issues.append(f"Job '{job['name']}' failed")
                except:
                    issues.append("Failed to analyze job details")
            
            # Determine workflow health status
            if success_rate >= 80:
                status = 'healthy'
            elif success_rate >= 50:
                status = 'unstable'
            else:
                status = 'broken'
            
            analysis['workflows'][workflow_name] = {
                'status': status,
                'last_run': runs[0]['created_at'][:10],
                'success_rate': success_rate,
                'total_runs': total_runs,
                'successes': successes,
                'failures': failures,
                'issues': issues,
                'url': f"https://github.com/{self.repo}/actions/workflows/{workflow['path']}"
            }
            
            # Extract platform information from workflow name/path
            platforms = self.extract_platforms_from_workflow(workflow_name, workflow.get('path', ''))
            for platform in platforms:
                analysis['platform_success_rates'][platform].append(success_rate)
        
        # Calculate overall health metrics
        all_success_rates = [w['success_rate'] for w in analysis['workflows'].values() 
                           if w['status'] != 'inactive']
        
        if all_success_rates:
            analysis['overall_health'] = {
                'average_success_rate': sum(all_success_rates) / len(all_success_rates),
                'healthy_workflows': len([w for w in analysis['workflows'].values() 
                                        if w['status'] == 'healthy']),
                'total_active_workflows': len(all_success_rates),
                'deployment_reliability': 'Good' if sum(all_success_rates) / len(all_success_rates) > 70 else 'Needs Improvement'
            }
        
        # Generate recommendations
        analysis['recommendations'] = self.generate_recommendations(analysis)
        
        return analysis
    
    def extract_platforms_from_workflow(self, name: str, path: str) -> List[str]:
        """Extract platform names from workflow name/path"""
        platforms = []
        platform_keywords = {
            'npm': ['npm'],
            'pypi': ['pypi', 'python'],
            'docker': ['docker'],
            'chocolatey': ['chocolatey', 'choco'],
            'homebrew': ['homebrew', 'brew'],
            'github': ['github', 'release'],
            'crates': ['crates', 'rust'],
            'snap': ['snap'],
            'aur': ['aur', 'arch']
        }
        
        text = f"{name} {path}".lower()
        
        for platform, keywords in platform_keywords.items():
            if any(keyword in text for keyword in keywords):
                platforms.append(platform)
        
        return platforms
    
    def generate_recommendations(self, analysis: Dict[str, Any]) -> List[str]:
        """Generate actionable recommendations based on analysis"""
        recommendations = []
        
        # Check for broken workflows
        broken_workflows = [name for name, data in analysis['workflows'].items() 
                          if data['status'] == 'broken']
        if broken_workflows:
            recommendations.append(f"🚨 Fix {len(broken_workflows)} broken workflows: {', '.join(broken_workflows)}")
        
        # Check for inactive workflows
        inactive_workflows = [name for name, data in analysis['workflows'].items() 
                            if data['status'] == 'inactive']
        if inactive_workflows:
            recommendations.append(f"🔄 Consider removing or updating {len(inactive_workflows)} inactive workflows")
        
        # Check for platform coverage gaps
        platform_rates = analysis['platform_success_rates']
        for platform, rates in platform_rates.items():
            avg_rate = sum(rates) / len(rates) if rates else 0
            if avg_rate < 50:
                recommendations.append(f"📦 {platform} deployment needs attention (success rate: {avg_rate:.1f}%)")
        
        # Check overall health
        overall = analysis['overall_health']
        if overall and overall['average_success_rate'] < 70:
            recommendations.append("⚡ Overall deployment reliability is low - consider workflow consolidation")
        
        return recommendations
    
    def print_health_report(self, analysis: Dict[str, Any]):
        """Print comprehensive workflow health report"""
        print("\n" + "="*80)
        print("🏥 CONTEXTLITE WORKFLOW HEALTH REPORT")
        print(f"📅 Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print("="*80)
        
        # Overall health summary
        overall = analysis['overall_health']
        if overall:
            print(f"\n📊 OVERALL DEPLOYMENT HEALTH")
            print(f"   Success Rate: {overall['average_success_rate']:.1f}%")
            print(f"   Healthy Workflows: {overall['healthy_workflows']}/{overall['total_active_workflows']}")
            print(f"   Reliability: {overall['deployment_reliability']}")
        
        # Workflow details
        print(f"\n🔧 WORKFLOW STATUS BREAKDOWN")
        print(f"{'Workflow':<30} {'Status':<12} {'Success Rate':<12} {'Last Run':<12} {'Issues'}")
        print("-" * 80)
        
        for name, data in sorted(analysis['workflows'].items()):
            status_icon = {
                'healthy': '✅',
                'unstable': '⚠️',
                'broken': '❌',
                'inactive': '⏸️'
            }.get(data['status'], '❓')
            
            issues_summary = f"{len(data['issues'])} issues" if data['issues'] else "None"
            
            print(f"{name[:29]:<30} {status_icon} {data['status']:<11} {data['success_rate']:>8.1f}%    {data['last_run']:<12} {issues_summary}")
            
            # Show specific issues for problematic workflows
            if data['issues'] and data['status'] in ['broken', 'unstable']:
                for issue in data['issues'][:2]:  # Show max 2 issues
                    print(f"{'  └─':<30} {issue}")
        
        # Platform analysis
        platform_rates = analysis['platform_success_rates']
        if platform_rates:
            print(f"\n📦 PLATFORM DEPLOYMENT SUCCESS RATES")
            for platform, rates in sorted(platform_rates.items()):
                avg_rate = sum(rates) / len(rates) if rates else 0
                status_icon = "✅" if avg_rate >= 80 else "⚠️" if avg_rate >= 50 else "❌"
                print(f"   {status_icon} {platform.capitalize()}: {avg_rate:.1f}% (across {len(rates)} workflows)")
        
        # Recommendations
        recommendations = analysis['recommendations']
        if recommendations:
            print(f"\n💡 ACTIONABLE RECOMMENDATIONS")
            for i, rec in enumerate(recommendations, 1):
                print(f"   {i}. {rec}")
        
        print("\n🔗 WORKFLOW LINKS")
        for name, data in analysis['workflows'].items():
            if data['status'] != 'inactive':
                print(f"   {name}: {data['url']}")
        
        print("="*80)
    
    def monitor_deployment_health(self, days_back: int = 14):
        """Run complete deployment health monitoring"""
        try:
            analysis = self.analyze_deployment_patterns(days_back)
            self.print_health_report(analysis)
            return analysis
        except Exception as e:
            print(f"❌ Error monitoring deployment health: {e}")
            raise

def main():
    monitor = WorkflowHealthMonitor()
    monitor.monitor_deployment_health()

if __name__ == "__main__":
    main()
