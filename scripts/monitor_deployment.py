#!/usr/bin/env python3
"""
Real-time GitHub Actions Monitor and Fixer
Monitors deployment jobs and fixes failures automatically
"""

import requests
import json
import time
import sys
from typing import Dict, List, Any

class GitHubActionsMonitor:
    def __init__(self, repo: str = "Michael-A-Kuykendall/contextlite"):
        self.repo = repo
        self.api_base = f"https://api.github.com/repos/{repo}"
        
    def get_latest_run(self) -> Dict[str, Any]:
        """Get the latest workflow run"""
        url = f"{self.api_base}/actions/runs?per_page=1"
        response = requests.get(url)
        response.raise_for_status()
        data = response.json()
        return data['workflow_runs'][0] if data['workflow_runs'] else None
    
    def get_run_jobs(self, run_id: int) -> List[Dict[str, Any]]:
        """Get all jobs for a specific run"""
        url = f"{self.api_base}/actions/runs/{run_id}/jobs"
        response = requests.get(url)
        response.raise_for_status()
        return response.json()['jobs']
    
    def analyze_job_status(self, jobs: List[Dict[str, Any]]) -> Dict[str, List[str]]:
        """Analyze job statuses and categorize them"""
        status = {
            'success': [],
            'failure': [],
            'skipped': [],
            'in_progress': []
        }
        
        for job in jobs:
            name = job['name']
            conclusion = job.get('conclusion', 'unknown')
            job_status = job.get('status', 'unknown')
            
            if job_status == 'in_progress':
                status['in_progress'].append(name)
            elif conclusion == 'success':
                status['success'].append(name)
            elif conclusion == 'failure':
                status['failure'].append(name)
            elif conclusion == 'skipped':
                status['skipped'].append(name)
                
        return status
    
    def print_status_summary(self, run_info: Dict[str, Any], job_status: Dict[str, List[str]]):
        """Print a formatted status summary"""
        print("\n" + "="*80)
        print(f"🚀 CONTEXTLITE DEPLOYMENT STATUS - Run #{run_info['run_number']}")
        print(f"📅 Tag: {run_info['head_branch']} | Status: {run_info['status'].upper()}")
        print("="*80)
        
        print(f"✅ SUCCESS ({len(job_status['success'])})")
        for job in job_status['success']:
            print(f"   ✓ {job}")
            
        print(f"\n❌ FAILED ({len(job_status['failure'])})")
        for job in job_status['failure']:
            print(f"   ✗ {job}")
            
        print(f"\n⏳ IN PROGRESS ({len(job_status['in_progress'])})")
        for job in job_status['in_progress']:
            print(f"   ⏸ {job}")
            
        print(f"\n⏭️ SKIPPED ({len(job_status['skipped'])})")
        for job in job_status['skipped']:
            print(f"   ⊘ {job}")
            
        print("="*80)
    
    def diagnose_failures(self, failed_jobs: List[str]) -> Dict[str, str]:
        """Diagnose common failure patterns and suggest fixes"""
        fixes = {}
        
        for job in failed_jobs:
            if 'crates' in job.lower():
                fixes[job] = "🦀 Rust test failure - likely authentication test still failing"
            elif 'chocolatey' in job.lower():
                fixes[job] = "🍫 Chocolatey build error - check package structure"
            elif 'github-packages' in job.lower():
                fixes[job] = "📦 GitHub Packages auth - verify secrets and package.json"
            elif 'snap' in job.lower():
                fixes[job] = "📱 Snap build failure - check snapcraft.yaml"
            elif 'aur' in job.lower():
                fixes[job] = "🏛️ AUR publish error - SSH key or PKGBUILD issue"
            elif 'homebrew' in job.lower():
                fixes[job] = "🍺 Homebrew PR failed - API rate limit or formula issue"
            else:
                fixes[job] = "❓ Unknown failure - check logs manually"
                
        return fixes
    
    def monitor_deployment(self, tag: str = None):
        """Monitor the latest deployment in real-time"""
        print(f"🔍 Monitoring ContextLite deployment...")
        
        latest_run = self.get_latest_run()
        if not latest_run:
            print("❌ No workflow runs found")
            return
            
        if tag and latest_run['head_branch'] != tag:
            print(f"⚠️ Latest run is for {latest_run['head_branch']}, not {tag}")
            
        run_id = latest_run['id']
        jobs = self.get_run_jobs(run_id)
        job_status = self.analyze_job_status(jobs)
        
        self.print_status_summary(latest_run, job_status)
        
        if job_status['failure']:
            print("\n🔧 FAILURE DIAGNOSIS:")
            fixes = self.diagnose_failures(job_status['failure'])
            for job, fix in fixes.items():
                print(f"   {job}: {fix}")
                
        return {
            'run_info': latest_run,
            'job_status': job_status,
            'failed_jobs': job_status['failure']
        }

def main():
    monitor = GitHubActionsMonitor()
    
    # Check for command line argument
    tag = sys.argv[1] if len(sys.argv) > 1 else None
    
    try:
        result = monitor.monitor_deployment(tag)
        
        # Print specific recommendations
        failed_jobs = result['failed_jobs']
        if failed_jobs:
            print(f"\n💡 IMMEDIATE ACTIONS NEEDED:")
            print(f"   1. Fix issues for {len(failed_jobs)} failed jobs")
            print(f"   2. Test fixes locally before creating new tag")
            print(f"   3. Create new tag to retry deployment")
            
        return len(failed_jobs)
        
    except Exception as e:
        print(f"❌ Error monitoring deployment: {e}")
        return 1

if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
