#!/usr/bin/env python3
"""
ContextLite Deployment Progress Tracker
Tracks improvement over multiple deployment attempts
"""

import json
import os
from datetime import datetime

PROGRESS_FILE = "deployment_progress.json"

def load_progress():
    """Load historical progress data"""
    if os.path.exists(PROGRESS_FILE):
        with open(PROGRESS_FILE, 'r') as f:
            return json.load(f)
    return {"attempts": []}

def save_progress(progress):
    """Save progress data"""
    with open(PROGRESS_FILE, 'w') as f:
        json.dump(progress, f, indent=2)

def record_attempt(tag, successful_channels, failed_channels, total_channels):
    """Record a deployment attempt"""
    progress = load_progress()
    
    attempt = {
        "tag": tag,
        "timestamp": datetime.now().isoformat(),
        "successful": successful_channels,
        "failed": failed_channels,
        "total": total_channels,
        "success_rate": round(len(successful_channels) / total_channels * 100, 1)
    }
    
    progress["attempts"].append(attempt)
    save_progress(progress)
    
    return attempt

def show_progress():
    """Display deployment progress over time"""
    progress = load_progress()
    
    if not progress["attempts"]:
        print("📊 No deployment attempts recorded yet")
        return
    
    print("📈 CONTEXTLITE DEPLOYMENT PROGRESS HISTORY")
    print("=" * 60)
    
    for i, attempt in enumerate(progress["attempts"], 1):
        print(f"\n🏷️  ATTEMPT #{i} - {attempt['tag']}")
        print(f"📅 {attempt['timestamp']}")
        print(f"✅ Success Rate: {attempt['success_rate']}% ({len(attempt['successful'])}/{attempt['total']})")
        
        if attempt['successful']:
            print(f"✅ Working: {', '.join(attempt['successful'])}")
        
        if attempt['failed']:
            print(f"❌ Failed: {', '.join(attempt['failed'])}")
    
    # Show improvement
    if len(progress["attempts"]) > 1:
        first = progress["attempts"][0]
        latest = progress["attempts"][-1]
        improvement = latest['success_rate'] - first['success_rate']
        
        print(f"\n📈 OVERALL IMPROVEMENT")
        print(f"🎯 Success Rate: {first['success_rate']}% → {latest['success_rate']}% ({improvement:+.1f}%)")
        
        # Fixed channels
        first_successful = set(first['successful'])
        latest_successful = set(latest['successful'])
        newly_fixed = latest_successful - first_successful
        
        if newly_fixed:
            print(f"🔧 Newly Fixed: {', '.join(newly_fixed)}")

if __name__ == "__main__":
    # Record v1.0.20 results
    successful = ["publish-npm", "publish-pypi", "publish-docker", "publish-github-packages"]
    failed = ["publish-crates", "publish-chocolatey", "publish-aur", "publish-snap"]
    total = 9  # Including skipped ones
    
    attempt = record_attempt("v1.0.20", successful, failed, total)
    
    print(f"📊 RECORDED DEPLOYMENT ATTEMPT: {attempt['tag']}")
    print(f"✅ Success Rate: {attempt['success_rate']}%")
    print()
    
    show_progress()
