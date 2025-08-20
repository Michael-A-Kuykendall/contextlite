#!/usr/bin/env python3

import json
import requests
from datetime import datetime

def record_deployment():
    # GitHub API call to get the latest workflow run
    url = "https://api.github.com/repos/Michael-A-Kuykendall/contextlite/actions/workflows/publish-packages.yml/runs"
    params = {"per_page": 1, "status": "completed"}
    
    try:
        response = requests.get(url, params=params, timeout=10)
        if response.status_code == 200:
            runs = response.json()["workflow_runs"]
            if runs:
                latest_run = runs[0]
                
                # Get job details
                jobs_url = latest_run["jobs_url"]
                jobs_response = requests.get(jobs_url, timeout=10)
                
                if jobs_response.status_code == 200:
                    jobs = jobs_response.json()["jobs"]
                    
                    successful = []
                    failed = []
                    
                    for job in jobs:
                        if job["conclusion"] == "success":
                            successful.append(job["name"])
                        elif job["conclusion"] == "failure":
                            failed.append(job["name"])
                    
                    # Record the results
                    result = {
                        "version": "v1.0.23",
                        "timestamp": datetime.now().isoformat(),
                        "success_rate": f"{len(successful)}/{len(successful) + len(failed)}",
                        "success_percentage": round((len(successful) / (len(successful) + len(failed))) * 100, 1),
                        "successful": successful,
                        "failed": failed,
                        "notes": "Fixed Rust crates integration tests but still failing. Homebrew permission issue - need official tap. Chocolatey needs approval of existing package."
                    }
                    
                    print(f"📊 RECORDED DEPLOYMENT ATTEMPT: {result['version']}")
                    print(f"✅ Success Rate: {result['success_percentage']}%")
                    print(f"✅ Working: {', '.join(successful)}")
                    print(f"❌ Failed: {', '.join(failed)}")
                    
                    # Append to deployment_results.json
                    try:
                        with open("deployment_results.json", "r") as f:
                            results = json.load(f)
                    except FileNotFoundError:
                        results = []
                    
                    results.append(result)
                    
                    with open("deployment_results.json", "w") as f:
                        json.dump(results, f, indent=2)
                    
                    return result
    
    except Exception as e:
        print(f"Error recording deployment: {e}")
        return None

if __name__ == "__main__":
    record_deployment()
