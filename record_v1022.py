#!/usr/bin/env python3
# Record v1.0.22 results

import sys
sys.path.append('scripts')
from deployment_progress import record_attempt

successful = ['build-and-release', 'publish-docker', 'publish-npm', 'publish-pypi', 'publish-github-packages']
failed = ['publish-aur', 'publish-crates', 'publish-snap', 'publish-chocolatey', 'publish-homebrew']

attempt = record_attempt('v1.0.22', successful, failed, 9)
print(f"📊 RECORDED: {attempt['tag']} - {attempt['success_rate']}% success rate")
