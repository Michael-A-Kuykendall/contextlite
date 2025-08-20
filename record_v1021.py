#!/usr/bin/env python3
# Record v1.0.21 results

import sys
sys.path.append('scripts')
from deployment_progress import record_attempt

successful = ['build-and-release', 'publish-npm', 'publish-docker', 'publish-pypi', 'publish-github-packages']
failed = ['publish-chocolatey', 'publish-crates', 'publish-aur', 'publish-homebrew', 'publish-snap']

attempt = record_attempt('v1.0.21', successful, failed, 9)
print(f"📊 RECORDED: {attempt['tag']} - {attempt['success_rate']}% success rate")
