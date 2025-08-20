#!/usr/bin/env python3
"""
ContextLite CLI Wrapper

This module provides the main entry point for the ContextLite Python package.
It handles binary detection, download, and execution.
"""

import sys
import subprocess
import platform
import os
from pathlib import Path
from typing import Optional, List

from .binary_manager import BinaryManager
from .exceptions import ContextLiteError, BinaryNotFoundError


def main() -> int:
    """Main entry point for contextlite command."""
    try:
        binary_manager = BinaryManager()
        binary_path = binary_manager.get_binary_path()
        
        if not binary_path:
            print("🔍 ContextLite binary not found in system, attempting to download...", file=sys.stderr)
            try:
                binary_path = binary_manager.download_binary()
                print(f"✅ Binary downloaded successfully to: {binary_path}", file=sys.stderr)
            except Exception as e:
                print(f"❌ Failed to download ContextLite binary: {e}", file=sys.stderr)
                print("\n🔧 Manual installation options:", file=sys.stderr)
                print("   Visit: https://github.com/Michael-A-Kuykendall/contextlite/releases", file=sys.stderr)
                print("   Or use direct download: https://contextlite.com/download", file=sys.stderr)
                return 1
            
        # Pass all arguments to the ContextLite binary
        cmd = [str(binary_path)] + sys.argv[1:]
        
        try:
            result = subprocess.run(cmd, check=False)
            return result.returncode
        except FileNotFoundError:
            print(f"❌ Failed to execute ContextLite binary at: {binary_path}", file=sys.stderr)
            return 1
        except KeyboardInterrupt:
            print("\n⏹️  ContextLite interrupted by user", file=sys.stderr)
            return 130
            
    except ContextLiteError as e:
        print(f"❌ ContextLite error: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"❌ Unexpected error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
