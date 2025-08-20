"""
ContextLite Python Package

A Python wrapper for the ContextLite context engine binary.
This package provides a convenient Python interface to launch and interact
with ContextLite, which is implemented as a high-performance Go binary.

Installation will automatically download the appropriate binary for your platform.
"""

__version__ = "1.0.0"
__author__ = "ContextLite Team"
__email__ = "support@contextlite.com"

from .client import ContextLiteClient
from .exceptions import ContextLiteError, BinaryNotFoundError, ServerError

__all__ = [
    "ContextLiteClient",
    "ContextLiteError", 
    "BinaryNotFoundError",
    "ServerError",
]
