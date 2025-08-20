"""
ContextLite Exceptions

Custom exception classes for ContextLite Python package.
"""


class ContextLiteError(Exception):
    """Base exception for ContextLite errors."""
    pass


class BinaryNotFoundError(ContextLiteError):
    """Raised when ContextLite binary cannot be found."""
    pass


class ServerError(ContextLiteError):
    """Raised when server operations fail."""
    pass


class DownloadError(ContextLiteError):
    """Raised when binary download fails."""
    pass
