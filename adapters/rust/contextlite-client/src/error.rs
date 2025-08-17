//! Error types for the ContextLite Rust client.
//!
//! This module provides comprehensive error handling with detailed error messages
//! and proper error chaining for debugging.

use thiserror::Error;

/// The main error type for the ContextLite client
#[derive(Error, Debug)]
pub enum ContextLiteError {
    /// HTTP request errors
    #[error("HTTP request failed: {0}")]
    HttpError(#[from] reqwest::Error),
    
    /// JSON serialization/deserialization errors
    #[error("JSON processing failed: {0}")]
    JsonError(#[from] serde_json::Error),
    
    /// URL parsing errors
    #[error("Invalid URL: {0}")]
    UrlError(#[from] url::ParseError),
    
    /// Authentication errors
    #[error("Authentication failed: {message}")]
    AuthError { 
        /// Error message
        message: String 
    },
    
    /// Server returned an error status
    #[error("Server error {status}: {message}")]
    ServerError { 
        /// HTTP status code
        status: u16, 
        /// Error message
        message: String 
    },
    
    /// Document validation errors
    #[error("Document validation failed: {message}")]
    ValidationError { 
        /// Error message
        message: String 
    },
    
    /// Configuration errors
    #[error("Configuration error: {message}")]
    ConfigError { 
        /// Error message
        message: String 
    },
    
    /// Timeout errors
    #[error("Request timed out after {seconds} seconds")]
    TimeoutError { 
        /// Timeout duration in seconds
        seconds: u64 
    },
    
    /// Connection pool errors
    #[error("Connection pool error: {message}")]
    ConnectionError { 
        /// Error message
        message: String 
    },
    
    /// Invalid response format
    #[error("Invalid response format: {message}")]
    ResponseError { 
        /// Error message
        message: String 
    },
    
    /// Rate limiting errors
    #[error("Rate limit exceeded: {message}")]
    RateLimitError { 
        /// Error message
        message: String 
    },
    
    /// Generic client errors
    #[error("Client error: {message}")]
    ClientError { 
        /// Error message
        message: String 
    },
}

impl ContextLiteError {
    /// Create an authentication error
    pub fn auth(message: impl Into<String>) -> Self {
        Self::AuthError {
            message: message.into(),
        }
    }
    
    /// Create a server error
    pub fn server(status: u16, message: impl Into<String>) -> Self {
        Self::ServerError {
            status,
            message: message.into(),
        }
    }
    
    /// Create a validation error
    pub fn validation(message: impl Into<String>) -> Self {
        Self::ValidationError {
            message: message.into(),
        }
    }
    
    /// Create a configuration error
    pub fn config(message: impl Into<String>) -> Self {
        Self::ConfigError {
            message: message.into(),
        }
    }
    
    /// Create a timeout error
    pub fn timeout(seconds: u64) -> Self {
        Self::TimeoutError { seconds }
    }
    
    /// Create a connection error
    pub fn connection(message: impl Into<String>) -> Self {
        Self::ConnectionError {
            message: message.into(),
        }
    }
    
    /// Create a response error
    pub fn response(message: impl Into<String>) -> Self {
        Self::ResponseError {
            message: message.into(),
        }
    }
    
    /// Create a rate limit error
    pub fn rate_limit(message: impl Into<String>) -> Self {
        Self::RateLimitError {
            message: message.into(),
        }
    }
    
    /// Create a generic client error
    pub fn client(message: impl Into<String>) -> Self {
        Self::ClientError {
            message: message.into(),
        }
    }
    
    /// Check if this error is retryable
    pub fn is_retryable(&self) -> bool {
        match self {
            Self::HttpError(e) => {
                // Connection errors are retryable
                e.is_connect() || e.is_timeout()
            }
            Self::ServerError { status, .. } => {
                // 5xx errors are retryable, 4xx are not
                *status >= 500
            }
            Self::TimeoutError { .. } => true,
            Self::ConnectionError { .. } => true,
            Self::RateLimitError { .. } => true,
            _ => false,
        }
    }
    
    /// Check if this error is a client-side error
    pub fn is_client_error(&self) -> bool {
        match self {
            Self::ValidationError { .. } |
            Self::ConfigError { .. } |
            Self::AuthError { .. } |
            Self::JsonError(_) |
            Self::UrlError(_) => true,
            Self::ServerError { status, .. } => *status >= 400 && *status < 500,
            _ => false,
        }
    }
    
    /// Check if this error is a server-side error
    pub fn is_server_error(&self) -> bool {
        match self {
            Self::ServerError { status, .. } => *status >= 500,
            _ => false,
        }
    }
}

/// Result type for ContextLite operations
pub type Result<T> = std::result::Result<T, ContextLiteError>;

/// Helper function to handle HTTP response errors
pub async fn handle_response_error(response: reqwest::Response) -> Result<reqwest::Response> {
    let status = response.status();
    
    if status.is_success() {
        Ok(response)
    } else if status == 401 {
        Err(ContextLiteError::auth("Invalid or missing authentication token"))
    } else if status == 429 {
        let message = response.text().await
            .unwrap_or_else(|_| "Rate limit exceeded".to_string());
        Err(ContextLiteError::rate_limit(message))
    } else {
        let message = response.text().await
            .unwrap_or_else(|_| format!("HTTP {}", status.as_u16()));
        Err(ContextLiteError::server(status.as_u16(), message))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_error_creation() {
        let auth_err = ContextLiteError::auth("Invalid token");
        assert!(matches!(auth_err, ContextLiteError::AuthError { .. }));
        assert!(auth_err.is_client_error());
        assert!(!auth_err.is_retryable());
        
        let server_err = ContextLiteError::server(500, "Internal error");
        assert!(matches!(server_err, ContextLiteError::ServerError { .. }));
        assert!(server_err.is_server_error());
        assert!(server_err.is_retryable());
        
        let timeout_err = ContextLiteError::timeout(30);
        assert!(matches!(timeout_err, ContextLiteError::TimeoutError { .. }));
        assert!(timeout_err.is_retryable());
    }
    
    #[test]
    fn test_error_display() {
        let auth_err = ContextLiteError::auth("Invalid token");
        assert_eq!(auth_err.to_string(), "Authentication failed: Invalid token");
        
        let server_err = ContextLiteError::server(404, "Not found");
        assert_eq!(server_err.to_string(), "Server error 404: Not found");
        
        let timeout_err = ContextLiteError::timeout(60);
        assert_eq!(timeout_err.to_string(), "Request timed out after 60 seconds");
    }
    
    #[test]
    fn test_retryable_classification() {
        // Retryable errors
        assert!(ContextLiteError::server(500, "error").is_retryable());
        assert!(ContextLiteError::server(502, "error").is_retryable());
        assert!(ContextLiteError::timeout(30).is_retryable());
        assert!(ContextLiteError::connection("error").is_retryable());
        assert!(ContextLiteError::rate_limit("error").is_retryable());
        
        // Non-retryable errors
        assert!(!ContextLiteError::server(400, "error").is_retryable());
        assert!(!ContextLiteError::server(404, "error").is_retryable());
        assert!(!ContextLiteError::auth("error").is_retryable());
        assert!(!ContextLiteError::validation("error").is_retryable());
    }
    
    #[test]
    fn test_error_classification() {
        // Client errors
        assert!(ContextLiteError::server(400, "error").is_client_error());
        assert!(ContextLiteError::server(404, "error").is_client_error());
        assert!(ContextLiteError::auth("error").is_client_error());
        assert!(ContextLiteError::validation("error").is_client_error());
        
        // Server errors
        assert!(ContextLiteError::server(500, "error").is_server_error());
        assert!(ContextLiteError::server(502, "error").is_server_error());
        
        // Neither client nor server errors
        assert!(!ContextLiteError::timeout(30).is_client_error());
        assert!(!ContextLiteError::timeout(30).is_server_error());
    }
}
