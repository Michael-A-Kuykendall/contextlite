# ContextLite Docker Image
# Multi-stage build for minimal production image

# Build stage
FROM golang:1.21-alpine AS builder

# Install build dependencies
RUN apk add --no-cache git ca-certificates

# Set working directory
WORKDIR /app

# Copy go mod and sum files
COPY go.mod go.sum ./

# Download dependencies
RUN go mod download

# Copy source code
COPY . .

# Build the binary
RUN CGO_ENABLED=0 GOOS=linux go build -a -installsuffix cgo -o contextlite ./cmd/contextlite

# Production stage
FROM alpine:3.18

# Install ca-certificates for HTTPS requests
RUN apk --no-cache add ca-certificates tzdata

# Create non-root user
RUN addgroup -g 1001 -S contextlite && \
    adduser -u 1001 -S contextlite -G contextlite

# Create directories
RUN mkdir -p /app/data && \
    chown -R contextlite:contextlite /app

# Set working directory
WORKDIR /app

# Copy binary from builder stage
COPY --from=builder /app/contextlite /app/contextlite

# Copy any additional files if needed
# COPY --from=builder /app/configs /app/configs

# Change ownership
RUN chown contextlite:contextlite /app/contextlite

# Switch to non-root user
USER contextlite

# Expose port
EXPOSE 8080

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD /app/contextlite --health-check || exit 1

# Default command
CMD ["/app/contextlite", "--port", "8080", "--host", "0.0.0.0", "--database", "/app/data/contextlite.db"]

# Labels for metadata
LABEL maintainer="ContextLite Team <support@contextlite.com>"
LABEL description="Ultra-fast context engine for retrieval and AI applications"
LABEL version="1.0.0"
LABEL org.opencontainers.image.title="ContextLite"
LABEL org.opencontainers.image.description="Ultra-fast context engine for retrieval and AI applications with SMT-powered optimization. Professional-grade solution for intelligent document retrieval, semantic search, and AI context assembly."
LABEL org.opencontainers.image.url="https://contextlite.com"
LABEL org.opencontainers.image.source="https://github.com/Michael-A-Kuykendall/contextlite"
LABEL org.opencontainers.image.version="1.0.0"
LABEL org.opencontainers.image.created="2025-08-22T00:00:00Z"
LABEL org.opencontainers.image.licenses="MIT"
