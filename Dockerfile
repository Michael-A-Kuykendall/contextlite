FROM gcr.io/distroless/static:nonroot

# Copy the binary from the build context
COPY contextlite /usr/local/bin/contextlite

# Use nonroot user for security
USER nonroot

# Expose the default port
EXPOSE 8080

# Set the entrypoint
ENTRYPOINT ["/usr/local/bin/contextlite"]

# Default command
CMD ["--help"]
