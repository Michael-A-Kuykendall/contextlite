FROM alpine:latest AS builder
COPY contextlite-amd64 /usr/local/bin/contextlite
RUN chmod +x /usr/local/bin/contextlite

FROM gcr.io/distroless/static:nonroot
COPY --from=builder /usr/local/bin/contextlite /usr/local/bin/contextlite
USER nonroot
EXPOSE 8080
ENTRYPOINT ["/usr/local/bin/contextlite"]
CMD ["--help"]
