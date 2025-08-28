### Multi-stage build to guarantee binary presence
FROM golang:1.21-alpine AS builder
WORKDIR /app
RUN adduser -D -u 10001 appuser
COPY go.mod go.sum ./
RUN go mod download
COPY cmd/ ./cmd/
COPY internal/ ./internal/
# pkg directory is optional; copy only if present
RUN if [ -d pkg ]; then cp -r pkg /app/pkg; fi || true
# Build only license server (no CGO, static)
RUN CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -ldflags='-s -w' -o contextlite ./cmd/license-server

FROM gcr.io/distroless/static:nonroot
COPY --from=builder /app/contextlite /usr/local/bin/contextlite
USER nonroot
EXPOSE 8080
ENTRYPOINT ["/usr/local/bin/contextlite"]
