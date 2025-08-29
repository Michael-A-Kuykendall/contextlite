# ContextLite Build Instructions

## Standard Build (Community Version)
```bash
go build -o contextlite ./cmd/contextlite
```

## Library Build (C Interface - requires private components)
```bash
go build -tags library -buildmode=c-shared -o libcontextlite.so library_main.go
```

Note: The library build requires access to private repository components and will produce stubs in the community version.
