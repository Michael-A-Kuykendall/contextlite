// contextlite_private.h - C Interface for ContextLite Private Engine
// CONFIDENTIAL AND PROPRIETARY - Commercial License Required

#ifndef CONTEXTLITE_PRIVATE_H
#define CONTEXTLITE_PRIVATE_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <stdbool.h>

// Library information
#define CONTEXTLITE_PRIVATE_VERSION_MAJOR 1
#define CONTEXTLITE_PRIVATE_VERSION_MINOR 0
#define CONTEXTLITE_PRIVATE_VERSION_PATCH 0

// Error codes
typedef enum {
    CONTEXTLITE_SUCCESS = 0,
    CONTEXTLITE_ERROR_INVALID_PARAMS = -1,
    CONTEXTLITE_ERROR_OUT_OF_MEMORY = -2,
    CONTEXTLITE_ERROR_INIT_FAILED = -3,
    CONTEXTLITE_ERROR_LICENSE_INVALID = -4,
    CONTEXTLITE_ERROR_ENGINE_BUSY = -5,
    CONTEXTLITE_ERROR_QUERY_FAILED = -6,
    CONTEXTLITE_ERROR_JSON_PARSE = -7
} contextlite_error_t;

// Opaque handle types
typedef struct contextlite_engine* contextlite_engine_handle_t;

// Library initialization and cleanup
contextlite_error_t contextlite_init(void);
void contextlite_cleanup(void);

// Engine management
contextlite_error_t contextlite_engine_create(
    const char* config_json,
    contextlite_engine_handle_t* engine
);

contextlite_error_t contextlite_engine_destroy(
    contextlite_engine_handle_t engine
);

// License validation
contextlite_error_t contextlite_validate_license(
    const char* license_key,
    const char* hardware_fingerprint
);

// Core operations
contextlite_error_t contextlite_add_document(
    contextlite_engine_handle_t engine,
    const char* document_json
);

contextlite_error_t contextlite_query(
    contextlite_engine_handle_t engine,
    const char* query_json,
    char** result_json  // Caller must free with contextlite_free_string
);

contextlite_error_t contextlite_get_stats(
    contextlite_engine_handle_t engine,
    char** stats_json  // Caller must free with contextlite_free_string
);

// Memory management
void contextlite_free_string(char* str);

// Error handling
const char* contextlite_error_string(contextlite_error_t error);

// Version information
void contextlite_version(int* major, int* minor, int* patch);
const char* contextlite_build_info(void);

// Hardware fingerprinting
contextlite_error_t contextlite_get_hardware_fingerprint(
    char** fingerprint  // Caller must free with contextlite_free_string
);

// License status
typedef struct {
    bool is_valid;
    uint64_t expiry_timestamp;
    const char* license_type;
    const char* organization;
    uint32_t max_documents;
    uint32_t max_queries_per_day;
} contextlite_license_info_t;

contextlite_error_t contextlite_get_license_info(
    contextlite_license_info_t* info
);

// Performance monitoring
typedef struct {
    uint64_t total_queries;
    uint64_t cache_hits;
    uint64_t cache_misses;
    double avg_query_time_ms;
    uint64_t documents_indexed;
    uint64_t memory_usage_bytes;
} contextlite_performance_stats_t;

contextlite_error_t contextlite_get_performance_stats(
    contextlite_engine_handle_t engine,
    contextlite_performance_stats_t* stats
);

#ifdef __cplusplus
}
#endif

#endif // CONTEXTLITE_PRIVATE_H
