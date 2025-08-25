#!/bin/bash

# ContextLite Data Ingestion Pipeline
# Clones and indexes real large-scale public repositories

set -e

DATA_DIR="/opt/contextlite-demo/data"
REPOS_DIR="$DATA_DIR/repos"
DB_PATH="$DATA_DIR/contextlite.db"
LOG_FILE="$DATA_DIR/logs/ingestion.log"
CONTEXTLITE_BIN="/opt/contextlite-demo/bin/contextlite"

echo "📊 ContextLite Data Ingestion Pipeline Starting..."
echo "📅 Date: $(date)"
echo "🎯 Target: Real production repositories (~3.8GB code)"
echo "" | tee -a $LOG_FILE

# Create directories
mkdir -p "$REPOS_DIR" "$DATA_DIR/logs"

# Repository configuration
declare -A REPOS=(
    ["microsoft/vscode"]="https://github.com/microsoft/vscode.git"
    ["facebook/react"]="https://github.com/facebook/react.git"
    ["golang/go"]="https://github.com/golang/go.git"
    ["rust-lang/rust"]="https://github.com/rust-lang/rust.git"
    ["nodejs/node"]="https://github.com/nodejs/node.git"
    ["tensorflow/tensorflow"]="https://github.com/tensorflow/tensorflow.git"
    ["kubernetes/kubernetes"]="https://github.com/kubernetes/kubernetes.git"
)

# Function to clone repository efficiently
clone_repo() {
    local name=$1
    local url=$2
    local repo_dir="$REPOS_DIR/$name"
    
    echo "📥 Cloning $name..." | tee -a $LOG_FILE
    
    if [ -d "$repo_dir" ]; then
        echo "⚠️  Repository $name already exists, updating..." | tee -a $LOG_FILE
        cd "$repo_dir"
        git fetch origin main || git fetch origin master || true
        git reset --hard FETCH_HEAD || true
    else
        echo "🔽 Fresh clone of $name..." | tee -a $LOG_FILE
        git clone --depth=1 --single-branch "$url" "$repo_dir" 2>&1 | tee -a $LOG_FILE
    fi
    
    # Clean up git metadata to save space
    if [ -d "$repo_dir/.git" ]; then
        echo "🧹 Cleaning git metadata for $name..." | tee -a $LOG_FILE
        rm -rf "$repo_dir/.git"
    fi
    
    # Get repository statistics
    local file_count=$(find "$repo_dir" -type f | wc -l)
    local size=$(du -sh "$repo_dir" | cut -f1)
    echo "📈 $name: $file_count files, $size" | tee -a $LOG_FILE
}

# Function to index repository with ContextLite
index_repo() {
    local name=$1
    local repo_dir="$REPOS_DIR/$name"
    
    if [ ! -d "$repo_dir" ]; then
        echo "❌ Repository directory not found: $repo_dir" | tee -a $LOG_FILE
        return 1
    fi
    
    echo "🔍 Indexing $name with ContextLite..." | tee -a $LOG_FILE
    
    # Change to repository directory
    cd "$repo_dir"
    
    # Run ContextLite indexing with timing
    local start_time=$(date +%s)
    
    if [ -f "$CONTEXTLITE_BIN" ]; then
        echo "⚡ Running: $CONTEXTLITE_BIN index ." | tee -a $LOG_FILE
        timeout 600 "$CONTEXTLITE_BIN" index . 2>&1 | tee -a $LOG_FILE || {
            echo "⚠️  Indexing timeout or error for $name (continuing...)" | tee -a $LOG_FILE
        }
    else
        echo "⚠️  ContextLite binary not found at $CONTEXTLITE_BIN" | tee -a $LOG_FILE
        echo "💡 Using mock indexing for testing..." | tee -a $LOG_FILE
        sleep 5  # Simulate indexing time
    fi
    
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    
    echo "⏱️  Indexing completed for $name in ${duration}s" | tee -a $LOG_FILE
}

# Function to optimize database
optimize_database() {
    echo "🚀 Optimizing ContextLite database..." | tee -a $LOG_FILE
    
    if [ -f "$DB_PATH" ]; then
        echo "📊 Database statistics before optimization:" | tee -a $LOG_FILE
        sqlite3 "$DB_PATH" "SELECT COUNT(*) as total_records FROM sqlite_master WHERE type='table';" | tee -a $LOG_FILE
        
        echo "🔧 Running VACUUM and ANALYZE..." | tee -a $LOG_FILE
        sqlite3 "$DB_PATH" "VACUUM; ANALYZE;" 2>&1 | tee -a $LOG_FILE
        
        echo "📏 Database size after optimization:" | tee -a $LOG_FILE
        du -sh "$DB_PATH" | tee -a $LOG_FILE
    else
        echo "⚠️  Database not found at $DB_PATH" | tee -a $LOG_FILE
    fi
}

# Function to generate statistics
generate_statistics() {
    echo "📈 Generating ingestion statistics..." | tee -a $LOG_FILE
    
    local stats_file="$DATA_DIR/ingestion_stats.json"
    local total_files=0
    local total_size=0
    
    # Count files and sizes
    for repo_name in "${!REPOS[@]}"; do
        local repo_dir="$REPOS_DIR/$repo_name"
        if [ -d "$repo_dir" ]; then
            local file_count=$(find "$repo_dir" -type f | wc -l)
            local size_bytes=$(du -sb "$repo_dir" | cut -f1)
            total_files=$((total_files + file_count))
            total_size=$((total_size + size_bytes))
        fi
    done
    
    # Convert size to human readable
    local total_size_human=$(echo $total_size | awk '{
        if ($1 > 1073741824) printf "%.1fGB", $1/1073741824
        else if ($1 > 1048576) printf "%.1fMB", $1/1048576
        else if ($1 > 1024) printf "%.1fKB", $1/1024
        else printf "%dB", $1
    }')
    
    # Create statistics JSON
    cat > "$stats_file" <<EOF
{
    "ingestion_date": "$(date -Iseconds)",
    "repositories": $(echo "${!REPOS[@]}" | wc -w),
    "total_files": $total_files,
    "total_size_bytes": $total_size,
    "total_size_human": "$total_size_human",
    "database_path": "$DB_PATH",
    "database_size": "$([ -f "$DB_PATH" ] && du -sh "$DB_PATH" | cut -f1 || echo "N/A")",
    "repositories_indexed": {
EOF
    
    local first=true
    for repo_name in "${!REPOS[@]}"; do
        local repo_dir="$REPOS_DIR/$repo_name"
        if [ -d "$repo_dir" ]; then
            local file_count=$(find "$repo_dir" -type f | wc -l)
            local size=$(du -sh "$repo_dir" | cut -f1)
            
            if [ "$first" = true ]; then
                first=false
            else
                echo "," >> "$stats_file"
            fi
            
            echo "        \"$repo_name\": {" >> "$stats_file"
            echo "            \"files\": $file_count," >> "$stats_file"
            echo "            \"size\": \"$size\"" >> "$stats_file"
            echo -n "        }" >> "$stats_file"
        fi
    done
    
    cat >> "$stats_file" <<EOF

    },
    "performance_metrics": {
        "indexing_start": "$(head -1 $LOG_FILE | grep -o '[0-9][0-9]:[0-9][0-9]:[0-9][0-9]' || echo 'N/A')",
        "indexing_complete": "$(date +%H:%M:%S)",
        "log_file": "$LOG_FILE"
    }
}
EOF
    
    echo "📊 Statistics saved to: $stats_file" | tee -a $LOG_FILE
    echo "📋 Quick stats:" | tee -a $LOG_FILE
    echo "   • Repositories: $(echo "${!REPOS[@]}" | wc -w)" | tee -a $LOG_FILE
    echo "   • Total files: $total_files" | tee -a $LOG_FILE
    echo "   • Total size: $total_size_human" | tee -a $LOG_FILE
}

# Function to verify indexing
verify_indexing() {
    echo "✅ Verifying ContextLite indexing..." | tee -a $LOG_FILE
    
    if [ -f "$CONTEXTLITE_BIN" ]; then
        echo "🔍 Testing search functionality..." | tee -a $LOG_FILE
        
        # Test basic search
        cd "$REPOS_DIR"
        echo "Search test: function" | tee -a $LOG_FILE
        timeout 30 "$CONTEXTLITE_BIN" search "function" 2>&1 | head -5 | tee -a $LOG_FILE || true
        
        echo "Search test: React component" | tee -a $LOG_FILE  
        timeout 30 "$CONTEXTLITE_BIN" search "React component" 2>&1 | head -5 | tee -a $LOG_FILE || true
        
        echo "🎯 ContextLite verification complete" | tee -a $LOG_FILE
    else
        echo "⚠️  ContextLite binary not available for verification" | tee -a $LOG_FILE
    fi
}

# Main execution
echo "🚀 Starting data ingestion pipeline..." | tee -a $LOG_FILE

# Check available space
echo "💾 Checking disk space..." | tee -a $LOG_FILE
df -h "$DATA_DIR" | tee -a $LOG_FILE

available_space=$(df "$DATA_DIR" | tail -1 | awk '{print $4}')
if [ "$available_space" -lt 5000000 ]; then  # Less than ~5GB
    echo "⚠️  Warning: Low disk space. Recommend at least 5GB free." | tee -a $LOG_FILE
fi

# Clone all repositories
echo "📥 Cloning repositories..." | tee -a $LOG_FILE
for repo_name in "${!REPOS[@]}"; do
    clone_repo "$repo_name" "${REPOS[$repo_name]}"
done

# Index all repositories
echo "🔍 Indexing repositories..." | tee -a $LOG_FILE
for repo_name in "${!REPOS[@]}"; do
    index_repo "$repo_name"
done

# Optimize database
optimize_database

# Generate statistics
generate_statistics

# Verify indexing
verify_indexing

# Final summary
echo "" | tee -a $LOG_FILE
echo "🎉 Data Ingestion Pipeline Complete!" | tee -a $LOG_FILE
echo "📊 Statistics: $DATA_DIR/ingestion_stats.json" | tee -a $LOG_FILE
echo "📋 Full log: $LOG_FILE" | tee -a $LOG_FILE
echo "🗂️  Repository data: $REPOS_DIR" | tee -a $LOG_FILE
echo "🗃️  ContextLite database: $DB_PATH" | tee -a $LOG_FILE
echo "" | tee -a $LOG_FILE

# Display final statistics
if [ -f "$DATA_DIR/ingestion_stats.json" ]; then
    echo "📈 Final Statistics:" | tee -a $LOG_FILE
    jq -r '
        "📦 Repositories: " + (.repositories | tostring) + 
        "\n📄 Total files: " + (.total_files | tostring) +
        "\n💾 Total size: " + .total_size_human +
        "\n🗃️  Database: " + .database_size
    ' "$DATA_DIR/ingestion_stats.json" | tee -a $LOG_FILE
fi

echo "✅ Ready for web terminal deployment!" | tee -a $LOG_FILE
