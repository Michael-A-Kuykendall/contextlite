#!/bin/bash
# ContextLite Database Backup Script
# Usage: ./backup_contextlite.sh

# Configuration
BACKUP_DIR="backups"
DB_FILE="contextlite.db"
FRESH_DB_FILE="contextlite_fresh.db"
RETENTION_DAYS=7

# Create backup directory if it doesn't exist
mkdir -p "$BACKUP_DIR"

# Generate timestamp
DATE=$(date +%Y%m%d_%H%M%S)

# Backup main database
if [ -f "$DB_FILE" ]; then
    echo "Backing up $DB_FILE..."
    cp "$DB_FILE" "$BACKUP_DIR/contextlite_${DATE}.db"
    echo "✅ Main database backed up to $BACKUP_DIR/contextlite_${DATE}.db"
else
    echo "⚠️ Warning: $DB_FILE not found"
fi

# Backup fresh database
if [ -f "$FRESH_DB_FILE" ]; then
    echo "Backing up $FRESH_DB_FILE..."
    cp "$FRESH_DB_FILE" "$BACKUP_DIR/contextlite_fresh_${DATE}.db"
    echo "✅ Fresh database backed up to $BACKUP_DIR/contextlite_fresh_${DATE}.db"
fi

# Clean up old backups (keep only last N days)
echo "Cleaning up old backups (older than $RETENTION_DAYS days)..."
find "$BACKUP_DIR" -name "contextlite_*.db" -mtime +$RETENTION_DAYS -delete 2>/dev/null
find "$BACKUP_DIR" -name "contextlite_fresh_*.db" -mtime +$RETENTION_DAYS -delete 2>/dev/null

echo "✅ Backup complete!"

# Show backup status
echo ""
echo "📊 Backup Status:"
echo "==================="
ls -lh "$BACKUP_DIR"/contextlite_*.db 2>/dev/null | tail -5
echo ""
echo "Total backups: $(ls -1 "$BACKUP_DIR"/contextlite_*.db 2>/dev/null | wc -l)"
echo "Disk usage: $(du -sh "$BACKUP_DIR" 2>/dev/null | cut -f1)"
