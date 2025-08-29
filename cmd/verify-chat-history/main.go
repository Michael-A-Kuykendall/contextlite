package main

import (
	"database/sql"
	"fmt"
	"log"

	_ "modernc.org/sqlite"
)

func main() {
	fmt.Println("🔍 ContextLite Chat History Verification")
	fmt.Println("========================================")

	// Connect to database
	db, err := sql.Open("sqlite", "./contextlite.db")
	if err != nil {
		log.Fatalf("Failed to open database: %v", err)
	}
	defer db.Close()

	// Check if chat_history table exists
	var tableExists int
	err = db.QueryRow("SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='chat_history'").Scan(&tableExists)
	if err != nil {
		log.Fatalf("Failed to check table existence: %v", err)
	}

	if tableExists == 0 {
		fmt.Println("❌ chat_history table does not exist")
		return
	}

	fmt.Println("✅ chat_history table exists")

	// Get total message count
	var totalCount int
	err = db.QueryRow("SELECT COUNT(*) FROM chat_history").Scan(&totalCount)
	if err != nil {
		log.Fatalf("Failed to count messages: %v", err)
	}

	fmt.Printf("📊 Total messages in database: %d\n\n", totalCount)

	// Get breakdown by source
	rows, err := db.Query("SELECT source, message_type, COUNT(*) FROM chat_history GROUP BY source, message_type ORDER BY source, message_type")
	if err != nil {
		log.Fatalf("Failed to get breakdown: %v", err)
	}
	defer rows.Close()

	fmt.Println("📊 Message breakdown:")
	for rows.Next() {
		var source, messageType string
		var count int
		if err := rows.Scan(&source, &messageType, &count); err != nil {
			log.Printf("Error scanning row: %v", err)
			continue
		}
		fmt.Printf("   %s - %s: %d messages\n", source, messageType, count)
	}

	// Sample recent messages
	fmt.Println("\n🔍 Sample recent messages:")
	sampleRows, err := db.Query(`
		SELECT source, message_type, timestamp, substr(content, 1, 100) as preview 
		FROM chat_history 
		ORDER BY timestamp DESC 
		LIMIT 5
	`)
	if err != nil {
		log.Fatalf("Failed to get sample messages: %v", err)
	}
	defer sampleRows.Close()

	for sampleRows.Next() {
		var source, messageType, timestamp, preview string
		if err := sampleRows.Scan(&source, &messageType, &timestamp, &preview); err != nil {
			log.Printf("Error scanning sample row: %v", err)
			continue
		}
		fmt.Printf("   [%s] %s %s: %s...\n", timestamp, source, messageType, preview)
	}

	fmt.Println("\n✅ Chat history verification complete!")
}
