package main

import (
	"bufio"
	"database/sql"
	"encoding/json"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"strings"
	"time"

	_ "github.com/mattn/go-sqlite3"
)

// Claude message structure
type ClaudeMessage struct {
	UUID      string    `json:"uuid"`
	Type      string    `json:"type"`
	Content   string    `json:"content"`
	CreatedAt time.Time `json:"created_at"`
	UpdatedAt time.Time `json:"updated_at"`
}

// Copilot session structure
type CopilotSession struct {
	Version                    int                    `json:"version"`
	User                      string                 `json:"user"`
	Responder                 string                 `json:"responder"`
	ResponderAvatarIconUri    string                 `json:"responderAvatarIconUri"`
	Requests                  []CopilotRequest       `json:"requests"`
	Location                  string                 `json:"location"`
	SessionStartTime          time.Time              `json:"sessionStartTime"`
	LastUpdatedDate          time.Time              `json:"lastUpdatedDate"`
}

type CopilotRequest struct {
	Command              string                 `json:"command"`
	Response             CopilotResponse        `json:"response"`
	ResponseTime         time.Time              `json:"responseTime"`
	PromptElementRanges  []PromptElementRange   `json:"promptElementRanges"`
}

type CopilotResponse struct {
	ResponseText    string `json:"responseText"`
	ChosenResponse  string `json:"chosenResponse"`
}

type PromptElementRange struct {
	Kind   string `json:"kind"`
	Start  int    `json:"start"`
	End    int    `json:"end"`
	Text   string `json:"text"`
}

func main() {
	fmt.Println("🚀 ContextLite Chat History Ingester")
	fmt.Println("====================================")

	// Connect to ContextLite database
	db, err := sql.Open("sqlite3", "./contextlite.db")
	if err != nil {
		log.Fatalf("Failed to open database: %v", err)
	}
	defer db.Close()

	// Create chat_history table if it doesn't exist
	createTableSQL := `
	CREATE TABLE IF NOT EXISTS chat_history (
		id INTEGER PRIMARY KEY AUTOINCREMENT,
		source TEXT NOT NULL,           -- 'claude' or 'copilot'
		session_id TEXT,                -- file UUID for claude, session ID for copilot
		message_type TEXT NOT NULL,     -- 'user', 'assistant', 'system'
		content TEXT NOT NULL,
		timestamp DATETIME NOT NULL,
		uuid TEXT,                      -- claude UUID or copilot request ID
		metadata TEXT,                  -- JSON blob for additional data
		created_at DATETIME DEFAULT CURRENT_TIMESTAMP
	);
	
	CREATE INDEX IF NOT EXISTS idx_chat_source ON chat_history(source);
	CREATE INDEX IF NOT EXISTS idx_chat_timestamp ON chat_history(timestamp);
	CREATE INDEX IF NOT EXISTS idx_chat_session ON chat_history(session_id);
	`

	if _, err := db.Exec(createTableSQL); err != nil {
		log.Fatalf("Failed to create table: %v", err)
	}

	fmt.Println("✅ Database table ready")

	// Process Claude files
	claudePath := `C:\Users\micha\AppData\Roaming\Claude\claude_desktop\chat_history\C--Users-micha-repos-contextlite`
	fmt.Printf("📂 Processing Claude files from: %s\n", claudePath)
	
	claudeCount := 0
	err = filepath.Walk(claudePath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		if !strings.HasSuffix(path, ".jsonl") {
			return nil
		}

		count, err := processClaudeFile(db, path)
		if err != nil {
			fmt.Printf("❌ Error processing %s: %v\n", filepath.Base(path), err)
			return nil // Continue processing other files
		}

		claudeCount += count
		fmt.Printf("✅ Processed %s: %d messages\n", filepath.Base(path), count)
		return nil
	})

	if err != nil {
		log.Printf("Error walking Claude directory: %v", err)
	}

	// Process Copilot files
	copilotPath := `C:\Users\micha\AppData\Roaming\Code\User\workspaceStorage\a533c7164716c31deec2ec44e15c0f40\GitHub.copilot-chat\sessions`
	fmt.Printf("📂 Processing Copilot files from: %s\n", copilotPath)
	
	copilotCount := 0
	err = filepath.Walk(copilotPath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		if !strings.HasSuffix(path, ".json") {
			return nil
		}

		count, err := processCopilotFile(db, path)
		if err != nil {
			fmt.Printf("❌ Error processing %s: %v\n", filepath.Base(path), err)
			return nil // Continue processing other files
		}

		copilotCount += count
		fmt.Printf("✅ Processed %s: %d messages\n", filepath.Base(path), count)
		return nil
	})

	if err != nil {
		log.Printf("Error walking Copilot directory: %v", err)
	}

	fmt.Println("\n🎉 Ingestion Complete!")
	fmt.Printf("📊 Claude Messages: %d\n", claudeCount)
	fmt.Printf("📊 Copilot Messages: %d\n", copilotCount)
	fmt.Printf("📊 Total Messages: %d\n", claudeCount+copilotCount)

	// Verify ingestion
	var totalCount int
	err = db.QueryRow("SELECT COUNT(*) FROM chat_history").Scan(&totalCount)
	if err != nil {
		log.Printf("Error verifying ingestion: %v", err)
	} else {
		fmt.Printf("✅ Database contains: %d total messages\n", totalCount)
	}
}

func processClaudeFile(db *sql.DB, filePath string) (int, error) {
	file, err := os.Open(filePath)
	if err != nil {
		return 0, err
	}
	defer file.Close()

	// Extract session ID from filename (UUID part)
	fileName := filepath.Base(filePath)
	sessionID := strings.TrimSuffix(fileName, ".jsonl")

	scanner := bufio.NewScanner(file)
	// Set larger buffer for large lines
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 10*1024*1024) // 10MB max line length

	count := 0
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" {
			continue
		}

		var msg ClaudeMessage
		if err := json.Unmarshal([]byte(line), &msg); err != nil {
			// Skip invalid JSON lines
			continue
		}

		// Insert into database
		insertSQL := `
		INSERT INTO chat_history (source, session_id, message_type, content, timestamp, uuid, metadata)
		VALUES (?, ?, ?, ?, ?, ?, ?)
		`

		metadata := map[string]interface{}{
			"file": fileName,
		}
		metadataJSON, _ := json.Marshal(metadata)

		_, err := db.Exec(insertSQL, "claude", sessionID, msg.Type, msg.Content, msg.CreatedAt, msg.UUID, string(metadataJSON))
		if err != nil {
			return count, err
		}

		count++
	}

	if err := scanner.Err(); err != nil {
		return count, err
	}

	return count, nil
}

func processCopilotFile(db *sql.DB, filePath string) (int, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return 0, err
	}

	var session CopilotSession
	if err := json.Unmarshal(data, &session); err != nil {
		return 0, err
	}

	// Extract session ID from filename
	fileName := filepath.Base(filePath)
	sessionID := strings.TrimSuffix(fileName, ".json")

	count := 0
	for i, request := range session.Requests {
		// Insert user message (command)
		if request.Command != "" {
			insertSQL := `
			INSERT INTO chat_history (source, session_id, message_type, content, timestamp, uuid, metadata)
			VALUES (?, ?, ?, ?, ?, ?, ?)
			`

			metadata := map[string]interface{}{
				"file":        fileName,
				"request_id":  i,
				"user":        session.User,
				"responder":   session.Responder,
				"location":    session.Location,
			}
			metadataJSON, _ := json.Marshal(metadata)

			_, err := db.Exec(insertSQL, "copilot", sessionID, "user", request.Command, request.ResponseTime, fmt.Sprintf("req_%d", i), string(metadataJSON))
			if err != nil {
				return count, err
			}
			count++
		}

		// Insert assistant response
		responseText := request.Response.ResponseText
		if responseText == "" {
			responseText = request.Response.ChosenResponse
		}

		if responseText != "" {
			insertSQL := `
			INSERT INTO chat_history (source, session_id, message_type, content, timestamp, uuid, metadata)
			VALUES (?, ?, ?, ?, ?, ?, ?)
			`

			metadata := map[string]interface{}{
				"file":        fileName,
				"request_id":  i,
				"user":        session.User,
				"responder":   session.Responder,
				"location":    session.Location,
				"prompt_elements": len(request.PromptElementRanges),
			}
			metadataJSON, _ := json.Marshal(metadata)

			_, err := db.Exec(insertSQL, "copilot", sessionID, "assistant", responseText, request.ResponseTime, fmt.Sprintf("resp_%d", i), string(metadataJSON))
			if err != nil {
				return count, err
			}
			count++
		}
	}

	return count, nil
}
