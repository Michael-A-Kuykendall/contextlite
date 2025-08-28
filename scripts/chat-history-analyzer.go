package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"io/fs"
	"log"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"time"
)

// Claude Chat Message Structure (JSONL format)
type ClaudeMessage struct {
	ParentUUID      *string `json:"parentUuid"`
	IsSidechain     bool    `json:"isSidechain"`
	UserType        string  `json:"userType"`
	CWD             string  `json:"cwd"`
	SessionID       string  `json:"sessionId"`
	Version         string  `json:"version"`
	GitBranch       string  `json:"gitBranch"`
	Type            string  `json:"type"`
	UUID            string  `json:"uuid"`
	Timestamp       string  `json:"timestamp"`
	Message         json.RawMessage `json:"message"`
	IsCompactSummary bool   `json:"isCompactSummary,omitempty"`
	RequestID       string `json:"requestId,omitempty"`
}

// Copilot Chat Session Structure (JSON format)
type CopilotSession struct {
	Version                   int    `json:"version"`
	RequesterUsername         string `json:"requesterUsername"`
	RequesterAvatarIconUri    json.RawMessage `json:"requesterAvatarIconUri"`
	ResponderUsername         string `json:"responderUsername"`
	ResponderAvatarIconUri    json.RawMessage `json:"responderAvatarIconUri"`
	InitialLocation           string `json:"initialLocation"`
	Requests                  []json.RawMessage `json:"requests"`
}

// File Analysis Result
type FileAnalysis struct {
	FilePath     string
	FileSize     int64
	LineCount    int
	MessageCount int
	SessionCount int
	TimeRange    TimeRange
	Errors       []string
	Source       string // "claude" or "copilot"
	Preview      []string
}

type TimeRange struct {
	Start *time.Time
	End   *time.Time
}

func main() {
	fmt.Println("🔍 ContextLite Chat History Analyzer")
	fmt.Println("=====================================")
	
	// Define paths
	claudePath := `C:\Users\micha\.claude\projects\C--Users-micha-repos-contextlite`
	copilotPath := `C:\Users\micha\AppData\Roaming\Code\User\workspaceStorage\a533c7164716c31deec2ec44e15c0f40\chatSessions`
	
	fmt.Println("\n📂 Analyzing Claude Chat History...")
	claudeResults := analyzeClaudeFiles(claudePath)
	
	fmt.Println("\n📂 Analyzing Copilot Chat History...")
	copilotResults := analyzeCopilotFiles(copilotPath)
	
	fmt.Println("\n📊 Summary Report")
	fmt.Println("=================")
	printSummary(claudeResults, copilotResults)
	
	fmt.Println("\n🔍 Detailed Analysis")
	fmt.Println("====================")
	printDetailedAnalysis(claudeResults, copilotResults)
	
	fmt.Println("\n⚠️  Potential Issues")
	fmt.Println("====================")
	printIssues(claudeResults, copilotResults)
	
	fmt.Println("\n✅ Dry Run Complete!")
	fmt.Println("Ready for ContextLite ingestion once issues are resolved.")
}

func analyzeClaudeFiles(dirPath string) []FileAnalysis {
	var results []FileAnalysis
	
	err := filepath.WalkDir(dirPath, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			log.Printf("Error accessing %s: %v", path, err)
			return nil
		}
		
		if d.IsDir() || !strings.HasSuffix(path, ".jsonl") {
			return nil
		}
		
		analysis := analyzeClaudeFile(path)
		results = append(results, analysis)
		return nil
	})
	
	if err != nil {
		log.Printf("Error walking Claude directory: %v", err)
	}
	
	// Sort by file size for better overview
	sort.Slice(results, func(i, j int) bool {
		return results[i].FileSize > results[j].FileSize
	})
	
	return results
}

func analyzeClaudeFile(filePath string) FileAnalysis {
	analysis := FileAnalysis{
		FilePath: filePath,
		Source:   "claude",
		Errors:   []string{},
		Preview:  []string{},
	}
	
	// Get file info
	info, err := os.Stat(filePath)
	if err != nil {
		analysis.Errors = append(analysis.Errors, fmt.Sprintf("Failed to stat file: %v", err))
		return analysis
	}
	analysis.FileSize = info.Size()
	
	// Open and analyze file
	file, err := os.Open(filePath)
	if err != nil {
		analysis.Errors = append(analysis.Errors, fmt.Sprintf("Failed to open file: %v", err))
		return analysis
	}
	defer file.Close()
	
	scanner := bufio.NewScanner(file)
	// Increase buffer size for large lines (Claude files can have very long lines)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 10*1024*1024) // 10MB max line size
	
	lineNum := 0
	previewCount := 0
	
	for scanner.Scan() {
		lineNum++
		line := strings.TrimSpace(scanner.Text())
		
		if line == "" {
			continue
		}
		
		// Try to parse Claude message
		var msg ClaudeMessage
		if err := json.Unmarshal([]byte(line), &msg); err != nil {
			analysis.Errors = append(analysis.Errors, fmt.Sprintf("Line %d: JSON parse error: %v", lineNum, err))
			if previewCount < 3 {
				analysis.Preview = append(analysis.Preview, fmt.Sprintf("ERROR Line %d: %s", lineNum, line[:min(100, len(line))]))
				previewCount++
			}
			continue
		}
		
		analysis.MessageCount++
		
		// Parse timestamp
		if msg.Timestamp != "" {
			if t, err := time.Parse("2006-01-02T15:04:05.000Z", msg.Timestamp); err == nil {
				if analysis.TimeRange.Start == nil || t.Before(*analysis.TimeRange.Start) {
					analysis.TimeRange.Start = &t
				}
				if analysis.TimeRange.End == nil || t.After(*analysis.TimeRange.End) {
					analysis.TimeRange.End = &t
				}
			}
		}
		
		// Add to preview
		if previewCount < 5 {
			uuidPreview := msg.UUID
			if len(uuidPreview) > 8 {
				uuidPreview = uuidPreview[:8]
			}
			analysis.Preview = append(analysis.Preview, fmt.Sprintf("Line %d: %s [%s] UUID:%s", lineNum, msg.Type, msg.Timestamp, uuidPreview))
			previewCount++
		}
	}
	
	analysis.LineCount = lineNum
	
	if err := scanner.Err(); err != nil {
		analysis.Errors = append(analysis.Errors, fmt.Sprintf("Scanner error: %v", err))
	}
	
	return analysis
}

func analyzeCopilotFiles(dirPath string) []FileAnalysis {
	var results []FileAnalysis
	
	err := filepath.WalkDir(dirPath, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			log.Printf("Error accessing %s: %v", path, err)
			return nil
		}
		
		if d.IsDir() || !strings.HasSuffix(path, ".json") {
			return nil
		}
		
		analysis := analyzeCopilotFile(path)
		results = append(results, analysis)
		return nil
	})
	
	if err != nil {
		log.Printf("Error walking Copilot directory: %v", err)
	}
	
	// Sort by file size for better overview
	sort.Slice(results, func(i, j int) bool {
		return results[i].FileSize > results[j].FileSize
	})
	
	return results
}

func analyzeCopilotFile(filePath string) FileAnalysis {
	analysis := FileAnalysis{
		FilePath: filePath,
		Source:   "copilot",
		Errors:   []string{},
		Preview:  []string{},
	}
	
	// Get file info
	info, err := os.Stat(filePath)
	if err != nil {
		analysis.Errors = append(analysis.Errors, fmt.Sprintf("Failed to stat file: %v", err))
		return analysis
	}
	analysis.FileSize = info.Size()
	
	// Read and parse JSON
	data, err := os.ReadFile(filePath)
	if err != nil {
		analysis.Errors = append(analysis.Errors, fmt.Sprintf("Failed to read file: %v", err))
		return analysis
	}
	
	// Try to parse as Copilot session
	var session CopilotSession
	if err := json.Unmarshal(data, &session); err != nil {
		analysis.Errors = append(analysis.Errors, fmt.Sprintf("JSON parse error: %v", err))
		return analysis
	}
	
	analysis.SessionCount = 1
	analysis.MessageCount = len(session.Requests)
	analysis.LineCount = 1 // Single JSON object
	
	// Add preview information
	analysis.Preview = append(analysis.Preview, fmt.Sprintf("Version: %d", session.Version))
	analysis.Preview = append(analysis.Preview, fmt.Sprintf("User: %s", session.RequesterUsername))
	analysis.Preview = append(analysis.Preview, fmt.Sprintf("Responder: %s", session.ResponderUsername))
	analysis.Preview = append(analysis.Preview, fmt.Sprintf("Requests: %d", len(session.Requests)))
	analysis.Preview = append(analysis.Preview, fmt.Sprintf("Location: %s", session.InitialLocation))
	
	return analysis
}

func printSummary(claudeResults, copilotResults []FileAnalysis) {
	fmt.Printf("📊 Claude Files: %d\n", len(claudeResults))
	claudeTotal := calculateTotals(claudeResults)
	fmt.Printf("   Total Size: %.2f MB\n", float64(claudeTotal.TotalSize)/1024/1024)
	fmt.Printf("   Total Messages: %d\n", claudeTotal.TotalMessages)
	fmt.Printf("   Total Lines: %d\n", claudeTotal.TotalLines)
	
	fmt.Printf("\n📊 Copilot Files: %d\n", len(copilotResults))
	copilotTotal := calculateTotals(copilotResults)
	fmt.Printf("   Total Size: %.2f MB\n", float64(copilotTotal.TotalSize)/1024/1024)
	fmt.Printf("   Total Messages: %d\n", copilotTotal.TotalMessages)
	fmt.Printf("   Total Sessions: %d\n", copilotTotal.TotalSessions)
	
	overallTotal := claudeTotal.TotalSize + copilotTotal.TotalSize
	fmt.Printf("\n🎯 Overall Total: %.2f MB of chat history\n", float64(overallTotal)/1024/1024)
}

type Totals struct {
	TotalSize     int64
	TotalMessages int
	TotalLines    int
	TotalSessions int
}

func calculateTotals(results []FileAnalysis) Totals {
	var totals Totals
	for _, r := range results {
		totals.TotalSize += r.FileSize
		totals.TotalMessages += r.MessageCount
		totals.TotalLines += r.LineCount
		totals.TotalSessions += r.SessionCount
	}
	return totals
}

func printDetailedAnalysis(claudeResults, copilotResults []FileAnalysis) {
	fmt.Println("\n🔍 Claude Files (Top 5 by size):")
	for i, result := range claudeResults {
		if i >= 5 {
			break
		}
		printFileDetails(result)
	}
	
	fmt.Println("\n🔍 Copilot Files (Top 5 by size):")
	for i, result := range copilotResults {
		if i >= 5 {
			break
		}
		printFileDetails(result)
	}
}

func printFileDetails(analysis FileAnalysis) {
	filename := filepath.Base(analysis.FilePath)
	fmt.Printf("\n📄 %s\n", filename)
	fmt.Printf("   Size: %.2f MB\n", float64(analysis.FileSize)/1024/1024)
	fmt.Printf("   Messages: %d\n", analysis.MessageCount)
	fmt.Printf("   Lines: %d\n", analysis.LineCount)
	
	if analysis.TimeRange.Start != nil && analysis.TimeRange.End != nil {
		fmt.Printf("   Time Range: %s to %s\n", 
			analysis.TimeRange.Start.Format("2006-01-02 15:04"),
			analysis.TimeRange.End.Format("2006-01-02 15:04"))
	}
	
	if len(analysis.Preview) > 0 {
		fmt.Printf("   Preview:\n")
		for _, line := range analysis.Preview {
			fmt.Printf("     %s\n", line)
		}
	}
}

func printIssues(claudeResults, copilotResults []FileAnalysis) {
	errorCount := 0
	
	fmt.Println("🚨 Claude File Issues:")
	for _, result := range claudeResults {
		if len(result.Errors) > 0 {
			fmt.Printf("   %s:\n", filepath.Base(result.FilePath))
			for _, err := range result.Errors {
				fmt.Printf("     - %s\n", err)
				errorCount++
			}
		}
	}
	
	fmt.Println("\n🚨 Copilot File Issues:")
	for _, result := range copilotResults {
		if len(result.Errors) > 0 {
			fmt.Printf("   %s:\n", filepath.Base(result.FilePath))
			for _, err := range result.Errors {
				fmt.Printf("     - %s\n", err)
				errorCount++
			}
		}
	}
	
	if errorCount == 0 {
		fmt.Println("✅ No parsing errors detected!")
	} else {
		fmt.Printf("❌ Found %d total errors that need attention\n", errorCount)
	}
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}
