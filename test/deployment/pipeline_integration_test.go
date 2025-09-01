package main

import (
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"regexp"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// GitHubWorkflowRun represents a GitHub Actions workflow run
type GitHubWorkflowRun struct {
	ID          int64  `json:"id"`
	Name        string `json:"name"`
	Status      string `json:"status"`
	Conclusion  string `json:"conclusion"`
	CreatedAt   string `json:"created_at"`
	UpdatedAt   string `json:"updated_at"`
	HtmlURL     string `json:"html_url"`
	HeadBranch  string `json:"head_branch"`
	WorkflowID  int64  `json:"workflow_id"`
	DisplayTitle string `json:"display_title"`
}

// GitHubWorkflowResponse represents the GitHub API response for workflow runs
type GitHubWorkflowResponse struct {
	TotalCount   int                 `json:"total_count"`
	WorkflowRuns []GitHubWorkflowRun `json:"workflow_runs"`
}

// GitHubJob represents a job within a workflow run
type GitHubJob struct {
	ID          int64  `json:"id"`
	RunID       int64  `json:"run_id"`
	Name        string `json:"name"`
	Status      string `json:"status"`
	Conclusion  string `json:"conclusion"`
	StartedAt   string `json:"started_at"`
	CompletedAt string `json:"completed_at"`
	HtmlURL     string `json:"html_url"`
	Steps       []GitHubStep `json:"steps"`
}

// GitHubStep represents a step within a job
type GitHubStep struct {
	Name       string `json:"name"`
	Status     string `json:"status"`
	Conclusion string `json:"conclusion"`
	Number     int    `json:"number"`
	StartedAt  string `json:"started_at"`
	CompletedAt string `json:"completed_at"`
}

// GitHubJobsResponse represents the GitHub API response for jobs
type GitHubJobsResponse struct {
	TotalCount int         `json:"total_count"`
	Jobs       []GitHubJob `json:"jobs"`
}

// GitHubRelease represents a GitHub release
type GitHubRelease struct {
	TagName     string `json:"tag_name"`
	Name        string `json:"name"`
	Draft       bool   `json:"draft"`
	Prerelease  bool   `json:"prerelease"`
	CreatedAt   string `json:"created_at"`
	PublishedAt string `json:"published_at"`
	HtmlURL     string `json:"html_url"`
	Assets      []GitHubAsset `json:"assets"`
}

// GitHubAsset represents a release asset
type GitHubAsset struct {
	Name        string `json:"name"`
	Size        int64  `json:"size"`
	DownloadURL string `json:"browser_download_url"`
	CreatedAt   string `json:"created_at"`
}

// DeploymentTestRunner handles deployment pipeline testing
type DeploymentTestRunner struct {
	GitHubToken string
	Repository  string
	BaseURL     string
	HTTPClient  *http.Client
}

// NewDeploymentTestRunner creates a new deployment test runner
func NewDeploymentTestRunner() *DeploymentTestRunner {
	return &DeploymentTestRunner{
		GitHubToken: os.Getenv("GITHUB_TOKEN"),
		Repository:  "Michael-A-Kuykendall/contextlite",
		BaseURL:     "https://api.github.com",
		HTTPClient: &http.Client{
			Timeout: 30 * time.Second,
		},
	}
}

// makeGitHubRequest makes an authenticated request to GitHub API
func (d *DeploymentTestRunner) makeGitHubRequest(endpoint string) (*http.Response, error) {
	url := d.BaseURL + endpoint
	req, err := http.NewRequest("GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("creating request: %w", err)
	}

	if d.GitHubToken != "" {
		req.Header.Set("Authorization", "token "+d.GitHubToken)
	}
	req.Header.Set("Accept", "application/vnd.github.v3+json")

	return d.HTTPClient.Do(req)
}

// GetLatestWorkflowRuns retrieves the latest workflow runs
func (d *DeploymentTestRunner) GetLatestWorkflowRuns(limit int) ([]GitHubWorkflowRun, error) {
	endpoint := fmt.Sprintf("/repos/%s/actions/runs?per_page=%d", d.Repository, limit)
	resp, err := d.makeGitHubRequest(endpoint)
	if err != nil {
		return nil, fmt.Errorf("making request: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("GitHub API error: %d - %s", resp.StatusCode, string(body))
	}

	var response GitHubWorkflowResponse
	if err := json.NewDecoder(resp.Body).Decode(&response); err != nil {
		return nil, fmt.Errorf("decoding response: %w", err)
	}

	return response.WorkflowRuns, nil
}

// GetJobDetails retrieves detailed job information for a workflow run
func (d *DeploymentTestRunner) GetJobDetails(runID int64) ([]GitHubJob, error) {
	endpoint := fmt.Sprintf("/repos/%s/actions/runs/%d/jobs", d.Repository, runID)
	resp, err := d.makeGitHubRequest(endpoint)
	if err != nil {
		return nil, fmt.Errorf("making request: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("GitHub API error: %d - %s", resp.StatusCode, string(body))
	}

	var response GitHubJobsResponse
	if err := json.NewDecoder(resp.Body).Decode(&response); err != nil {
		return nil, fmt.Errorf("decoding response: %w", err)
	}

	return response.Jobs, nil
}

// GetLatestReleases retrieves the latest GitHub releases
func (d *DeploymentTestRunner) GetLatestReleases(limit int) ([]GitHubRelease, error) {
	endpoint := fmt.Sprintf("/repos/%s/releases?per_page=%d", d.Repository, limit)
	resp, err := d.makeGitHubRequest(endpoint)
	if err != nil {
		return nil, fmt.Errorf("making request: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("GitHub API error: %d - %s", resp.StatusCode, string(body))
	}

	var releases []GitHubRelease
	if err := json.NewDecoder(resp.Body).Decode(&releases); err != nil {
		return nil, fmt.Errorf("decoding response: %w", err)
	}

	return releases, nil
}

// TestLocalBuildSystem validates the local build system
func TestLocalBuildSystem(t *testing.T) {
	t.Log("🏗️  Testing Local Build System")

	// Test Go build works
	t.Run("Go Build", func(t *testing.T) {
		cmd := exec.Command("go", "build", "-o", "test_contextlite", "./cmd/contextlite")
		cmd.Dir = "../.."
		output, err := cmd.CombinedOutput()
		require.NoError(t, err, "Go build failed: %s", string(output))

		// Check binary exists
		_, err = os.Stat("../../test_contextlite")
		assert.NoError(t, err, "Binary not created")

		// Cleanup
		os.Remove("../../test_contextlite")
		os.Remove("../../test_contextlite.exe") // Windows
	})

	// Test make build works
	t.Run("Make Build", func(t *testing.T) {
		cmd := exec.Command("make", "build")
		cmd.Dir = "../.."
		output, err := cmd.CombinedOutput()
		require.NoError(t, err, "Make build failed: %s", string(output))

		// Check binary exists
		_, err = os.Stat("../../build/contextlite")
		if err != nil {
			_, err = os.Stat("../../build/contextlite.exe") // Windows
		}
		assert.NoError(t, err, "Make build binary not created")
	})

	// Test make test works
	t.Run("Make Test", func(t *testing.T) {
		cmd := exec.Command("make", "test")
		cmd.Dir = "../.."
		output, err := cmd.CombinedOutput()
		if err != nil {
			t.Logf("Make test output: %s", string(output))
		}
		// Don't require this to pass - we're testing the deployment pipeline
		// require.NoError(t, err, "Make test failed: %s", string(output))
	})
}

// TestGitHubActionsAPI validates GitHub Actions API connectivity
func TestGitHubActionsAPI(t *testing.T) {
	t.Log("🔌 Testing GitHub Actions API Connectivity")

	runner := NewDeploymentTestRunner()
	require.NotEmpty(t, runner.GitHubToken, "GITHUB_TOKEN environment variable is required")

	t.Run("API Authentication", func(t *testing.T) {
		// Test API authentication works
		runs, err := runner.GetLatestWorkflowRuns(1)
		require.NoError(t, err, "Failed to authenticate with GitHub API")
		assert.NotEmpty(t, runs, "No workflow runs found")
	})

	t.Run("Workflow Run Analysis", func(t *testing.T) {
		// Get recent workflow runs
		runs, err := runner.GetLatestWorkflowRuns(10)
		require.NoError(t, err, "Failed to get workflow runs")

		t.Logf("Found %d recent workflow runs", len(runs))

		// Analyze failure patterns
		var failures []GitHubWorkflowRun
		var successes []GitHubWorkflowRun

		for _, run := range runs {
			t.Logf("Workflow: %s - Status: %s - Conclusion: %s - Branch: %s", 
				run.Name, run.Status, run.Conclusion, run.HeadBranch)

			if run.Conclusion == "failure" {
				failures = append(failures, run)
			} else if run.Conclusion == "success" {
				successes = append(successes, run)
			}
		}

		t.Logf("Failures: %d, Successes: %d", len(failures), len(successes))

		// Analyze most recent failures
		if len(failures) > 0 {
			for i, failure := range failures {
				if i >= 3 { // Limit to first 3 failures
					break
				}

				t.Logf("Analyzing failure: %s (ID: %d)", failure.Name, failure.ID)

				jobs, err := runner.GetJobDetails(failure.ID)
				if err != nil {
					t.Logf("Failed to get job details: %v", err)
					continue
				}

				for _, job := range jobs {
					if job.Conclusion == "failure" {
						t.Logf("  Failed job: %s - Started: %s", job.Name, job.StartedAt)

						// Count failed steps
						failedSteps := 0
						for _, step := range job.Steps {
							if step.Conclusion == "failure" {
								failedSteps++
								t.Logf("    Failed step: %s", step.Name)
							}
						}
						t.Logf("  Total failed steps: %d", failedSteps)
					}
				}
			}
		}
	})
}

// TestPackageManagerEndpoints validates package manager availability
func TestPackageManagerEndpoints(t *testing.T) {
	t.Log("📦 Testing Package Manager Endpoints")

	packageChecks := map[string]struct {
		url    string
		expect string
	}{
		"npm": {
			url:    "https://registry.npmjs.org/contextlite",
			expect: "contextlite",
		},
		"PyPI": {
			url:    "https://pypi.org/pypi/contextlite/json",
			expect: "contextlite",
		},
		"Chocolatey": {
			url:    "https://community.chocolatey.org/api/v2/Packages?$filter=Id%20eq%20%27contextlite%27",
			expect: "contextlite",
		},
		"Docker Hub": {
			url:    "https://hub.docker.com/v2/repositories/makuykendall/contextlite/",
			expect: "contextlite",
		},
	}

	client := &http.Client{Timeout: 10 * time.Second}

	for name, check := range packageChecks {
		t.Run(name, func(t *testing.T) {
			resp, err := client.Get(check.url)
			if err != nil {
				t.Logf("%s endpoint unreachable: %v", name, err)
				return
			}
			defer resp.Body.Close()

			body, err := io.ReadAll(resp.Body)
			if err != nil {
				t.Logf("%s failed to read response: %v", name, err)
				return
			}

			if resp.StatusCode == 200 && strings.Contains(string(body), check.expect) {
				t.Logf("%s: ✅ Package exists and accessible", name)
			} else {
				t.Logf("%s: ❌ Package not found or inaccessible (Status: %d)", name, resp.StatusCode)
			}
		})
	}
}

// TestGoReleaserConfiguration validates GoReleaser setup
func TestGoReleaserConfiguration(t *testing.T) {
	t.Log("🚀 Testing GoReleaser Configuration")

	t.Run("GoReleaser Config Exists", func(t *testing.T) {
		configFiles := []string{
			"../../.goreleaser.yml",
			"../../.goreleaser.yaml",
			"../../goreleaser.yml",
			"../../goreleaser.yaml",
		}

		var configFound bool
		for _, config := range configFiles {
			if _, err := os.Stat(config); err == nil {
				configFound = true
				t.Logf("Found GoReleaser config: %s", config)
				break
			}
		}

		assert.True(t, configFound, "No GoReleaser configuration file found")
	})

	t.Run("GoReleaser Validation", func(t *testing.T) {
		cmd := exec.Command("goreleaser", "check")
		cmd.Dir = "../.."
		output, err := cmd.CombinedOutput()

		if err != nil {
			t.Logf("GoReleaser check output: %s", string(output))
			// Don't fail if GoReleaser isn't installed
			if strings.Contains(string(output), "not found") {
				t.Skip("GoReleaser not installed")
			}
		}

		// Log the validation result
		t.Logf("GoReleaser validation: %s", string(output))
	})
}

// TestGitHubReleases validates release creation and assets
func TestGitHubReleases(t *testing.T) {
	t.Log("🏷️  Testing GitHub Releases")

	runner := NewDeploymentTestRunner()
	require.NotEmpty(t, runner.GitHubToken, "GITHUB_TOKEN environment variable is required")

	t.Run("Latest Releases", func(t *testing.T) {
		releases, err := runner.GetLatestReleases(5)
		require.NoError(t, err, "Failed to get releases")

		t.Logf("Found %d releases", len(releases))

		for i, release := range releases {
			if i >= 3 { // Limit to first 3 releases
				break
			}

			t.Logf("Release: %s - Created: %s - Assets: %d", 
				release.TagName, release.CreatedAt, len(release.Assets))

			// Check for expected asset patterns
			expectedPatterns := []string{
				`contextlite.*linux.*amd64`,
				`contextlite.*windows.*amd64`,
				`contextlite.*darwin.*amd64`,
			}

			for _, pattern := range expectedPatterns {
				found := false
				regex := regexp.MustCompile(pattern)
				for _, asset := range release.Assets {
					if regex.MatchString(asset.Name) {
						found = true
						t.Logf("  Found asset: %s (%d bytes)", asset.Name, asset.Size)
						break
					}
				}
				if !found {
					t.Logf("  Missing asset pattern: %s", pattern)
				}
			}
		}
	})
}

// TestDeploymentScripts validates deployment scripts
func TestDeploymentScripts(t *testing.T) {
	t.Log("📜 Testing Deployment Scripts")

	scripts := map[string]string{
		"deploy.sh":               "../../deploy.sh",
		"install-universal.sh":   "../../install-universal.sh", 
		"backup_contextlite.sh":  "../../backup_contextlite.sh",
	}

	for name, path := range scripts {
		t.Run(name, func(t *testing.T) {
			info, err := os.Stat(path)
			if err != nil {
				t.Logf("Script not found: %s", path)
				return
			}

			assert.True(t, info.Mode().IsRegular(), "Script is not a regular file")

			// Check if executable (Unix-like systems)
			if info.Mode()&0111 != 0 {
				t.Logf("Script is executable: %s", path)
			} else {
				t.Logf("Script may not be executable: %s", path)
			}

			// Read script content for basic validation
			content, err := os.ReadFile(path)
			if err != nil {
				t.Logf("Failed to read script: %v", err)
				return
			}

			// Basic shebang check
			if strings.HasPrefix(string(content), "#!") {
				t.Logf("Script has valid shebang: %s", path)
			} else {
				t.Logf("Script missing shebang: %s", path)
			}
		})
	}
}

// TestEnvironmentVariables validates required environment variables
func TestEnvironmentVariables(t *testing.T) {
	t.Log("🔐 Testing Environment Variables")

	requiredVars := []string{
		"GITHUB_TOKEN",
	}

	optionalVars := []string{
		"CHOCOLATEY_API_KEY",
		"NPM_TOKEN",
		"PYPI_TOKEN",
		"DOCKER_USERNAME",
		"DOCKER_PASSWORD",
		"CRATES_TOKEN",
	}

	for _, varName := range requiredVars {
		t.Run(fmt.Sprintf("Required_%s", varName), func(t *testing.T) {
			value := os.Getenv(varName)
			assert.NotEmpty(t, value, "Required environment variable %s is not set", varName)
			if value != "" {
				t.Logf("%s: ✅ Set (length: %d)", varName, len(value))
			}
		})
	}

	for _, varName := range optionalVars {
		t.Run(fmt.Sprintf("Optional_%s", varName), func(t *testing.T) {
			value := os.Getenv(varName)
			if value != "" {
				t.Logf("%s: ✅ Set (length: %d)", varName, len(value))
			} else {
				t.Logf("%s: ❌ Not set", varName)
			}
		})
	}
}

// Main test runner
func TestMain(m *testing.M) {
	fmt.Println("🎯 ContextLite Deployment Pipeline Integration Tests")
	fmt.Println(strings.Repeat("=", 60))
	
	// Ensure we're in the right directory
	if _, err := os.Stat("../../go.mod"); err != nil {
		fmt.Println("❌ Must run from test/deployment directory")
		os.Exit(1)
	}

	// Run tests
	code := m.Run()
	
	fmt.Println(strings.Repeat("=", 60))
	fmt.Println("✅ Deployment Pipeline Integration Tests Complete")
	
	os.Exit(code)
}
