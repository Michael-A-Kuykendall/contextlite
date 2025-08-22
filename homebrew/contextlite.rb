class Contextlite < Formula
  desc "Ultra-fast context engine for retrieval and AI applications"
  homepage "https://contextlite.com"
  url "https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v1.0.38/contextlite-1.0.38-darwin-amd64.tar.gz"
  sha256 "638a4e51dfcee17e90d39e11ac779d7156c347708f41afe6e77311b4f53f7652"
  license "MIT"

  depends_on "git"

  on_intel do
    url "https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v1.0.38/contextlite-1.0.38-darwin-amd64.tar.gz"
    sha256 "638a4e51dfcee17e90d39e11ac779d7156c347708f41afe6e77311b4f53f7652"
  end

  on_arm do
    url "https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v1.0.38/contextlite-1.0.38-darwin-arm64.tar.gz"
    sha256 "8ecfdb3913ff435c4da2b37ebf8427f46e0fdd5dbb024642f0d4f31806026cbe"
  end

  def install
    bin.install "contextlite"
    
    # Install man page if available
    if File.exist?("contextlite.1")
      man1.install "contextlite.1"
    end
    
    # Install shell completions if available
    if File.exist?("completions")
      bash_completion.install "completions/contextlite.bash" => "contextlite"
      zsh_completion.install "completions/_contextlite"
      fish_completion.install "completions/contextlite.fish"
    end
    
    # Create default config directory
    (etc/"contextlite").mkpath
  end

  service do
    run [opt_bin/"contextlite", "--port", "8080"]
    keep_alive true
    log_path var/"log/contextlite.log"
    error_log_path var/"log/contextlite.log"
    working_dir var/"lib/contextlite"
  end

  test do
    # Test basic functionality
    system "#{bin}/contextlite", "--version"
    
    # Test server can start (background process)
    port = "18080"
    pid = fork do
      exec "#{bin}/contextlite", "--port", port
    end
    
    sleep 3
    
    # Test health endpoint
    system "curl", "-f", "http://localhost:#{port}/health"
    
    # Cleanup
    Process.kill("TERM", pid)
    Process.wait(pid)
  end
end
