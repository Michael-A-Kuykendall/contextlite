class Contextlite < Formula
  desc "Ultra-fast context engine with enterprise workspace clustering for AI applications"
  homepage "https://contextlite.com"
  url "https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v#{version}/contextlite_Darwin_x86_64.tar.gz"
  sha256 "#{ENV['AMD64_SHA']}"
  license "MIT"

  depends_on "git"

  on_intel do
    url "https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v#{version}/contextlite_Darwin_x86_64.tar.gz"
    sha256 "#{ENV['AMD64_SHA']}"
  end

  on_arm do
    url "https://github.com/Michael-A-Kuykendall/contextlite/releases/download/v#{version}/contextlite_Darwin_arm64.tar.gz"
    sha256 "#{ENV['ARM64_SHA']}"
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
