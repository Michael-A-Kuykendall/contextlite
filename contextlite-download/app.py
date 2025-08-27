import gradio as gr
import requests
import json
from datetime import datetime

def get_latest_release():
    """Fetch latest release from GitHub API"""
    try:
        response = requests.get('https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases/latest', timeout=10)
        if response.status_code == 200:
            return response.json()
        else:
            print(f"GitHub API returned status code: {response.status_code}")
            return None
    except Exception as e:
        print(f"Error fetching GitHub release: {e}")
        return None

def format_file_size(bytes_size):
    """Convert bytes to MB"""
    return f"{bytes_size / 1024 / 1024:.1f} MB"

def get_contextlite_css():
    """CSS styles matching contextlite.com design"""
    return """
    <style>
        @import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&display=swap');
        
        .contextlite-container {
            font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            background: linear-gradient(135deg, #0f172a 0%, #1e293b 50%, #334155 100%);
            color: white;
            min-height: 100vh;
            margin: 0;
            padding: 0;
        }
        
        .hero-gradient {
            background: linear-gradient(45deg, #ef4444, #f97316, #eab308);
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
            background-clip: text;
        }
        
        .glass-card {
            background: rgba(30, 41, 59, 0.5);
            backdrop-filter: blur(10px);
            border: 1px solid rgba(59, 130, 246, 0.3);
            border-radius: 24px;
            transition: all 0.3s ease;
        }
        
        .glass-card:hover {
            border-color: rgba(59, 130, 246, 0.6);
            transform: translateY(-5px);
        }
        
        .gradient-button {
            background: linear-gradient(45deg, #3b82f6, #8b5cf6);
            color: white;
            text-decoration: none;
            border-radius: 16px;
            font-weight: 700;
            transition: all 0.3s ease;
            border: none;
            cursor: pointer;
        }
        
        .gradient-button:hover {
            transform: translateY(-3px);
            box-shadow: 0 20px 40px rgba(59, 130, 246, 0.4);
        }
        
        .stats-card {
            background: rgba(30, 41, 59, 0.3);
            border: 1px solid rgba(59, 130, 246, 0.2);
            border-radius: 16px;
            padding: 30px;
            text-align: center;
            transition: all 0.3s ease;
        }
        
        .stats-card:hover {
            border-color: rgba(59, 130, 246, 0.5);
            transform: translateY(-3px);
        }
        
        .package-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
            gap: 25px;
        }
        
        .platform-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(280px, 1fr));
            gap: 30px;
        }
        
        .code-block {
            background: #0f172a;
            border-radius: 12px;
            padding: 20px;
            font-family: 'Monaco', 'Consolas', monospace;
            color: #94a3b8;
            font-size: 1.1rem;
        }
        
        .comparison-bad {
            background: linear-gradient(45deg, #ef4444, #f97316);
            border-radius: 50%;
            width: 80px;
            height: 80px;
            display: flex;
            align-items: center;
            justify-content: center;
            margin: 0 auto 20px;
            font-size: 2rem;
            color: white;
        }
        
        .comparison-good {
            background: linear-gradient(45deg, #3b82f6, #8b5cf6);
            border-radius: 50%;
            width: 80px;
            height: 80px;
            display: flex;
            align-items: center;
            justify-content: center;
            margin: 0 auto 20px;
            font-size: 2rem;
        }
    </style>
    """

def create_download_page():
    release = get_latest_release()
    
    # Get version and date info
    version = release['tag_name'] if release and 'tag_name' in release else 'latest'
    release_date = datetime.fromisoformat(release['published_at'].replace('Z', '+00:00')).strftime('%B %d, %Y') if release and 'published_at' in release else 'Recently'
    
    # Create comprehensive download page with contextlite.com styling
    return f"""
    {get_contextlite_css()}
    
    <div class="contextlite-container">
        <!-- Hero Section -->
        <div style="text-align: center; padding: 80px 20px 60px; max-width: 1200px; margin: 0 auto;">
            <h1 style="font-size: 4rem; font-weight: 800; margin-bottom: 30px; line-height: 1.1;" class="hero-gradient">
                The RAG Revolution Was a Mistake
            </h1>
            <h2 style="font-size: 2.5rem; font-weight: 700; color: #3b82f6; margin-bottom: 30px;">
                Download ContextLite {version}
            </h2>
            <p style="font-size: 1.4rem; color: #94a3b8; margin-bottom: 20px; max-width: 900px; margin-left: auto; margin-right: auto; line-height: 1.4;">
                Replace expensive vector databases with <strong style="color: #3b82f6;">mathematically optimal</strong> context selection. 
                Get provably perfect results in <strong style="color: #06b6d4;">0.3ms</strong> instead of 50ms guesswork.
            </p>
            <p style="font-size: 1.2rem; color: #64748b; margin-bottom: 30px;">
                Released {release_date} • SMT-optimized • 100% Local • Zero Dependencies
            </p>
            
            <!-- Performance Stats -->
            <div style="display: flex; justify-content: center; gap: 60px; margin: 40px 0; flex-wrap: wrap;">
                <div style="text-align: center;">
                    <div style="font-size: 3rem; font-weight: 800; color: #3b82f6;">0.3ms</div>
                    <div style="color: #94a3b8; font-size: 1.1rem;">Query Time</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 3rem; font-weight: 800; color: #8b5cf6;">2,406</div>
                    <div style="color: #94a3b8; font-size: 1.1rem;">Files/Second</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 3rem; font-weight: 800; color: #06b6d4;">100x</div>
                    <div style="color: #94a3b8; font-size: 1.1rem;">Faster</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 3rem; font-weight: 800; color: #10b981;">$0</div>
                    <div style="color: #94a3b8; font-size: 1.1rem;">Monthly Cost</div>
                </div>
            </div>
        </div>
        
        <!-- All Distribution Channels -->
        <div style="max-width: 1200px; margin: 0 auto; padding: 0 20px 40px;">
            <div class="glass-card" style="padding: 50px; margin-bottom: 40px;">
                <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">🔗 All Distribution Channels</h2>
                <p style="text-align: center; color: #94a3b8; margin-bottom: 40px; font-size: 1.2rem;">
                    Choose your preferred installation method - we're available everywhere developers work
                </p>
                
                <div class="package-grid">
                    <a href="https://huggingface.co/spaces/MikeKuykendall/contextlite-download" 
                       style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(255, 165, 0, 0.3); border-radius: 16px; padding: 30px; text-decoration: none; color: white; display: block; transition: all 0.3s ease;"
                       onmouseover="this.style.borderColor='rgba(255, 165, 0, 0.6)'; this.style.transform='translateY(-3px)'"
                       onmouseout="this.style.borderColor='rgba(255, 165, 0, 0.3)'; this.style.transform='translateY(0)'">
                        <div style="font-size: 3rem; margin-bottom: 15px; text-align: center;">🤗</div>
                        <h3 style="color: #ff8c00; font-size: 1.5rem; margin-bottom: 15px; text-align: center;">HuggingFace</h3>
                        <p style="color: #94a3b8; text-align: center; margin: 0;">Interactive download with platform detection</p>
                    </a>
                    
                    <a href="https://hub.docker.com/r/makuykendall/contextlite" 
                       style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(0, 123, 255, 0.3); border-radius: 16px; padding: 30px; text-decoration: none; color: white; display: block; transition: all 0.3s ease;"
                       onmouseover="this.style.borderColor='rgba(0, 123, 255, 0.6)'; this.style.transform='translateY(-3px)'"
                       onmouseout="this.style.borderColor='rgba(0, 123, 255, 0.3)'; this.style.transform='translateY(0)'">
                        <div style="font-size: 3rem; margin-bottom: 15px; text-align: center;">🐳</div>
                        <h3 style="color: #007bff; font-size: 1.5rem; margin-bottom: 15px; text-align: center;">Docker Hub</h3>
                        <div class="code-block" style="margin-bottom: 15px; text-align: center;">
                            docker pull makuykendall/contextlite
                        </div>
                        <p style="color: #94a3b8; text-align: center; margin: 0;">Production-ready containers</p>
                    </a>
                    
                    <a href="https://www.npmjs.com/package/contextlite" 
                       style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(203, 56, 55, 0.3); border-radius: 16px; padding: 30px; text-decoration: none; color: white; display: block; transition: all 0.3s ease;"
                       onmouseover="this.style.borderColor='rgba(203, 56, 55, 0.6)'; this.style.transform='translateY(-3px)'"
                       onmouseout="this.style.borderColor='rgba(203, 56, 55, 0.3)'; this.style.transform='translateY(0)'">
                        <div style="font-size: 3rem; margin-bottom: 15px; text-align: center;">📦</div>
                        <h3 style="color: #cb3837; font-size: 1.5rem; margin-bottom: 15px; text-align: center;">npm</h3>
                        <div class="code-block" style="margin-bottom: 15px; text-align: center;">
                            npm install -g contextlite
                        </div>
                        <p style="color: #94a3b8; text-align: center; margin: 0;">Node.js global installation</p>
                    </a>
                    
                    <a href="https://community.chocolatey.org/packages/contextlite" 
                       style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(139, 69, 19, 0.3); border-radius: 16px; padding: 30px; text-decoration: none; color: white; display: block; transition: all 0.3s ease;"
                       onmouseover="this.style.borderColor='rgba(139, 69, 19, 0.6)'; this.style.transform='translateY(-3px)'"
                       onmouseout="this.style.borderColor='rgba(139, 69, 19, 0.3)'; this.style.transform='translateY(0)'">
                        <div style="font-size: 3rem; margin-bottom: 15px; text-align: center;">🍫</div>
                        <h3 style="color: #8b4513; font-size: 1.5rem; margin-bottom: 15px; text-align: center;">Chocolatey</h3>
                        <div class="code-block" style="margin-bottom: 15px; text-align: center;">
                            choco install contextlite
                        </div>
                        <p style="color: #94a3b8; text-align: center; margin: 0;">Windows package manager</p>
                    </a>
                    
                    <a href="https://pypi.org/project/contextlite/" 
                       style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(59, 130, 246, 0.3); border-radius: 16px; padding: 30px; text-decoration: none; color: white; display: block; transition: all 0.3s ease;"
                       onmouseover="this.style.borderColor='rgba(59, 130, 246, 0.6)'; this.style.transform='translateY(-3px)'"
                       onmouseout="this.style.borderColor='rgba(59, 130, 246, 0.3)'; this.style.transform='translateY(0)'">
                        <div style="font-size: 3rem; margin-bottom: 15px; text-align: center;">🐍</div>
                        <h3 style="color: #3776ab; font-size: 1.5rem; margin-bottom: 15px; text-align: center;">PyPI</h3>
                        <div class="code-block" style="margin-bottom: 15px; text-align: center;">
                            pip install contextlite
                        </div>
                        <p style="color: #94a3b8; text-align: center; margin: 0;">Python package with wrapper</p>
                    </a>
                    
                    <a href="https://crates.io/crates/contextlite-client" 
                       style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(222, 165, 132, 0.3); border-radius: 16px; padding: 30px; text-decoration: none; color: white; display: block; transition: all 0.3s ease;"
                       onmouseover="this.style.borderColor='rgba(222, 165, 132, 0.6)'; this.style.transform='translateY(-3px)'"
                       onmouseout="this.style.borderColor='rgba(222, 165, 132, 0.3)'; this.style.transform='translateY(0)'">
                        <div style="font-size: 3rem; margin-bottom: 15px; text-align: center;">🦀</div>
                        <h3 style="color: #dea584; font-size: 1.5rem; margin-bottom: 15px; text-align: center;">Crates.io</h3>
                        <div class="code-block" style="margin-bottom: 15px; text-align: center;">
                            cargo install contextlite-client
                        </div>
                        <p style="color: #94a3b8; text-align: center; margin: 0;">Rust native bindings</p>
                    </a>
                    
                    <a href="https://marketplace.visualstudio.com/items?itemName=ContextLite.contextlite" 
                       style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(0, 120, 215, 0.3); border-radius: 16px; padding: 30px; text-decoration: none; color: white; display: block; transition: all 0.3s ease;"
                       onmouseover="this.style.borderColor='rgba(0, 120, 215, 0.6)'; this.style.transform='translateY(-3px)'"
                       onmouseout="this.style.borderColor='rgba(0, 120, 215, 0.3)'; this.style.transform='translateY(0)'">
                        <div style="font-size: 3rem; margin-bottom: 15px; text-align: center;">🔧</div>
                        <h3 style="color: #0078d7; font-size: 1.5rem; margin-bottom: 15px; text-align: center;">VS Code</h3>
                        <p style="color: #94a3b8; text-align: center; margin: 0;">IDE integration with server management</p>
                    </a>
                    
                    <a href="https://contextlite.com" 
                       style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(59, 130, 246, 0.3); border-radius: 16px; padding: 30px; text-decoration: none; color: white; display: block; transition: all 0.3s ease;"
                       onmouseover="this.style.borderColor='rgba(59, 130, 246, 0.6)'; this.style.transform='translateY(-3px)'"
                       onmouseout="this.style.borderColor='rgba(59, 130, 246, 0.3)'; this.style.transform='translateY(0)'">
                        <div style="font-size: 3rem; margin-bottom: 15px; text-align: center;">🏠</div>
                        <h3 style="color: #3b82f6; font-size: 1.5rem; margin-bottom: 15px; text-align: center;">Official Website</h3>
                        <p style="color: #94a3b8; text-align: center; margin: 0;">Documentation, pricing, and support</p>
                    </a>
                </div>
            </div>
            
            <!-- Direct Download Section -->
            <div class="glass-card" style="padding: 50px; margin-bottom: 40px;">
                <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">⬇️ Direct Downloads</h2>
                <p style="text-align: center; color: #94a3b8; margin-bottom: 40px; font-size: 1.2rem;">
                    Platform-specific binaries from GitHub Releases - zero dependencies, maximum performance
                </p>
                
                <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 30px;">
                    {generate_download_cards(release)}
                </div>
            </div>
            
            <!-- ContextLite vs Vector DBs Comparison -->
            <div class="glass-card" style="padding: 50px; margin-bottom: 40px;">
                <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">🚀 Why ContextLite?</h2>
                
                <div style="display: grid; grid-template-columns: 1fr 1fr; gap: 40px; margin-bottom: 40px;">
                    <div>
                        <h3 style="color: #ef4444; font-size: 1.8rem; margin-bottom: 20px; text-align: center;">❌ Vector Databases</h3>
                        <ul style="color: #94a3b8; font-size: 1.1rem; line-height: 1.8; list-style: none; padding: 0;">
                            <li style="margin-bottom: 10px;">🐌 50ms+ query latency</li>
                            <li style="margin-bottom: 10px;">💸 $100-500+ monthly hosting</li>
                            <li style="margin-bottom: 10px;">🎲 Approximate similarity matching</li>
                            <li style="margin-bottom: 10px;">📈 Complex scaling requirements</li>
                            <li style="margin-bottom: 10px;">🔧 Heavy infrastructure overhead</li>
                            <li style="margin-bottom: 10px;">🌐 Network dependency required</li>
                        </ul>
                    </div>
                    
                    <div>
                        <h3 style="color: #10b981; font-size: 1.8rem; margin-bottom: 20px; text-align: center;">✅ ContextLite</h3>
                        <ul style="color: #94a3b8; font-size: 1.1rem; line-height: 1.8; list-style: none; padding: 0;">
                            <li style="margin-bottom: 10px;">⚡ 0.3ms query time (100x faster)</li>
                            <li style="margin-bottom: 10px;">💰 $0 operational costs</li>
                            <li style="margin-bottom: 10px;">🎯 Mathematically optimal selection</li>
                            <li style="margin-bottom: 10px;">📊 Linear scaling with file count</li>
                            <li style="margin-bottom: 10px;">🪶 Single binary, zero dependencies</li>
                            <li style="margin-bottom: 10px;">🔒 100% local processing</li>
                        </ul>
                    </div>
                </div>
            </div>
            
            <!-- SMT Optimization Deep Dive -->
            <div class="glass-card" style="padding: 50px; margin-bottom: 40px;">
                <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">🧠 SMT-Powered Intelligence</h2>
                <p style="text-align: center; color: #94a3b8; margin-bottom: 40px; font-size: 1.2rem;">
                    While others guess with vectors, we prove with mathematics
                </p>
                
                <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(350px, 1fr)); gap: 30px;">
                    <div class="stats-card" style="padding: 30px; text-align: center;">
                        <div style="font-size: 3rem; margin-bottom: 20px;">🔬</div>
                        <h3 style="color: #3b82f6; font-size: 1.5rem; margin-bottom: 15px;">Satisfiability Modulo Theories</h3>
                        <p style="color: #94a3b8; line-height: 1.6;">
                            Uses Z3 theorem prover to find mathematically optimal context combinations instead of approximate similarity
                        </p>
                    </div>
                    
                    <div class="stats-card" style="padding: 30px; text-align: center;">
                        <div style="font-size: 3rem; margin-bottom: 20px;">⚡</div>
                        <h3 style="color: #8b5cf6; font-size: 1.5rem; margin-bottom: 15px;">Multi-Stage Pipeline</h3>
                        <p style="color: #94a3b8; line-height: 1.6;">
                            BM25 pre-filtering + SMT optimization ensures both speed and mathematical precision
                        </p>
                    </div>
                    
                    <div class="stats-card" style="padding: 30px; text-align: center;">
                        <div style="font-size: 3rem; margin-bottom: 20px;">🎯</div>
                        <h3 style="color: #06b6d4; font-size: 1.5rem; margin-bottom: 15px;">Constraint-Based Selection</h3>
                        <p style="color: #94a3b8; line-height: 1.6;">
                            Token limits, relevance thresholds, and dependency analysis as formal constraints
                        </p>
                    </div>
                    
                    <div class="stats-card" style="padding: 30px; text-align: center;">
                        <div style="font-size: 3rem; margin-bottom: 20px;">🏆</div>
                        <h3 style="color: #10b981; font-size: 1.5rem; margin-bottom: 15px;">Provably Optimal</h3>
                        <p style="color: #94a3b8; line-height: 1.6;">
                            When SMT finds a solution, it's mathematically guaranteed to be the best possible
                        </p>
                    </div>
                </div>
            </div>
            
            <!-- Technical Features -->
            <div class="glass-card" style="padding: 50px; margin-bottom: 40px;">
                <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">🛠️ Technical Features</h2>
                
                <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 30px;">
                    <div style="border-left: 4px solid #3b82f6; padding-left: 25px;">
                        <h3 style="color: #3b82f6; font-size: 1.3rem; margin-bottom: 15px;">🌍 Universal Compatibility</h3>
                        <p style="color: #94a3b8; line-height: 1.6;">
                            Works with any programming language, framework, or text format. No vendor lock-in.
                        </p>
                    </div>
                    
                    <div style="border-left: 4px solid #8b5cf6; padding-left: 25px;">
                        <h3 style="color: #8b5cf6; font-size: 1.3rem; margin-bottom: 15px;">📊 Real-Time Analytics</h3>
                        <p style="color: #94a3b8; line-height: 1.6;">
                            Performance metrics, query patterns, and optimization insights via web dashboard.
                        </p>
                    </div>
                    
                    <div style="border-left: 4px solid #06b6d4; padding-left: 25px;">
                        <h3 style="color: #06b6d4; font-size: 1.3rem; margin-bottom: 15px;">🔒 Privacy-First</h3>
                        <p style="color: #94a3b8; line-height: 1.6;">
                            Your code never leaves your machine. No cloud dependencies, no data collection.
                        </p>
                    </div>
                    
                    <div style="border-left: 4px solid #10b981; padding-left: 25px;">
                        <h3 style="color: #10b981; font-size: 1.3rem; margin-bottom: 15px;">⚙️ Intelligent Caching</h3>
                        <p style="color: #94a3b8; line-height: 1.6;">
                            Smart cache invalidation ensures fresh results while maintaining lightning speed.
                        </p>
                    </div>
                </div>
            </div>
            
            <!-- Repository Links -->
            <div class="glass-card" style="padding: 50px; margin-bottom: 40px;">
                <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">📚 Learn More</h2>
                
                <div style="display: flex; justify-content: center; gap: 30px; flex-wrap: wrap;">
                    <a href="https://github.com/Michael-A-Kuykendall/contextlite" class="gradient-button" 
                       style="padding: 20px 30px; text-decoration: none; font-size: 1.2rem; font-weight: 600; border-radius: 12px; transition: all 0.3s ease;">
                        🔗 GitHub Repository
                    </a>
                    <a href="https://contextlite.com/docs" class="gradient-button"
                       style="padding: 20px 30px; text-decoration: none; font-size: 1.2rem; font-weight: 600; border-radius: 12px; transition: all 0.3s ease;">
                        📖 Documentation
                    </a>
                    <a href="https://contextlite.com/purchase" class="gradient-button"
                       style="padding: 20px 30px; text-decoration: none; font-size: 1.2rem; font-weight: 600; border-radius: 12px; transition: all 0.3s ease;">
                        💎 Get Pro License
                    </a>
                </div>
                
                <div style="text-align: center; margin-top: 40px; padding-top: 30px; border-top: 1px solid rgba(255, 255, 255, 0.1);">
                    <p style="color: #64748b; font-size: 1rem;">
                        Made with ❤️ for developers who demand mathematical precision
                    </p>
                </div>
            </div>
        </div>
    </div>
    """
        # Stunning fallback page matching contextlite.com design
        return """
        <div style="background: linear-gradient(135deg, #0f172a 0%, #1e293b 50%, #334155 100%); min-height: 100vh; color: white; font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;">
            <!-- Hero Section -->
            <div style="text-align: center; padding: 80px 20px 60px; max-width: 1200px; margin: 0 auto;">
                <h1 style="font-size: 4rem; font-weight: 800; background: linear-gradient(45deg, #ef4444, #f97316, #eab308); -webkit-background-clip: text; -webkit-text-fill-color: transparent; margin-bottom: 30px; line-height: 1.1;">
                    RAG Systems Were a Mistake
                </h1>
                <h2 style="font-size: 2.5rem; font-weight: 700; color: #3b82f6; margin-bottom: 30px;">
                    Download ContextLite
                </h2>
                <p style="font-size: 1.4rem; color: #94a3b8; margin-bottom: 20px; max-width: 900px; margin-left: auto; margin-right: auto; line-height: 1.4;">
                    Replace approximate vector search with <strong style="color: #3b82f6;">mathematically optimal</strong> context selection. Get provably perfect results in <strong style="color: #06b6d4;">0.3ms</strong> instead of 50ms guesswork.
                </p>
                
                <!-- Performance Stats -->
                <div style="display: flex; justify-content: center; gap: 60px; margin: 40px 0; flex-wrap: wrap;">
                    <div style="text-align: center;">
                        <div style="font-size: 3rem; font-weight: 800; color: #3b82f6;">0.3ms</div>
                        <div style="color: #94a3b8; font-size: 1.1rem;">Query Time</div>
                    </div>
                    <div style="text-align: center;">
                        <div style="font-size: 3rem; font-weight: 800; color: #8b5cf6;">2,406</div>
                        <div style="color: #94a3b8; font-size: 1.1rem;">Files/Second</div>
                    </div>
                    <div style="text-align: center;">
                        <div style="font-size: 3rem; font-weight: 800; color: #06b6d4;">100x</div>
                        <div style="color: #94a3b8; font-size: 1.1rem;">Faster</div>
                    </div>
                </div>
            </div>
            
            <!-- Download Options -->
            <div style="max-width: 1000px; margin: 0 auto; padding: 0 20px 60px;">
                <div style="background: rgba(30, 41, 59, 0.5); backdrop-filter: blur(10px); border: 1px solid rgba(59, 130, 246, 0.3); border-radius: 24px; padding: 50px; margin-bottom: 40px;">
                    <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">📥 Download Options</h2>
                    
                    <!-- Primary Download Button -->
                    <div style="text-align: center; margin-bottom: 40px;">
                        <a href="https://github.com/Michael-A-Kuykendall/contextlite/releases/latest" 
                           style="display: inline-block; background: linear-gradient(45deg, #3b82f6, #8b5cf6); color: white; text-decoration: none; padding: 20px 40px; border-radius: 16px; font-size: 1.3rem; font-weight: 700; box-shadow: 0 10px 25px rgba(59, 130, 246, 0.3); transition: all 0.3s ease; border: none;"
                           onmouseover="this.style.transform='translateY(-5px)'; this.style.boxShadow='0 20px 40px rgba(59, 130, 246, 0.4)'"
                           onmouseout="this.style.transform='translateY(0)'; this.style.boxShadow='0 10px 25px rgba(59, 130, 246, 0.3)'">
                            🚀 Get Latest Release from GitHub
                        </a>
                    </div>
                    
                    <!-- Package Managers -->
                    <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 25px; margin-top: 40px;">
                        <div style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(59, 130, 246, 0.2); border-radius: 16px; padding: 30px; text-align: center; transition: all 0.3s ease;"
                             onmouseover="this.style.borderColor='rgba(59, 130, 246, 0.5)'; this.style.transform='translateY(-3px)'"
                             onmouseout="this.style.borderColor='rgba(59, 130, 246, 0.2)'; this.style.transform='translateY(0)'">
                            <div style="font-size: 3rem; margin-bottom: 15px;">📕</div>
                            <h3 style="color: #ef4444; font-size: 1.5rem; margin-bottom: 15px;">npm</h3>
                            <div style="background: #0f172a; border-radius: 12px; padding: 20px; margin-bottom: 20px;">
                                <code style="color: #94a3b8; font-size: 1.1rem; font-family: 'Monaco', 'Consolas', monospace;">
                                    npm install -g contextlite
                                </code>
                            </div>
                            <p style="color: #64748b; font-size: 0.9rem;">Global installation via npm</p>
                        </div>
                        
                        <div style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(59, 130, 246, 0.2); border-radius: 16px; padding: 30px; text-align: center; transition: all 0.3s ease;"
                             onmouseover="this.style.borderColor='rgba(59, 130, 246, 0.5)'; this.style.transform='translateY(-3px)'"
                             onmouseout="this.style.borderColor='rgba(59, 130, 246, 0.2)'; this.style.transform='translateY(0)'">
                            <div style="font-size: 3rem; margin-bottom: 15px;">🐍</div>
                            <h3 style="color: #3b82f6; font-size: 1.5rem; margin-bottom: 15px;">PyPI</h3>
                            <div style="background: #0f172a; border-radius: 12px; padding: 20px; margin-bottom: 20px;">
                                <code style="color: #94a3b8; font-size: 1.1rem; font-family: 'Monaco', 'Consolas', monospace;">
                                    pip install contextlite
                                </code>
                            </div>
                            <p style="color: #64748b; font-size: 0.9rem;">Python package installation</p>
                        </div>
                    </div>
                </div>
                
                <!-- Features Grid -->
                <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 25px; margin-bottom: 60px;">
                    <div style="background: rgba(30, 41, 59, 0.3); border: 1px solid rgba(59, 130, 246, 0.2); border-radius: 16px; padding: 30px; text-align: center;">
                        <div style="font-size: 3rem; margin-bottom: 15px;">⚡</div>
                        <h3 style="color: #3b82f6; font-size: 1.3rem; margin-bottom: 10px;">Lightning Fast</h3>
                        <p style="color: #94a3b8;">0.3ms average query time - 100x faster than vector databases</p>
                    </div>
                    
                    <div style="background: rgba(30, 41, 59, 0.3); border: 1px solid rgba(139, 92, 246, 0.2); border-radius: 16px; padding: 30px; text-align: center;">
                        <div style="font-size: 3rem; margin-bottom: 15px;">🔒</div>
                        <h3 style="color: #8b5cf6; font-size: 1.3rem; margin-bottom: 10px;">Privacy First</h3>
                        <p style="color: #94a3b8;">All processing happens locally - your data never leaves your machine</p>
                    </div>
                    
                    <div style="background: rgba(30, 41, 59, 0.3); border: 1px solid rgba(6, 182, 212, 0.2); border-radius: 16px; padding: 30px; text-align: center;">
                        <div style="font-size: 3rem; margin-bottom: 15px;">🎯</div>
                        <h3 style="color: #06b6d4; font-size: 1.3rem; margin-bottom: 10px;">Perfect Precision</h3>
                        <p style="color: #94a3b8;">Mathematical optimization ensures you get the right context every time</p>
                    </div>
                </div>
                
                <!-- Quick Start -->
                <div style="background: rgba(30, 41, 59, 0.5); backdrop-filter: blur(10px); border: 1px solid rgba(59, 130, 246, 0.3); border-radius: 24px; padding: 50px; margin-bottom: 40px;">
                    <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">🚀 Quick Start Guide</h2>
                    
                    <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(280px, 1fr)); gap: 30px;">
                        <div style="background: rgba(15, 23, 42, 0.8); border-radius: 16px; padding: 30px;">
                            <h3 style="color: #3b82f6; font-size: 1.5rem; margin-bottom: 20px; display: flex; align-items: center; gap: 10px;">
                                <span>🖥️</span> Windows
                            </h3>
                            <ol style="color: #94a3b8; line-height: 1.8; padding-left: 20px; margin: 0;">
                                <li>Download the Windows executable</li>
                                <li>Extract the archive</li>
                                <li>Run <code style="background: rgba(59, 130, 246, 0.2); padding: 4px 8px; border-radius: 6px; color: #3b82f6;">contextlite.exe</code></li>
                                <li><strong style="color: #8b5cf6;">Start your 14-day trial!</strong></li>
                            </ol>
                        </div>
                        
                        <div style="background: rgba(15, 23, 42, 0.8); border-radius: 16px; padding: 30px;">
                            <h3 style="color: #8b5cf6; font-size: 1.5rem; margin-bottom: 20px; display: flex; align-items: center; gap: 10px;">
                                <span>🍎</span> macOS
                            </h3>
                            <ol style="color: #94a3b8; line-height: 1.8; padding-left: 20px; margin: 0;">
                                <li>Download the macOS archive</li>
                                <li><code style="background: rgba(139, 92, 246, 0.2); padding: 4px 8px; border-radius: 6px; color: #8b5cf6;">tar -xzf contextlite-*.tar.gz</code></li>
                                <li><code style="background: rgba(139, 92, 246, 0.2); padding: 4px 8px; border-radius: 6px; color: #8b5cf6;">chmod +x contextlite</code></li>
                                <li><code style="background: rgba(139, 92, 246, 0.2); padding: 4px 8px; border-radius: 6px; color: #8b5cf6;">./contextlite</code></li>
                            </ol>
                        </div>
                        
                        <div style="background: rgba(15, 23, 42, 0.8); border-radius: 16px; padding: 30px;">
                            <h3 style="color: #06b6d4; font-size: 1.5rem; margin-bottom: 20px; display: flex; align-items: center; gap: 10px;">
                                <span>🐧</span> Linux
                            </h3>
                            <ol style="color: #94a3b8; line-height: 1.8; padding-left: 20px; margin: 0;">
                                <li>Download the Linux archive</li>
                                <li><code style="background: rgba(6, 182, 212, 0.2); padding: 4px 8px; border-radius: 6px; color: #06b6d4;">tar -xzf contextlite-*.tar.gz</code></li>
                                <li><code style="background: rgba(6, 182, 212, 0.2); padding: 4px 8px; border-radius: 6px; color: #06b6d4;">chmod +x contextlite</code></li>
                                <li><code style="background: rgba(6, 182, 212, 0.2); padding: 4px 8px; border-radius: 6px; color: #06b6d4;">./contextlite</code></li>
                            </ol>
                        </div>
                    </div>
                </div>
                
                <!-- Navigation Links -->
                <div style="text-align: center; margin-bottom: 40px;">
                    <div style="display: flex; justify-content: center; gap: 20px; flex-wrap: wrap;">
                        <a href="https://github.com/Michael-A-Kuykendall/contextlite/wiki" 
                           style="background: rgba(59, 130, 246, 0.1); border: 1px solid rgba(59, 130, 246, 0.3); color: #3b82f6; padding: 15px 25px; border-radius: 12px; text-decoration: none; display: flex; align-items: center; gap: 10px; transition: all 0.3s ease;"
                           onmouseover="this.style.background='rgba(59, 130, 246, 0.2)'; this.style.borderColor='rgba(59, 130, 246, 0.5)'"
                           onmouseout="this.style.background='rgba(59, 130, 246, 0.1)'; this.style.borderColor='rgba(59, 130, 246, 0.3)'">
                            📚 Documentation
                        </a>
                        <a href="https://github.com/Michael-A-Kuykendall/contextlite" 
                           style="background: rgba(139, 92, 246, 0.1); border: 1px solid rgba(139, 92, 246, 0.3); color: #8b5cf6; padding: 15px 25px; border-radius: 12px; text-decoration: none; display: flex; align-items: center; gap: 10px; transition: all 0.3s ease;"
                           onmouseover="this.style.background='rgba(139, 92, 246, 0.2)'; this.style.borderColor='rgba(139, 92, 246, 0.5)'"
                           onmouseout="this.style.background='rgba(139, 92, 246, 0.1)'; this.style.borderColor='rgba(139, 92, 246, 0.3)'">
                            ⚡ GitHub
                        </a>
                        <a href="https://contextlite.com" 
                           style="background: linear-gradient(45deg, #3b82f6, #8b5cf6); color: white; padding: 15px 25px; border-radius: 12px; text-decoration: none; display: flex; align-items: center; gap: 10px; transition: all 0.3s ease; border: none;"
                           onmouseover="this.style.transform='translateY(-2px)'; this.style.boxShadow='0 10px 25px rgba(59, 130, 246, 0.3)'"
                           onmouseout="this.style.transform='translateY(0)'; this.style.boxShadow='none'">
                            🏠 Homepage
                        </a>
                    </div>
                </div>
                
                <!-- Why ContextLite Section -->
                <div style="background: rgba(30, 41, 59, 0.5); backdrop-filter: blur(10px); border: 1px solid rgba(59, 130, 246, 0.3); border-radius: 24px; padding: 50px;">
                    <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">Why ContextLite?</h2>
                    
                    <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); gap: 30px;">
                        <div style="text-align: center;">
                            <div style="background: linear-gradient(45deg, #ef4444, #f97316); border-radius: 50%; width: 80px; height: 80px; display: flex; align-items: center; justify-content: center; margin: 0 auto 20px; font-size: 2rem; color: white;">❌</div>
                            <h3 style="color: #ef4444; margin-bottom: 15px;">Vector DBs</h3>
                            <p style="color: #94a3b8; font-size: 0.9rem;">30-50ms latency<br/>$300-500/month<br/>Approximate results</p>
                        </div>
                        
                        <div style="text-align: center;">
                            <div style="background: linear-gradient(45deg, #3b82f6, #8b5cf6); border-radius: 50%; width: 80px; height: 80px; display: flex; align-items: center; justify-content: center; margin: 0 auto 20px; font-size: 2rem;">✅</div>
                            <h3 style="color: #3b82f6; margin-bottom: 15px;">ContextLite</h3>
                            <p style="color: #94a3b8; font-size: 0.9rem;">0.3ms latency<br/>$0/month<br/>Mathematically optimal</p>
                        </div>
                    </div>
                </div>
            </div>
            
            <!-- Footer -->
            <div style="border-top: 1px solid rgba(59, 130, 246, 0.2); padding: 40px 20px; text-align: center; color: #64748b;">
                <p style="margin: 0; font-size: 1.1rem;">
                    Made with ❤️ for developers who demand <strong style="color: #3b82f6;">perfect precision</strong>
                </p>
            </div>
        </div>
        """
    
    # Build beautiful download cards with consistent styling
    download_cards = ""
    for asset in release['assets']:
        platform = "Windows" if "windows" in asset['name'].lower() or "win" in asset['name'].lower() else \
                  "macOS" if "darwin" in asset['name'].lower() or "macos" in asset['name'].lower() else \
                  "Linux"
        
        icon = "🖥️" if platform == "Windows" else "🍎" if platform == "macOS" else "🐧"
        gradient_color = "#3b82f6" if platform == "Windows" else "#8b5cf6" if platform == "macOS" else "#06b6d4"
        
        download_cards += f"""
            <div style="background: rgba(30, 41, 59, 0.5); backdrop-filter: blur(10px); border: 1px solid rgba(59, 130, 246, 0.3); border-radius: 20px; padding: 30px; text-align: center; transition: all 0.3s ease;"
                 onmouseover="this.style.borderColor='rgba(59, 130, 246, 0.6)'; this.style.transform='translateY(-5px)'"
                 onmouseout="this.style.borderColor='rgba(59, 130, 246, 0.3)'; this.style.transform='translateY(0)'">
                <div style="font-size: 4rem; margin-bottom: 20px;">{icon}</div>
                <h3 style="color: {gradient_color}; font-size: 1.8rem; margin-bottom: 15px; font-weight: 700;">{platform}</h3>
                <p style="color: #94a3b8; margin-bottom: 25px; font-size: 1rem;">
                    {format_file_size(asset['size'])} • {asset['name'].split('.')[-1].upper()} Archive
                </p>
                <a href="{asset['browser_download_url']}" 
                   style="display: inline-block; background: linear-gradient(45deg, {gradient_color}, #8b5cf6); color: white; text-decoration: none; padding: 18px 35px; border-radius: 12px; font-size: 1.2rem; font-weight: 700; box-shadow: 0 8px 20px rgba(59, 130, 246, 0.3); transition: all 0.3s ease; border: none;"
                   onmouseover="this.style.transform='translateY(-3px)'; this.style.boxShadow='0 12px 30px rgba(59, 130, 246, 0.4)'"
                   onmouseout="this.style.transform='translateY(0)'; this.style.boxShadow='0 8px 20px rgba(59, 130, 246, 0.3)'">
                    📥 Download for {platform}
                </a>
                <p style="margin: 15px 0 0 0; font-size: 0.85rem; color: #64748b; word-break: break-all;">
                    {asset['name']}
                </p>
            </div>
        """
    
    # Create beautiful success page with professional styling
    return f"""
    <div style="background: linear-gradient(135deg, #0f172a 0%, #1e293b 50%, #334155 100%); min-height: 100vh; color: white; font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;">
        <!-- Hero Section -->
        <div style="text-align: center; padding: 60px 20px 40px; max-width: 1200px; margin: 0 auto;">
            <h1 style="font-size: 3.5rem; font-weight: 800; background: linear-gradient(45deg, #ef4444, #f97316, #eab308); -webkit-background-clip: text; -webkit-text-fill-color: transparent; margin-bottom: 20px; line-height: 1.1;">
                RAG Systems Were a Mistake
            </h1>
            <h2 style="font-size: 2.5rem; font-weight: 700; color: #3b82f6; margin-bottom: 20px;">
                Download ContextLite {version}
            </h2>
            <p style="font-size: 1.3rem; color: #94a3b8; margin-bottom: 15px;">
                Released {release_date} • <strong style="color: #3b82f6;">100x faster</strong> than vector databases
            </p>
            <p style="font-size: 1.2rem; color: #64748b; margin-bottom: 30px; max-width: 800px; margin-left: auto; margin-right: auto;">
                Get mathematically optimal context selection instead of approximate vector search guesswork.
            </p>
            
            <!-- Performance Stats -->
            <div style="display: flex; justify-content: center; gap: 50px; margin: 30px 0; flex-wrap: wrap;">
                <div style="text-align: center;">
                    <div style="font-size: 2.5rem; font-weight: 800; color: #3b82f6;">0.3ms</div>
                    <div style="color: #94a3b8;">Query Time</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 2.5rem; font-weight: 800; color: #8b5cf6;">2,406</div>
                    <div style="color: #94a3b8;">Files/Second</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 2.5rem; font-weight: 800; color: #06b6d4;">100x</div>
                    <div style="color: #94a3b8;">Faster</div>
                </div>
            </div>
        </div>
        
        <!-- Download Cards -->
        <div style="max-width: 1200px; margin: 0 auto; padding: 0 20px 60px;">
            <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(350px, 1fr)); gap: 25px; margin-bottom: 50px;">
                {download_cards}
            </div>
            
            <!-- Installation Instructions -->
            <div style="background: rgba(30, 41, 59, 0.5); backdrop-filter: blur(10px); border: 1px solid rgba(59, 130, 246, 0.3); border-radius: 24px; padding: 50px; margin-bottom: 40px;">
                <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">🚀 Quick Start Guide</h2>
                
                <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(280px, 1fr)); gap: 30px;">
                    <div style="background: rgba(15, 23, 42, 0.8); border-radius: 16px; padding: 30px;">
                        <h3 style="color: #3b82f6; font-size: 1.5rem; margin-bottom: 20px; display: flex; align-items: center; gap: 10px;">
                            <span>🖥️</span> Windows
                        </h3>
                        <ol style="color: #94a3b8; line-height: 1.8; padding-left: 20px; margin: 0;">
                            <li>Download the Windows executable</li>
                            <li>Extract the archive</li>
                            <li>Run <code style="background: rgba(59, 130, 246, 0.2); padding: 4px 8px; border-radius: 6px; color: #3b82f6;">contextlite.exe</code></li>
                            <li><strong style="color: #8b5cf6;">Start your 14-day trial!</strong></li>
                        </ol>
                    </div>
                    
                    <div style="background: rgba(15, 23, 42, 0.8); border-radius: 16px; padding: 30px;">
                        <h3 style="color: #8b5cf6; font-size: 1.5rem; margin-bottom: 20px; display: flex; align-items: center; gap: 10px;">
                            <span>🍎</span> macOS
                        </h3>
                        <ol style="color: #94a3b8; line-height: 1.8; padding-left: 20px; margin: 0;">
                            <li>Download the macOS archive</li>
                            <li><code style="background: rgba(139, 92, 246, 0.2); padding: 4px 8px; border-radius: 6px; color: #8b5cf6;">tar -xzf contextlite-*.tar.gz</code></li>
                            <li><code style="background: rgba(139, 92, 246, 0.2); padding: 4px 8px; border-radius: 6px; color: #8b5cf6;">chmod +x contextlite</code></li>
                            <li><code style="background: rgba(139, 92, 246, 0.2); padding: 4px 8px; border-radius: 6px; color: #8b5cf6;">./contextlite</code></li>
                        </ol>
                    </div>
                    
                    <div style="background: rgba(15, 23, 42, 0.8); border-radius: 16px; padding: 30px;">
                        <h3 style="color: #06b6d4; font-size: 1.5rem; margin-bottom: 20px; display: flex; align-items: center; gap: 10px;">
                            <span>🐧</span> Linux
                        </h3>
                        <ol style="color: #94a3b8; line-height: 1.8; padding-left: 20px; margin: 0;">
                            <li>Download the Linux archive</li>
                            <li><code style="background: rgba(6, 182, 212, 0.2); padding: 4px 8px; border-radius: 6px; color: #06b6d4;">tar -xzf contextlite-*.tar.gz</code></li>
                            <li><code style="background: rgba(6, 182, 212, 0.2); padding: 4px 8px; border-radius: 6px; color: #06b6d4;">chmod +x contextlite</code></li>
                            <li><code style="background: rgba(6, 182, 212, 0.2); padding: 4px 8px; border-radius: 6px; color: #06b6d4;">./contextlite</code></li>
                        </ol>
                    </div>
                </div>
            </div>
            
            <!-- Package Managers -->
            <div style="background: rgba(30, 41, 59, 0.5); backdrop-filter: blur(10px); border: 1px solid rgba(59, 130, 246, 0.3); border-radius: 24px; padding: 50px; margin-bottom: 40px;">
                <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">📦 Package Managers</h2>
                
                <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 25px;">
                    <div style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(59, 130, 246, 0.2); border-radius: 16px; padding: 30px; text-align: center; transition: all 0.3s ease;"
                         onmouseover="this.style.borderColor='rgba(59, 130, 246, 0.5)'; this.style.transform='translateY(-3px)'"
                         onmouseout="this.style.borderColor='rgba(59, 130, 246, 0.2)'; this.style.transform='translateY(0)'">
                        <div style="font-size: 3rem; margin-bottom: 15px;">📕</div>
                        <h3 style="color: #ef4444; font-size: 1.5rem; margin-bottom: 15px;">npm</h3>
                        <div style="background: #0f172a; border-radius: 12px; padding: 20px; margin-bottom: 20px;">
                            <code style="color: #94a3b8; font-size: 1.1rem; font-family: 'Monaco', 'Consolas', monospace;">
                                npm install -g contextlite
                            </code>
                        </div>
                        <p style="color: #64748b; font-size: 0.9rem;">Global installation via npm</p>
                    </div>
                    
                    <div style="background: linear-gradient(135deg, #1e293b, #334155); border: 1px solid rgba(59, 130, 246, 0.2); border-radius: 16px; padding: 30px; text-align: center; transition: all 0.3s ease;"
                         onmouseover="this.style.borderColor='rgba(59, 130, 246, 0.5)'; this.style.transform='translateY(-3px)'"
                         onmouseout="this.style.borderColor='rgba(59, 130, 246, 0.2)'; this.style.transform='translateY(0)'">
                        <div style="font-size: 3rem; margin-bottom: 15px;">🐍</div>
                        <h3 style="color: #3b82f6; font-size: 1.5rem; margin-bottom: 15px;">PyPI</h3>
                        <div style="background: #0f172a; border-radius: 12px; padding: 20px; margin-bottom: 20px;">
                            <code style="color: #94a3b8; font-size: 1.1rem; font-family: 'Monaco', 'Consolas', monospace;">
                                pip install contextlite
                            </code>
                        </div>
                        <p style="color: #64748b; font-size: 0.9rem;">Python package installation</p>
                    </div>
                </div>
            </div>
            
            <!-- Features Highlight -->
            <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 25px; margin-bottom: 50px;">
                <div style="background: rgba(30, 41, 59, 0.3); border: 1px solid rgba(59, 130, 246, 0.2); border-radius: 16px; padding: 30px; text-align: center;">
                    <div style="font-size: 3rem; margin-bottom: 15px;">⚡</div>
                    <h3 style="color: #3b82f6; font-size: 1.3rem; margin-bottom: 10px;">Lightning Fast</h3>
                    <p style="color: #94a3b8;">0.3ms average query time - 100x faster than vector databases</p>
                </div>
                
                <div style="background: rgba(30, 41, 59, 0.3); border: 1px solid rgba(139, 92, 246, 0.2); border-radius: 16px; padding: 30px; text-align: center;">
                    <div style="font-size: 3rem; margin-bottom: 15px;">🔒</div>
                    <h3 style="color: #8b5cf6; font-size: 1.3rem; margin-bottom: 10px;">Privacy First</h3>
                    <p style="color: #94a3b8;">All processing happens locally - your data never leaves your machine</p>
                </div>
                
                <div style="background: rgba(30, 41, 59, 0.3); border: 1px solid rgba(6, 182, 212, 0.2); border-radius: 16px; padding: 30px; text-align: center;">
                    <div style="font-size: 3rem; margin-bottom: 15px;">🎯</div>
                    <h3 style="color: #06b6d4; font-size: 1.3rem; margin-bottom: 10px;">Perfect Precision</h3>
                    <p style="color: #94a3b8;">Mathematical optimization ensures you get the right context every time</p>
                </div>
            </div>
            
            <!-- Navigation Links -->
            <div style="text-align: center; margin-bottom: 40px;">
                <div style="display: flex; justify-content: center; gap: 20px; flex-wrap: wrap;">
                    <a href="https://github.com/Michael-A-Kuykendall/contextlite/wiki" 
                       style="background: rgba(59, 130, 246, 0.1); border: 1px solid rgba(59, 130, 246, 0.3); color: #3b82f6; padding: 15px 25px; border-radius: 12px; text-decoration: none; display: flex; align-items: center; gap: 10px; transition: all 0.3s ease;"
                       onmouseover="this.style.background='rgba(59, 130, 246, 0.2)'; this.style.borderColor='rgba(59, 130, 246, 0.5)'"
                       onmouseout="this.style.background='rgba(59, 130, 246, 0.1)'; this.style.borderColor='rgba(59, 130, 246, 0.3)'">
                        📚 Documentation
                    </a>
                    <a href="https://github.com/Michael-A-Kuykendall/contextlite" 
                       style="background: rgba(139, 92, 246, 0.1); border: 1px solid rgba(139, 92, 246, 0.3); color: #8b5cf6; padding: 15px 25px; border-radius: 12px; text-decoration: none; display: flex; align-items: center; gap: 10px; transition: all 0.3s ease;"
                       onmouseover="this.style.background='rgba(139, 92, 246, 0.2)'; this.style.borderColor='rgba(139, 92, 246, 0.5)'"
                       onmouseout="this.style.background='rgba(139, 92, 246, 0.1)'; this.style.borderColor='rgba(139, 92, 246, 0.3)'">
                        ⚡ GitHub
                    </a>
                    <a href="https://contextlite.com" 
                       style="background: linear-gradient(45deg, #3b82f6, #8b5cf6); color: white; padding: 15px 25px; border-radius: 12px; text-decoration: none; display: flex; align-items: center; gap: 10px; transition: all 0.3s ease; border: none;"
                       onmouseover="this.style.transform='translateY(-2px)'; this.style.boxShadow='0 10px 25px rgba(59, 130, 246, 0.3)'"
                       onmouseout="this.style.transform='translateY(0)'; this.style.boxShadow='none'">
                        🏠 Homepage
                    </a>
                </div>
            </div>
            
            <!-- Why ContextLite Section -->
            <div style="background: rgba(30, 41, 59, 0.5); backdrop-filter: blur(10px); border: 1px solid rgba(59, 130, 246, 0.3); border-radius: 24px; padding: 50px;">
                <h2 style="text-align: center; font-size: 2.5rem; margin-bottom: 40px; color: #f1f5f9;">Why ContextLite?</h2>
                
                <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); gap: 30px;">
                    <div style="text-align: center;">
                        <div style="background: linear-gradient(45deg, #ef4444, #f97316); border-radius: 50%; width: 80px; height: 80px; display: flex; align-items: center; justify-content: center; margin: 0 auto 20px; font-size: 2rem; color: white;">❌</div>
                        <h3 style="color: #ef4444; margin-bottom: 15px;">Vector DBs</h3>
                        <p style="color: #94a3b8; font-size: 0.9rem;">30-50ms latency<br/>$300-500/month<br/>Approximate results</p>
                    </div>
                    
                    <div style="text-align: center;">
                        <div style="background: linear-gradient(45deg, #3b82f6, #8b5cf6); border-radius: 50%; width: 80px; height: 80px; display: flex; align-items: center; justify-content: center; margin: 0 auto 20px; font-size: 2rem;">✅</div>
                        <h3 style="color: #3b82f6; margin-bottom: 15px;">ContextLite</h3>
                        <p style="color: #94a3b8; font-size: 0.9rem;">0.3ms latency<br/>$0/month<br/>Mathematically optimal</p>
                    </div>
                </div>
            </div>
        </div>
        
        <!-- Footer -->
        <div style="border-top: 1px solid rgba(59, 130, 246, 0.2); padding: 40px 20px; text-align: center; color: #64748b;">
            <p style="margin: 0; font-size: 1.1rem;">
                Made with ❤️ for developers who demand <strong style="color: #3b82f6;">perfect precision</strong>
            </p>
        </div>
    </div>
    """
    
    # Package managers HTML section
    package_managers_html = """
        <div style="background: #1f2937; color: white; border-radius: 12px; padding: 30px; margin-bottom: 40px;">
            <h2 style="text-align: center; margin-bottom: 20px;">📦 Package Managers</h2>
            <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 20px;">
                <div style="background: #374151; padding: 20px; border-radius: 8px;">
                    <h3 style="color: #ef4444; margin-bottom: 10px;">📕 npm</h3>
                    <code style="background: #111827; padding: 10px; border-radius: 6px; display: block; color: #f9fafb;">
                        npm install -g contextlite
                    </code>
                </div>
                
                <div style="background: #374151; padding: 20px; border-radius: 8px;">
                    <h3 style="color: #3b82f6; margin-bottom: 10px;">🐍 PyPI</h3>
                    <code style="background: #111827; padding: 10px; border-radius: 6px; display: block; color: #f9fafb;">
                        pip install contextlite
                    </code>
                </div>
            </div>
        </div>
        
        <div style="text-align: center; padding: 20px;">
            <div style="display: flex; justify-content: center; gap: 20px; flex-wrap: wrap;">
                <a href="https://github.com/Michael-A-Kuykendall/contextlite/wiki" 
                   style="background: #374151; color: white; padding: 12px 24px; border-radius: 8px; text-decoration: none; display: flex; align-items: center; gap: 8px;">
                    📚 Documentation
                </a>
                <a href="https://github.com/Michael-A-Kuykendall/contextlite" 
                   style="background: #374151; color: white; padding: 12px 24px; border-radius: 8px; text-decoration: none; display: flex; align-items: center; gap: 8px;">
                    ⚡ GitHub
                </a>
                <a href="https://contextlite.com" 
                   style="background: #2563eb; color: white; padding: 12px 24px; border-radius: 8px; text-decoration: none; display: flex; align-items: center; gap: 8px;">
                    🏠 Homepage
                </a>
            </div>
        </div>
        
        <div style="text-align: center; margin-top: 40px; padding: 20px; background: #f0f9ff; border-radius: 12px; border-left: 4px solid #2563eb;">
            <h3 style="color: #1e40af; margin-bottom: 10px;">⚡ Performance Highlights</h3>
            <p style="color: #1e40af; margin: 5px 0;"><strong>0.3ms</strong> average response time</p>
            <p style="color: #1e40af; margin: 5px 0;"><strong>100x faster</strong> than vector databases</p>
            <p style="color: #1e40af; margin: 5px 0;"><strong>Smart Multi-Token (SMT)</strong> optimization technology</p>
        </div>
    </div>
    """
    
    return download_html

def generate_download_cards(release):
    """Generate download cards for all platforms"""
    if not release or 'assets' not in release:
        return '<p style="text-align: center; color: #94a3b8;">Download links will appear here when releases are available.</p>'
    
    assets = release.get('assets', [])
    cards = []
    
    # Platform configurations with enhanced styling
    platforms = [
        {
            'name': 'Windows (x64)', 
            'pattern': 'windows-amd64.exe',
            'icon': '🪟',
            'color': '#0078d4',
            'description': 'Windows 10/11 executable'
        },
        {
            'name': 'macOS (Intel)', 
            'pattern': 'darwin-amd64',
            'icon': '🍎',
            'color': '#007aff',
            'description': 'Intel Mac binary'
        },
        {
            'name': 'macOS (Apple Silicon)', 
            'pattern': 'darwin-arm64',
            'icon': '🍎',
            'color': '#007aff',
            'description': 'M1/M2/M3 Mac binary'
        },
        {
            'name': 'Linux (x64)', 
            'pattern': 'linux-amd64',
            'icon': '🐧',
            'color': '#ffa500',
            'description': 'Most Linux distributions'
        },
        {
            'name': 'Linux (ARM64)', 
            'pattern': 'linux-arm64',
            'icon': '🐧',
            'color': '#ffa500',
            'description': 'Raspberry Pi, ARM servers'
        },
        {
            'name': 'FreeBSD (x64)', 
            'pattern': 'freebsd-amd64',
            'icon': '👹',
            'color': '#c41e3a',
            'description': 'FreeBSD systems'
        }
    ]
    
    for platform in platforms:
        matching_asset = None
        for asset in assets:
            if platform['pattern'] in asset.get('name', '').lower():
                matching_asset = asset
                break
        
        if matching_asset:
            download_url = matching_asset.get('browser_download_url', '#')
            file_size = format_file_size(matching_asset.get('size', 0))
            
            card = f'''
            <a href="{download_url}" 
               style="background: linear-gradient(135deg, #1e293b, #334155); 
                      border: 1px solid rgba({hex_to_rgb(platform["color"])}, 0.3); 
                      border-radius: 16px; padding: 30px; text-decoration: none; 
                      color: white; display: block; transition: all 0.3s ease;"
               onmouseover="this.style.borderColor='rgba({hex_to_rgb(platform["color"])}, 0.6)'; this.style.transform='translateY(-3px)'"
               onmouseout="this.style.borderColor='rgba({hex_to_rgb(platform["color"])}, 0.3)'; this.style.transform='translateY(0)'">
                <div style="font-size: 3rem; margin-bottom: 15px; text-align: center;">{platform["icon"]}</div>
                <h3 style="color: {platform["color"]}; font-size: 1.5rem; margin-bottom: 15px; text-align: center;">
                    {platform["name"]}
                </h3>
                <p style="color: #94a3b8; text-align: center; margin-bottom: 10px; font-size: 0.9rem;">
                    {platform["description"]}
                </p>
                <p style="color: #64748b; text-align: center; margin: 0; font-size: 0.8rem;">
                    {file_size}
                </p>
            </a>
            '''
            cards.append(card)
    
    return '\n'.join(cards) if cards else '<p style="text-align: center; color: #94a3b8;">No platform binaries available yet.</p>'

def hex_to_rgb(hex_color):
    """Convert hex color to RGB values for CSS rgba"""
    hex_color = hex_color.lstrip('#')
    return f"{int(hex_color[0:2], 16)}, {int(hex_color[2:4], 16)}, {int(hex_color[4:6], 16)}"

def format_file_size(size_bytes):
    """Format file size in human readable format"""
    if size_bytes == 0:
        return "0 B"
    
    for unit in ['B', 'KB', 'MB', 'GB']:
        if size_bytes < 1024.0:
            return f"{size_bytes:.1f} {unit}"
        size_bytes /= 1024.0
    return f"{size_bytes:.1f} TB"

# Create Gradio interface
with gr.Blocks(title="ContextLite Download", theme=gr.themes.Soft()) as demo:
    html_output = gr.HTML(create_download_page())
    
    # Set up periodic refresh every 5 minutes
    timer = gr.Timer(300)  # 300 seconds = 5 minutes
    timer.tick(fn=create_download_page, outputs=html_output)

if __name__ == "__main__":
    demo.launch()
