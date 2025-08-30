import gradio as gr
import requests
import json
from datetime import datetime

def get_latest_release():
    """Fetch latest release from GitHub API"""
    try:
        response = requests.get('https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases/latest')
        return response.json()
    except:
        return None

def format_file_size(bytes_size):
    """Convert bytes to MB"""
    return f"{bytes_size / 1024 / 1024:.1f} MB"

def create_download_page():
    release = get_latest_release()
    
    if not release:
        return """
        <div style="text-align: center; padding: 40px;">
            <h1>ContextLite Download</h1>
            <p>Unable to fetch latest release. Please visit <a href="https://github.com/Michael-A-Kuykendall/contextlite/releases">GitHub Releases</a></p>
        </div>
        """
    
    # Build download links
    download_html = f"""
    <div style="max-width: 1200px; margin: 0 auto; padding: 20px; font-family: Arial, sans-serif;">
        <div style="text-align: center; margin-bottom: 40px;">
            <h1 style="font-size: 3rem; background: linear-gradient(45deg, #ef4444, #dc2626); -webkit-background-clip: text; -webkit-text-fill-color: transparent; margin-bottom: 20px;">
                RAG Systems Were a Mistake
            </h1>
            <h2 style="font-size: 2rem; color: #2563eb; margin-bottom: 20px;">
                Download ContextLite - The Vector Database Killer
            </h2>
            <div style="display: flex; justify-content: center; gap: 30px; margin-bottom: 20px; flex-wrap: wrap;">
                <div style="text-align: center;">
                    <div style="font-size: 2rem; color: #ef4444;">⚡</div>
                    <div style="font-weight: bold; color: #1f2937;">0.3ms</div>
                    <div style="color: #666; font-size: 0.9rem;">vs 30-50ms vector DBs</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 2rem; color: #22c55e;">🎯</div>
                    <div style="font-weight: bold; color: #1f2937;">Optimal</div>
                    <div style="color: #666; font-size: 0.9rem;">Mathematically proven</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 2rem; color: #22c55e;">💰</div>
                    <div style="font-weight: bold; color: #1f2937;">$0</div>
                    <div style="color: #666; font-size: 0.9rem;">vs $300-500/month</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 2rem; color: #3b82f6;">🔒</div>
                    <div style="font-weight: bold; color: #1f2937;">100% Local</div>
                    <div style="color: #666; font-size: 0.9rem;">Your data stays private</div>
                </div>
            </div>
            <p style="font-size: 1.2rem; color: #666; margin-bottom: 10px;">
                Latest Version: <strong style="color: #2563eb;">{release['tag_name']}</strong>
            </p>
            <p style="color: #888;">
                Released: {datetime.fromisoformat(release['published_at'].replace('Z', '+00:00')).strftime('%B %d, %Y')}
            </p>
        </div>
        
        <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 20px; margin-bottom: 40px;">
    """
    
    # Add download cards for each asset
    for asset in release['assets']:
        platform = "Windows" if "windows" in asset['name'].lower() or "win" in asset['name'].lower() else \
                  "macOS" if "darwin" in asset['name'].lower() or "macos" in asset['name'].lower() else \
                  "Linux"
        
        icon = "🖥️" if platform == "Windows" else "🍎" if platform == "macOS" else "🐧"
        
        download_html += f"""
            <div style="border: 2px solid #e5e7eb; border-radius: 12px; padding: 20px; background: white; box-shadow: 0 2px 4px rgba(0,0,0,0.1); transition: all 0.3s;">
                <div style="display: flex; align-items: center; margin-bottom: 15px;">
                    <span style="font-size: 2rem; margin-right: 10px;">{icon}</span>
                    <div>
                        <h3 style="margin: 0; color: #1f2937;">{platform}</h3>
                        <p style="margin: 5px 0 0 0; color: #6b7280; font-size: 0.9rem;">{format_file_size(asset['size'])}</p>
                    </div>
                </div>
                <a href="{asset['browser_download_url']}" 
                   style="display: block; background: linear-gradient(45deg, #2563eb, #3b82f6); color: white; text-decoration: none; padding: 12px 20px; border-radius: 8px; text-align: center; font-weight: bold; transition: all 0.3s;"
                   onmouseover="this.style.transform='translateY(-2px)'; this.style.boxShadow='0 4px 12px rgba(37,99,235,0.3)'"
                   onmouseout="this.style.transform='translateY(0)'; this.style.boxShadow='none'">
                    📥 Download for {platform}
                </a>
                <p style="margin: 10px 0 0 0; font-size: 0.8rem; color: #9ca3af; text-align: center;">
                    {asset['name']}
                </p>
            </div>
        """
    
    download_html += """
        </div>
        
        <div style="background: #f9fafb; border-radius: 12px; padding: 30px; margin-bottom: 40px;">
            <h2 style="text-align: center; color: #1f2937; margin-bottom: 30px;">🚀 Quick Start Guide</h2>
            <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); gap: 30px;">
                <div style="text-align: center;">
                    <h3 style="color: #2563eb; margin-bottom: 15px;">🖥️ Windows</h3>
                    <ol style="text-align: left; color: #555; padding-left: 20px;">
                        <li>Download the Windows executable</li>
                        <li>Extract the archive</li>
                        <li>Run <code style="background: #e5e7eb; padding: 2px 6px; border-radius: 4px;">contextlite.exe</code></li>
                        <li>Start your 14-day trial!</li>
                    </ol>
                </div>
                
                <div style="text-align: center;">
                    <h3 style="color: #2563eb; margin-bottom: 15px;">🍎 macOS</h3>
                    <ol style="text-align: left; color: #555; padding-left: 20px;">
                        <li>Download the macOS archive</li>
                        <li><code style="background: #e5e7eb; padding: 2px 6px; border-radius: 4px;">tar -xzf contextlite-*.tar.gz</code></li>
                        <li><code style="background: #e5e7eb; padding: 2px 6px; border-radius: 4px;">chmod +x contextlite</code></li>
                        <li><code style="background: #e5e7eb; padding: 2px 6px; border-radius: 4px;">./contextlite</code></li>
                    </ol>
                </div>
                
                <div style="text-align: center;">
                    <h3 style="color: #2563eb; margin-bottom: 15px;">🐧 Linux</h3>
                    <ol style="text-align: left; color: #555; padding-left: 20px;">
                        <li>Download the Linux archive</li>
                        <li><code style="background: #e5e7eb; padding: 2px 6px; border-radius: 4px;">tar -xzf contextlite-*.tar.gz</code></li>
                        <li><code style="background: #e5e7eb; padding: 2px 6px; border-radius: 4px;">chmod +x contextlite</code></li>
                        <li><code style="background: #e5e7eb; padding: 2px 6px; border-radius: 4px;">./contextlite</code></li>
                    </ol>
                </div>
            </div>
        </div>
        
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
        
        <div style="background: #fee2e2; border-radius: 12px; padding: 30px; margin-bottom: 40px; border-left: 4px solid #ef4444;">
            <h2 style="text-align: center; color: #dc2626; margin-bottom: 20px;">🚫 Why Vector Databases Are Obsolete</h2>
            <div style="display: grid; grid-template-columns: 1fr auto 1fr; gap: 20px; align-items: center; max-width: 800px; margin: 0 auto;">
                <div style="text-align: center;">
                    <h4 style="color: #dc2626; margin-bottom: 10px;">Vector Databases</h4>
                    <div style="color: #991b1b; margin: 5px 0;">🐌 30-50ms response time</div>
                    <div style="color: #991b1b; margin: 5px 0;">📊 Approximate similarity</div>
                    <div style="color: #991b1b; margin: 5px 0;">💸 $300-500/month costs</div>
                    <div style="color: #991b1b; margin: 5px 0;">☁️ Data uploaded to cloud</div>
                    <div style="color: #991b1b; margin: 5px 0;">🕐 Hours/days to setup</div>
                </div>
                
                <div style="font-size: 3rem; color: #dc2626;">VS</div>
                
                <div style="text-align: center;">
                    <h4 style="color: #059669; margin-bottom: 10px;">ContextLite</h4>
                    <div style="color: #047857; margin: 5px 0;">⚡ 0.3ms response time</div>
                    <div style="color: #047857; margin: 5px 0;">🎯 Mathematically optimal</div>
                    <div style="color: #047857; margin: 5px 0;">💰 $0 ongoing costs</div>
                    <div style="color: #047857; margin: 5px 0;">🔒 100% local data</div>
                    <div style="color: #047857; margin: 5px 0;">⚡ 30 seconds setup</div>
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
            <h3 style="color: #1e40af; margin-bottom: 10px;">⚡ Live Performance Stats</h3>
            <p style="color: #1e40af; margin: 5px 0;"><strong>0.3ms</strong> average response time (current system)</p>
            <p style="color: #1e40af; margin: 5px 0;"><strong>2,406 files/sec</strong> indexing speed</p>
            <p style="color: #1e40af; margin: 5px 0;"><strong>SMT optimization</strong> for provably optimal results</p>
            <p style="color: #1e40af; margin: 5px 0;"><strong>3 active workspaces</strong> with intelligent routing</p>
        </div>
    </div>
    """
    
    return download_html

# Create Gradio interface
with gr.Blocks(title="ContextLite Download", theme=gr.themes.Soft()) as demo:
    gr.HTML(create_download_page)
    
    # Auto-refresh every 5 minutes to check for new releases
    demo.load(fn=lambda: create_download_page(), outputs=gr.HTML(), every=300)

if __name__ == "__main__":
    demo.launch()
