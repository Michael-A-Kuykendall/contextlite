import gradio as gr
import json
import os
from datetime import datetime

# Analytics tracking
ANALYTICS_FILE = "analytics.json"

def track_visit():
    """Track page visits"""
    try:
        if os.path.exists(ANALYTICS_FILE):
            with open(ANALYTICS_FILE, 'r') as f:
                analytics = json.load(f)
        else:
            analytics = {"total_visits": 0, "daily_visits": {}}
        
        analytics["total_visits"] += 1
        today = datetime.now().strftime("%Y-%m-%d")
        analytics["daily_visits"][today] = analytics["daily_visits"].get(today, 0) + 1
        
        with open(ANALYTICS_FILE, 'w') as f:
            json.dump(analytics, f)
        
        return analytics
    except Exception:
        return {"total_visits": 0, "daily_visits": {}}

def create_page():
    analytics = track_visit()
    visits = analytics.get('total_visits', 0)
    
    return f"""
    <div style="font-family: 'Inter', sans-serif; background: linear-gradient(135deg, #0f172a 0%, #1e293b 50%); color: white; min-height: 100vh; padding: 40px 20px;">
        <div style="max-width: 1200px; margin: 0 auto; text-align: center;">
            <h1 style="font-size: 4rem; font-weight: 800; margin-bottom: 30px; background: linear-gradient(45deg, #ef4444, #f97316); -webkit-background-clip: text; -webkit-text-fill-color: transparent;">
                Download ContextLite v1.1.1
            </h1>
            
            <p style="font-size: 1.4rem; color: #94a3b8; margin-bottom: 40px;">
                Replace expensive vector databases with mathematically optimal context selection
            </p>
            
            <div style="display: flex; justify-content: center; gap: 60px; margin: 40px 0; flex-wrap: wrap;">
                <div style="text-align: center;">
                    <div style="font-size: 3rem; font-weight: 800; color: #3b82f6;">0.3ms</div>
                    <div style="color: #94a3b8;">Query Time</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 3rem; font-weight: 800; color: #10b981;">{visits:,}</div>
                    <div style="color: #94a3b8;">HF Space Visits</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 3rem; font-weight: 800; color: #8b5cf6;">100x</div>
                    <div style="color: #94a3b8;">Faster</div>
                </div>
            </div>
            
            <div style="background: rgba(30, 41, 59, 0.5); border-radius: 24px; padding: 40px; margin: 40px 0; border: 1px solid rgba(59, 130, 246, 0.3);">
                <h2 style="color: #3b82f6; margin-bottom: 30px; font-size: 2rem;">��� Download Options</h2>
                <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(280px, 1fr)); gap: 20px;">
                    <a href="https://github.com/Michael-A-Kuykendall/contextlite/releases/latest" 
                       style="display: block; background: linear-gradient(45deg, #3b82f6, #8b5cf6); color: white; padding: 20px; border-radius: 16px; text-decoration: none; font-weight: 700;">
                        ��� GitHub Releases<br><span style="font-size: 0.9rem; opacity: 0.8;">All Platforms</span>
                    </a>
                    <a href="https://www.npmjs.com/package/contextlite" 
                       style="display: block; background: linear-gradient(45deg, #cb3837, #ff6b6b); color: white; padding: 20px; border-radius: 16px; text-decoration: none; font-weight: 700;">
                        ��� npm install<br><span style="font-size: 0.9rem; opacity: 0.8;">Node.js</span>
                    </a>
                    <a href="https://pypi.org/project/contextlite/" 
                       style="display: block; background: linear-gradient(45deg, #3776ab, #4dabf7); color: white; padding: 20px; border-radius: 16px; text-decoration: none; font-weight: 700;">
                        ��� pip install<br><span style="font-size: 0.9rem; opacity: 0.8;">Python</span>
                    </a>
                </div>
            </div>
            
            <div style="margin-top: 40px;">
                <a href="https://contextlite.com" 
                   style="display: inline-block; background: rgba(16, 185, 129, 0.2); color: #10b981; padding: 15px 30px; border-radius: 12px; text-decoration: none; font-weight: 600; border: 1px solid rgba(16, 185, 129, 0.3);">
                    ��� Visit ContextLite.com
                </a>
            </div>
        </div>
    </div>
    """

with gr.Blocks(title="ContextLite Download", theme=gr.themes.Soft()) as demo:
    html_output = gr.HTML(create_page())

if __name__ == "__main__":
    demo.launch()
# Updated Thu, Aug 28, 2025  2:57:02 AM
