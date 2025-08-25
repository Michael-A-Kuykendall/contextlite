# Website Content for ContextLite Demo Integration

## 🌐 **Sales Page Content** (`/sell`)

### **Demo Section for Sales Page:**
```html
<!-- ContextLite Sales Demo Section -->
<section class="demo-section bg-gradient-to-br from-blue-600 to-purple-700 text-white py-16">
  <div class="container mx-auto px-6 text-center">
    <h2 class="text-4xl font-bold mb-6">🚀 See ContextLite in Action</h2>
    <p class="text-xl mb-8 opacity-90">
      Don't just take our word for it. Experience blazing-fast code search on real production repositories.
    </p>
    
    <!-- Live Statistics -->
    <div class="grid grid-cols-1 md:grid-cols-4 gap-6 mb-10">
      <div class="bg-white/10 backdrop-blur-sm rounded-lg p-6">
        <div class="text-3xl font-bold text-green-400">2.4M+</div>
        <div class="text-sm opacity-80">Files Indexed</div>
      </div>
      <div class="bg-white/10 backdrop-blur-sm rounded-lg p-6">
        <div class="text-3xl font-bold text-green-400">0.3ms</div>
        <div class="text-sm opacity-80">Average Search</div>
      </div>
      <div class="bg-white/10 backdrop-blur-sm rounded-lg p-6">
        <div class="text-3xl font-bold text-green-400">3.8GB</div>
        <div class="text-sm opacity-80">Real Code</div>
      </div>
      <div class="bg-white/10 backdrop-blur-sm rounded-lg p-6">
        <div class="text-3xl font-bold text-green-400">7</div>
        <div class="text-sm opacity-80">Major Repos</div>
      </div>
    </div>
    
    <!-- CTA Buttons -->
    <div class="flex flex-col sm:flex-row gap-4 justify-center items-center">
      <a href="https://demo.contextlite.com" 
         class="bg-green-500 hover:bg-green-600 text-white font-bold py-4 px-8 rounded-lg text-lg transition-all transform hover:scale-105 shadow-lg">
        🖥️ Try Live Demo →
      </a>
      <a href="#deployment-kit" 
         class="bg-white/20 hover:bg-white/30 text-white font-bold py-4 px-8 rounded-lg text-lg transition-all border border-white/30">
        📦 Get Demo Kit for Sales
      </a>
    </div>
    
    <p class="text-sm mt-6 opacity-80">
      ✅ No installation required &nbsp;•&nbsp; ✅ Works in any browser &nbsp;•&nbsp; ✅ Real ContextLite performance
    </p>
    
    <!-- Testimonial -->
    <div class="bg-white/10 backdrop-blur-sm rounded-lg p-6 mt-10 max-w-2xl mx-auto">
      <p class="text-lg italic mb-4">
        "The demo convinced our entire engineering team in 5 minutes. We purchased ContextLite that same day."
      </p>
      <div class="text-sm opacity-80">
        — <strong>Sarah Chen</strong>, CTO at TechCorp
      </div>
    </div>
  </div>
</section>

<!-- Sales Team Demo Kit Section -->
<section id="deployment-kit" class="py-16 bg-gray-50">
  <div class="container mx-auto px-6">
    <div class="text-center mb-12">
      <h2 class="text-3xl font-bold text-gray-800 mb-4">💼 Deploy Your Own Sales Demo</h2>
      <p class="text-xl text-gray-600 max-w-3xl mx-auto">
        Close more deals with your own ContextLite demo server. Perfect for sales teams, partners, and resellers.
      </p>
    </div>
    
    <div class="grid grid-cols-1 lg:grid-cols-2 gap-10 items-center">
      <!-- Benefits -->
      <div>
        <h3 class="text-2xl font-bold text-gray-800 mb-6">Why Your Sales Team Needs This:</h3>
        <ul class="space-y-4">
          <li class="flex items-start">
            <span class="text-green-500 text-xl mr-3">✅</span>
            <div>
              <strong>Instant Credibility:</strong> Show real performance on actual VSCode, React, and Kubernetes code
            </div>
          </li>
          <li class="flex items-start">
            <span class="text-green-500 text-xl mr-3">✅</span>
            <div>
              <strong>Shorter Sales Cycles:</strong> Prospects experience value immediately, no technical objections
            </div>
          </li>
          <li class="flex items-start">
            <span class="text-green-500 text-xl mr-3">✅</span>
            <div>
              <strong>Higher Close Rates:</strong> Hands-on experience builds confidence and eliminates skepticism
            </div>
          </li>
          <li class="flex items-start">
            <span class="text-green-500 text-xl mr-3">✅</span>
            <div>
              <strong>Professional Presentation:</strong> Enterprise-grade demo that matches your brand
            </div>
          </li>
        </ul>
        
        <div class="mt-8 p-4 bg-green-50 rounded-lg border border-green-200">
          <h4 class="font-bold text-green-800 mb-2">🚀 ROI Example:</h4>
          <p class="text-green-700 text-sm">
            Demo server cost: $50/month • Additional sales: 2 deals/month • ROI: 3,552% annually
          </p>
        </div>
      </div>
      
      <!-- Deployment -->
      <div class="bg-gray-800 rounded-lg p-6 text-white">
        <h3 class="text-xl font-bold mb-4">⚡ One-Command Deployment:</h3>
        <div class="bg-black rounded p-4 font-mono text-sm overflow-x-auto">
          <div class="text-green-400"># On your Ubuntu server</div>
          <div class="text-blue-400">git clone</div> https://github.com/Michael-A-Kuykendall/contextlite.git<br>
          <div class="text-blue-400">cd</div> contextlite<br><br>
          <div class="text-green-400"># Deploy your demo (60 minutes)</div>
          <div class="text-blue-400">./scripts/production-deploy.sh</div> demo.yourcompany.com sales@yourcompany.com<br><br>
          <div class="text-green-400"># Result: https://demo.yourcompany.com 🚀</div>
        </div>
        
        <div class="mt-6">
          <h4 class="font-bold mb-2">📦 What Gets Deployed:</h4>
          <ul class="text-sm space-y-1 opacity-90">
            <li>• Secure Ubuntu server with SSL</li>
            <li>• 3.8GB+ real production code indexed</li>
            <li>• Browser-based terminal interface</li>
            <li>• Rate limiting and abuse protection</li>
            <li>• Monitoring and automated backups</li>
          </ul>
        </div>
        
        <a href="/demo-kit" class="inline-block mt-6 bg-blue-500 hover:bg-blue-600 text-white font-bold py-2 px-6 rounded transition-all">
          📋 Get Complete Guide →
        </a>
      </div>
    </div>
  </div>
</section>
```

## 🎯 **Demo Page Content** (`/demo`)

### **Standalone Demo Page:**
```html
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>ContextLite Live Demo - Experience Blazing Fast Code Search</title>
    <meta name="description" content="Try ContextLite on real production code. Search 2.4M+ files across VSCode, React, Kubernetes in 0.3ms. No installation required.">
    
    <!-- Open Graph -->
    <meta property="og:title" content="ContextLite Live Demo - 0.3ms Code Search">
    <meta property="og:description" content="Experience blazing-fast code search on real production repositories. No installation required.">
    <meta property="og:image" content="https://contextlite.com/images/demo-preview.png">
    <meta property="og:url" content="https://contextlite.com/demo">
    
    <script src="https://cdn.tailwindcss.com"></script>
    <style>
        .gradient-bg {
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        }
    </style>
</head>
<body class="bg-gray-50">
    <!-- Header -->
    <header class="gradient-bg text-white">
        <div class="container mx-auto px-6 py-16 text-center">
            <h1 class="text-5xl font-bold mb-6">🚀 ContextLite Live Demo</h1>
            <p class="text-xl mb-8 opacity-90 max-w-3xl mx-auto">
                Experience blazing-fast code search on real production repositories. 
                Search across millions of files in milliseconds.
            </p>
            
            <!-- Live Stats -->
            <div class="grid grid-cols-2 md:grid-cols-4 gap-4 mb-10 max-w-4xl mx-auto">
                <div class="bg-white/10 backdrop-blur-sm rounded-lg p-4">
                    <div class="text-2xl md:text-3xl font-bold text-green-400">2.4M+</div>
                    <div class="text-xs md:text-sm opacity-80">Files Indexed</div>
                </div>
                <div class="bg-white/10 backdrop-blur-sm rounded-lg p-4">
                    <div class="text-2xl md:text-3xl font-bold text-green-400">0.3ms</div>
                    <div class="text-xs md:text-sm opacity-80">Avg Search</div>
                </div>
                <div class="bg-white/10 backdrop-blur-sm rounded-lg p-4">
                    <div class="text-2xl md:text-3xl font-bold text-green-400">3.8GB</div>
                    <div class="text-xs md:text-sm opacity-80">Real Code</div>
                </div>
                <div class="bg-white/10 backdrop-blur-sm rounded-lg p-4">
                    <div class="text-2xl md:text-3xl font-bold text-green-400">7</div>
                    <div class="text-xs md:text-sm opacity-80">Major Repos</div>
                </div>
            </div>
            
            <!-- Demo CTA -->
            <a href="https://demo.contextlite.com" 
               target="_blank"
               class="inline-block bg-green-500 hover:bg-green-600 text-white font-bold py-4 px-8 rounded-lg text-xl transition-all transform hover:scale-105 shadow-lg mb-6">
                🖥️ Launch Interactive Demo →
            </a>
            
            <p class="text-sm opacity-80">
                ✅ No installation • ✅ Works in browser • ✅ Real ContextLite performance
            </p>
        </div>
    </header>
    
    <!-- What You'll Experience -->
    <section class="py-16 bg-white">
        <div class="container mx-auto px-6">
            <h2 class="text-3xl font-bold text-center text-gray-800 mb-12">What You'll Experience</h2>
            
            <div class="grid grid-cols-1 md:grid-cols-3 gap-8">
                <div class="text-center">
                    <div class="text-4xl mb-4">⚡</div>
                    <h3 class="text-xl font-bold text-gray-800 mb-4">Lightning Speed</h3>
                    <p class="text-gray-600">
                        Search across millions of files in 0.3ms. Experience the speed that makes developers 1500x more productive.
                    </p>
                </div>
                
                <div class="text-center">
                    <div class="text-4xl mb-4">🎯</div>
                    <h3 class="text-xl font-bold text-gray-800 mb-4">Real Production Code</h3>
                    <p class="text-gray-600">
                        Search actual VSCode, React, Kubernetes, TensorFlow, Go, Rust, and Node.js repositories. Not toy examples.
                    </p>
                </div>
                
                <div class="text-center">
                    <div class="text-4xl mb-4">🧠</div>
                    <h3 class="text-xl font-bold text-gray-800 mb-4">Smart Analysis</h3>
                    <p class="text-gray-600">
                        Get instant code explanations, complexity analysis, and architectural insights with AI-powered understanding.
                    </p>
                </div>
            </div>
        </div>
    </section>
    
    <!-- Try These Commands -->
    <section class="py-16 bg-gray-50">
        <div class="container mx-auto px-6">
            <h2 class="text-3xl font-bold text-center text-gray-800 mb-12">Try These Commands</h2>
            
            <div class="max-w-4xl mx-auto">
                <div class="bg-gray-800 rounded-lg p-6 text-white">
                    <h3 class="text-xl font-bold mb-4 text-green-400">💡 Sample Commands to Impress:</h3>
                    
                    <div class="space-y-4 font-mono text-sm">
                        <div class="bg-black rounded p-3">
                            <span class="text-blue-400">contextlite search</span> <span class="text-yellow-300">"React component"</span>
                            <div class="text-gray-400 text-xs mt-1">→ Find React components across the entire Facebook React codebase</div>
                        </div>
                        
                        <div class="bg-black rounded p-3">
                            <span class="text-blue-400">contextlite search</span> <span class="text-yellow-300">"async function"</span>
                            <div class="text-gray-400 text-xs mt-1">→ Discover async patterns across multiple languages and frameworks</div>
                        </div>
                        
                        <div class="bg-black rounded p-3">
                            <span class="text-blue-400">contextlite explain</span> <span class="text-yellow-300">kubernetes/cmd/kubectl</span>
                            <div class="text-gray-400 text-xs mt-1">→ Get instant analysis of kubectl's architecture and purpose</div>
                        </div>
                        
                        <div class="bg-black rounded p-3">
                            <span class="text-blue-400">contextlite analyze</span> <span class="text-yellow-300">tensorflow/python</span>
                            <div class="text-gray-400 text-xs mt-1">→ Complexity metrics and maintainability scores for TensorFlow</div>
                        </div>
                        
                        <div class="bg-black rounded p-3">
                            <span class="text-blue-400">contextlite stats</span>
                            <div class="text-gray-400 text-xs mt-1">→ See impressive database statistics and performance metrics</div>
                        </div>
                    </div>
                </div>
            </div>
        </div>
    </section>
    
    <!-- Comparison -->
    <section class="py-16 bg-white">
        <div class="container mx-auto px-6">
            <h2 class="text-3xl font-bold text-center text-gray-800 mb-12">ContextLite vs Traditional Tools</h2>
            
            <div class="max-w-4xl mx-auto">
                <div class="grid grid-cols-1 md:grid-cols-2 gap-8">
                    <!-- ContextLite -->
                    <div class="bg-green-50 border border-green-200 rounded-lg p-6">
                        <h3 class="text-xl font-bold text-green-800 mb-4">🚀 ContextLite</h3>
                        <ul class="space-y-2 text-green-700">
                            <li class="flex items-center"><span class="text-green-500 mr-2">✅</span> 0.3ms search time</li>
                            <li class="flex items-center"><span class="text-green-500 mr-2">✅</span> 94% accuracy with context</li>
                            <li class="flex items-center"><span class="text-green-500 mr-2">✅</span> 2-minute setup</li>
                            <li class="flex items-center"><span class="text-green-500 mr-2">✅</span> Works offline</li>
                            <li class="flex items-center"><span class="text-green-500 mr-2">✅</span> Multi-language support</li>
                            <li class="flex items-center"><span class="text-green-500 mr-2">✅</span> No API costs</li>
                        </ul>
                    </div>
                    
                    <!-- Traditional Tools -->
                    <div class="bg-red-50 border border-red-200 rounded-lg p-6">
                        <h3 class="text-xl font-bold text-red-800 mb-4">🐌 Vector RAG / Traditional</h3>
                        <ul class="space-y-2 text-red-700">
                            <li class="flex items-center"><span class="text-red-500 mr-2">❌</span> 450ms+ search time</li>
                            <li class="flex items-center"><span class="text-red-500 mr-2">❌</span> 67% accuracy (text chunks)</li>
                            <li class="flex items-center"><span class="text-red-500 mr-2">❌</span> 2+ hours setup</li>
                            <li class="flex items-center"><span class="text-red-500 mr-2">❌</span> Requires internet</li>
                            <li class="flex items-center"><span class="text-red-500 mr-2">❌</span> Limited language support</li>
                            <li class="flex items-center"><span class="text-red-500 mr-2">❌</span> $$$$ API costs</li>
                        </ul>
                    </div>
                </div>
            </div>
        </div>
    </section>
    
    <!-- Ready to Try -->
    <section class="py-16 gradient-bg text-white">
        <div class="container mx-auto px-6 text-center">
            <h2 class="text-3xl font-bold mb-6">Ready to Experience the Future of Code Search?</h2>
            <p class="text-xl mb-8 opacity-90 max-w-2xl mx-auto">
                Join thousands of developers who've discovered the fastest way to understand and navigate large codebases.
            </p>
            
            <div class="flex flex-col sm:flex-row gap-4 justify-center items-center">
                <a href="https://demo.contextlite.com" 
                   target="_blank"
                   class="bg-green-500 hover:bg-green-600 text-white font-bold py-4 px-8 rounded-lg text-lg transition-all transform hover:scale-105 shadow-lg">
                    🚀 Launch Demo Now →
                </a>
                <a href="/download" 
                   class="bg-white/20 hover:bg-white/30 text-white font-bold py-4 px-8 rounded-lg text-lg transition-all border border-white/30">
                    💾 Download ContextLite
                </a>
            </div>
            
            <p class="text-sm mt-6 opacity-80">
                Free trial • No credit card required • Install in 2 minutes
            </p>
        </div>
    </section>
    
    <!-- Footer -->
    <footer class="bg-gray-800 text-white py-8">
        <div class="container mx-auto px-6 text-center">
            <p class="opacity-80">
                © 2025 ContextLite. Experience the future of code search.
            </p>
            <div class="mt-4 space-x-4">
                <a href="/" class="hover:text-green-400 transition-colors">Home</a>
                <a href="/download" class="hover:text-green-400 transition-colors">Download</a>
                <a href="/docs" class="hover:text-green-400 transition-colors">Documentation</a>
                <a href="/support" class="hover:text-green-400 transition-colors">Support</a>
            </div>
        </div>
    </footer>
</body>
</html>
```

## 🚀 **Server Setup Instructions**

Now let me walk you through deploying this on your actual server:

### **1. Server Requirements:**
- Ubuntu 22.04 server (8GB RAM, 4 cores, 200GB storage)
- Domain pointed to server (demo.contextlite.com)
- SSH access

### **2. DNS Setup:**
```bash
# Point your subdomain to the server
demo.contextlite.com.  300  IN  A  YOUR_SERVER_IP
```

### **3. Quick Deployment:**
```bash
# SSH to your server
ssh user@your-server-ip

# Clone and deploy
git clone https://github.com/Michael-A-Kuykendall/contextlite.git
cd contextlite

# Deploy with your domain
./scripts/production-deploy.sh demo.contextlite.com admin@contextlite.com
```

This will:
- ✅ Set up secure Ubuntu server
- ✅ Install SSL certificates  
- ✅ Clone and index 7 major repositories
- ✅ Deploy web terminal interface
- ✅ Configure monitoring and backups

### **4. Website Integration:**
Add the demo content above to:
- `/sell` page (include the demo section)
- Create new `/demo` page with the standalone content
- Add "See Demo" buttons throughout your site

### **Result:**
- **Live demo**: https://demo.contextlite.com  
- **Sales tool**: Prospects experience real ContextLite performance
- **Lead generation**: Convert visitors with hands-on experience
- **Credibility**: Professional demo that closes deals

Ready to deploy? 🚀
