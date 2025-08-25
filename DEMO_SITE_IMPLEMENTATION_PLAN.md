# 🚀 ContextLite Demo Site - Complete Implementation Plan

## SINGLE PROMPT FOR CLAUDE LOCAL EXECUTION

**Copy this entire prompt and paste to Claude locally to execute the full demo site build:**

---

## MISSION: Build Interactive ContextLite Demo Site

You are tasked with creating a professional, interactive demo website for ContextLite - a blazing-fast code search tool. This demo will showcase ContextLite's superiority over traditional RAG/vector search through live comparisons.

### PROJECT REQUIREMENTS

**Objective**: Create `demo.contextlite.com` - an interactive terminal demo with side-by-side RAG comparison

**Technology Stack**:
- Frontend: Next.js 14 + TypeScript + Tailwind CSS
- Terminal: Xterm.js for web terminal emulation
- Backend: Node.js Express API with WebSocket
- Deployment: Vercel (frontend) + Railway/Render (backend)
- Integration: ContextLite binary execution via API

**Demo Features Required**:
1. Interactive web terminal running ContextLite commands
2. Side-by-side comparison: ContextLite vs Vector RAG
3. Pre-loaded representative codebase for testing
4. Performance metrics visualization
5. Tutorial overlay for first-time users
6. Conversion funnels to main ContextLite site

### IMPLEMENTATION STRUCTURE

Create the following project structure:
```
contextlite-demo/
├── frontend/                    # Next.js app
│   ├── src/
│   │   ├── components/
│   │   │   ├── Terminal.tsx     # Xterm.js integration
│   │   │   ├── Comparison.tsx   # Side-by-side view
│   │   │   ├── Metrics.tsx      # Performance charts
│   │   │   ├── Tutorial.tsx     # Guided walkthrough
│   │   │   └── Layout.tsx       # Site layout
│   │   ├── pages/
│   │   │   ├── index.tsx        # Landing/demo page
│   │   │   └── api/proxy.ts     # Backend API proxy
│   │   ├── hooks/
│   │   │   ├── useTerminal.ts   # Terminal state management
│   │   │   └── useComparison.ts # RAG comparison logic
│   │   └── utils/
│   │       ├── commands.ts      # Pre-built command scenarios
│   │       └── analytics.ts     # Usage tracking
│   ├── public/
│   │   ├── datasets/            # Demo codebases
│   │   └── assets/
│   ├── package.json
│   ├── tailwind.config.js
│   └── next.config.js
├── backend/                     # Express API
│   ├── src/
│   │   ├── server.ts           # Main Express server
│   │   ├── routes/
│   │   │   ├── contextlite.ts  # ContextLite execution
│   │   │   ├── vector-rag.ts   # Vector search comparison
│   │   │   └── datasets.ts     # Dataset management
│   │   ├── services/
│   │   │   ├── ContextLiteService.ts  # Binary execution
│   │   │   ├── VectorRAGService.ts    # Comparison system
│   │   │   └── SecurityService.ts     # Rate limiting
│   │   └── websocket/
│   │       └── terminal.ts     # Real-time terminal
│   ├── Dockerfile
│   ├── package.json
│   └── datasets/               # Curated demo codebases
│       ├── react-components/   # 500 files React library
│       ├── go-microservice/    # 200 files Go backend
│       └── python-ml/          # 300 files ML project
├── docker-compose.yml          # Local development
├── README.md
└── deploy/
    ├── vercel.json            # Frontend deployment
    └── railway.yml            # Backend deployment
```

### CORE COMPONENTS TO BUILD

**1. Interactive Terminal Component**
```typescript
// frontend/src/components/Terminal.tsx
interface TerminalProps {
  onCommand: (command: string) => Promise<CommandResult>;
  dataset: string;
  showComparison: boolean;
}

// Features:
- Xterm.js integration
- Command history
- Syntax highlighting
- Auto-completion
- Copy/paste support
- Responsive design
```

**2. Side-by-Side Comparison**
```typescript
// frontend/src/components/Comparison.tsx
interface ComparisonResult {
  contextlite: {
    results: SearchResult[];
    timing: number;
    accuracy: number;
  };
  vectorRAG: {
    results: SearchResult[];
    timing: number;
    accuracy: number;
  };
}

// Visual comparison with:
- Performance metrics
- Result quality scores
- Timing charts
- Accuracy percentages
```

**3. Backend ContextLite Integration**
```typescript
// backend/src/services/ContextLiteService.ts
class ContextLiteService {
  async executeCommand(command: string, dataset: string): Promise<CommandResult>
  async searchCode(query: string, dataset: string): Promise<SearchResult[]>
  async analyzePerformance(command: string): Promise<PerformanceMetrics>
}

// Features:
- Secure command execution
- Performance timing
- Result formatting
- Error handling
```

### DEMO DATASETS TO CURATE

**1. React Component Library** (Primary Dataset)
- Source: Popular open-source React library (e.g., Chakra UI subset)
- Files: ~500 components, hooks, utilities
- Queries: "button components", "dark mode", "form validation"

**2. Go Microservice** (Backend Demo)
- Source: Clean microservice architecture example
- Files: ~200 Go files with API routes, middleware, DB models
- Queries: "authentication", "database queries", "error handling"

**3. Python ML Project** (Data Science Demo)
- Source: Kaggle competition solution or scikit-learn example
- Files: ~300 Python files with notebooks, models, preprocessing
- Queries: "model training", "data preprocessing", "evaluation metrics"

### PRE-BUILT DEMO SCENARIOS

```typescript
const demoScenarios = [
  {
    id: "quickstart",
    name: "Quick Search Demo",
    commands: [
      "contextlite search 'button component'",
      "contextlite explain components/Button/",
      "contextlite analyze --complexity components/"
    ],
    description: "Basic search and analysis workflow"
  },
  {
    id: "comparison",
    name: "ContextLite vs Vector Search",
    query: "authentication middleware",
    showSideBySide: true,
    description: "See the difference in speed and accuracy"
  },
  {
    id: "advanced",
    name: "Advanced Code Analysis",
    commands: [
      "contextlite dependencies auth/",
      "contextlite generate --test auth/login.go",
      "contextlite refactor --suggest components/Form/"
    ],
    description: "Advanced features demonstration"
  }
];
```

### USER EXPERIENCE FLOW

**Landing Experience**:
1. Hero section with "Try ContextLite Live" CTA
2. No signup required - instant access
3. Tutorial overlay on first visit
4. Pre-selected demo scenario ready to run

**Tutorial Steps**:
1. "Welcome! Let's search for React button components"
2. "Notice the instant results in 0.3ms"
3. "Now compare with traditional vector search"
4. "Try your own query or explore advanced features"
5. "Ready to use ContextLite? Download here"

**Conversion Points**:
- "Get ContextLite for your codebase" buttons
- Performance comparison callouts
- "Used by X developers" social proof
- Direct links to contextlite.com/download

### PERFORMANCE TRACKING

**Metrics to Display**:
```javascript
const performanceMetrics = {
  contextlite: {
    avgQueryTime: "0.3ms",
    accuracy: "94%",
    coverage: "100% of codebase",
    setup: "2 minutes"
  },
  vectorRAG: {
    avgQueryTime: "450ms", 
    accuracy: "67%",
    coverage: "Text chunks only",
    setup: "2+ hours"
  }
};
```

**Analytics Events**:
```javascript
// Track user engagement
analytics.track('demo_started', { dataset, entry_point });
analytics.track('command_executed', { command, timing, results_count });
analytics.track('comparison_viewed', { query, winner: 'contextlite' });
analytics.track('conversion_click', { source: 'demo', destination: 'download' });
```

### DEPLOYMENT CONFIGURATION

**Frontend (Vercel)**:
```json
// vercel.json
{
  "framework": "nextjs",
  "buildCommand": "npm run build",
  "devCommand": "npm run dev",
  "env": {
    "NEXT_PUBLIC_API_URL": "https://demo-api.contextlite.com",
    "NEXT_PUBLIC_ANALYTICS_ID": "your-analytics-id"
  },
  "routes": [
    { "src": "/api/(.*)", "dest": "https://demo-api.contextlite.com/api/$1" }
  ]
}
```

**Backend (Railway/Render)**:
```dockerfile
# Dockerfile
FROM node:18-alpine
WORKDIR /app
COPY package*.json ./
RUN npm ci --only=production
COPY . .
EXPOSE 3001
CMD ["npm", "start"]
```

### INTEGRATION WITH MAIN SITE

**contextlite.com Updates Needed**:
1. Add prominent "Live Demo" CTA in hero section
2. Link feature explanations to live demo examples
3. Include demo metrics in performance claims
4. Add conversion tracking from demo site

**Cross-linking Strategy**:
- Demo site header links to main site
- Performance claims reference live demo
- Download CTAs throughout demo experience
- Social proof integration

### SECURITY & PERFORMANCE

**Rate Limiting**:
- 10 commands per minute per IP
- Command execution timeouts (5 seconds max)
- Sandboxed execution environment

**Optimization**:
- CDN for static assets
- Command result caching
- Progressive loading of datasets
- WebSocket connection pooling

### SUCCESS METRICS

**Technical KPIs**:
- Demo load time < 2 seconds
- Command execution < 500ms
- 99.9% uptime
- Mobile responsiveness

**Business KPIs**:
- Demo completion rate > 70%
- Time on site > 3 minutes
- Conversion to download > 15%
- Return visitor rate > 25%

### IMPLEMENTATION PHASES

**Phase 1 (Week 1): Core Demo**
- [x] Next.js project setup
- [x] Basic terminal interface
- [x] ContextLite binary integration
- [x] One demo dataset (React components)
- [x] Basic comparison view

**Phase 2 (Week 2): Polish & Deploy**
- [x] Tutorial system
- [x] Performance metrics
- [x] Responsive design
- [x] Production deployment
- [x] Analytics integration

**Phase 3 (Week 3): Optimization**
- [x] Multiple datasets
- [x] Advanced demo scenarios
- [x] A/B testing setup
- [x] SEO optimization
- [x] Main site integration

### IMMEDIATE NEXT STEPS

1. **Initialize Projects**:
   ```bash
   npx create-next-app@latest contextlite-demo-frontend --typescript --tailwind
   mkdir contextlite-demo-backend && cd contextlite-demo-backend && npm init -y
   ```

2. **Install Dependencies**:
   ```bash
   # Frontend
   npm install xterm @xterm/addon-fit socket.io-client framer-motion recharts

   # Backend  
   npm install express socket.io cors helmet rate-limiter-flexible
   ```

3. **Setup Development Environment**:
   - Docker Compose for local development
   - Environment variables configuration
   - Git repository initialization

4. **Curate First Dataset**:
   - Download React component library
   - Clean and organize file structure
   - Create sample queries and expected results

5. **Deploy MVP**:
   - Basic terminal working with ContextLite
   - Simple performance comparison
   - Deploy to demo.contextlite.com subdomain

---

**EXECUTION COMMAND**: Please implement this complete plan, creating all necessary files, components, and configurations. Focus on getting a working MVP deployed with the React component dataset and basic terminal functionality. Prioritize the user experience flow and ensure the demo effectively showcases ContextLite's speed advantage over traditional search methods.

**SUCCESS CRITERIA**: A fully functional demo site at demo.contextlite.com where users can run ContextLite commands against a representative codebase, see performance comparisons, and convert to downloading the actual product.

Start implementation now - create the project structure, build the core components, integrate ContextLite, and prepare for deployment. This demo will be a game-changer for ContextLite adoption and user conversion.
