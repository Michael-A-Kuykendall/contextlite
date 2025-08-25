'use client';

import { useState, useEffect } from 'react';
import Terminal from '@/components/Terminal';
import Comparison from '@/components/Comparison';
import Tutorial from '@/components/Tutorial';
import { motion } from 'framer-motion';
import { Play, BookOpen, Download, Github, ArrowRight, Zap, Target, Clock } from 'lucide-react';

export default function Home() {
  const [showTutorial, setShowTutorial] = useState(false);
  const [activeView, setActiveView] = useState<'terminal' | 'comparison'>('terminal');
  const [highlightedElement, setHighlightedElement] = useState('');

  useEffect(() => {
    // Show tutorial on first visit
    const hasSeenTutorial = localStorage.getItem('contextlite-demo-tutorial');
    if (!hasSeenTutorial) {
      setShowTutorial(true);
    }
  }, []);

  const handleTutorialClose = () => {
    setShowTutorial(false);
    localStorage.setItem('contextlite-demo-tutorial', 'true');
  };

  const handleRunCommand = (command: string) => {
    // This would integrate with the terminal component
    console.log('Running command:', command);
  };

  const handleHighlight = (element: string) => {
    setHighlightedElement(element);
    if (element === 'comparison') {
      setActiveView('comparison');
    } else if (element === 'terminal') {
      setActiveView('terminal');
    }
  };

  return (
    <div className="min-h-screen bg-gradient-to-br from-slate-50 to-blue-50">
      {/* Header */}
      <header className="bg-white border-b border-gray-200 sticky top-0 z-30">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
          <div className="flex items-center justify-between h-16">
            <div className="flex items-center space-x-4">
              <div className="flex items-center space-x-2">
                <div className="w-8 h-8 bg-blue-600 rounded-lg flex items-center justify-center">
                  <Zap className="w-5 h-5 text-white" />
                </div>
                <div>
                  <h1 className="text-xl font-bold text-gray-900">ContextLite</h1>
                  <p className="text-xs text-gray-500">Interactive Demo</p>
                </div>
              </div>
            </div>
            
            <div className="flex items-center space-x-4">
              <button
                onClick={() => setShowTutorial(true)}
                className="flex items-center space-x-2 px-3 py-2 text-gray-600 hover:text-gray-900 transition-colors"
              >
                <BookOpen className="w-4 h-4" />
                <span className="hidden sm:inline">Tutorial</span>
              </button>
              <a
                href="https://github.com/Michael-A-Kuykendall/contextlite"
                target="_blank"
                rel="noopener noreferrer"
                className="flex items-center space-x-2 px-3 py-2 text-gray-600 hover:text-gray-900 transition-colors"
              >
                <Github className="w-4 h-4" />
                <span className="hidden sm:inline">GitHub</span>
              </a>
              <a
                href="https://contextlite.com"
                className="flex items-center space-x-2 px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
              >
                <Download className="w-4 h-4" />
                <span>Download</span>
              </a>
            </div>
          </div>
        </div>
      </header>

      {/* Hero Section */}
      <section className="py-12 px-4 sm:px-6 lg:px-8">
        <div className="max-w-7xl mx-auto text-center">
          <motion.div
            initial={{ opacity: 0, y: 20 }}
            animate={{ opacity: 1, y: 0 }}
            className="space-y-6"
          >
            <h1 className="text-4xl sm:text-5xl lg:text-6xl font-bold text-gray-900">
              Experience{' '}
              <span className="bg-gradient-to-r from-blue-600 to-purple-600 bg-clip-text text-transparent">
                Instant
              </span>{' '}
              Code Search
            </h1>
            <p className="text-xl text-gray-600 max-w-3xl mx-auto">
              Try ContextLite live - no installation required. See how it revolutionizes code search 
              with AI-powered understanding and lightning-fast results.
            </p>
            
            {/* Performance highlights */}
            <div className="flex flex-wrap justify-center gap-8 mt-8">
              <div className="flex items-center space-x-2">
                <Clock className="w-5 h-5 text-blue-600" />
                <span className="text-sm font-medium text-gray-700">0.3ms search time</span>
              </div>
              <div className="flex items-center space-x-2">
                <Target className="w-5 h-5 text-green-600" />
                <span className="text-sm font-medium text-gray-700">94% accuracy</span>
              </div>
              <div className="flex items-center space-x-2">
                <Zap className="w-5 h-5 text-purple-600" />
                <span className="text-sm font-medium text-gray-700">1500x faster than vector search</span>
              </div>
            </div>

            <div className="flex flex-col sm:flex-row gap-4 justify-center items-center mt-8">
              <button
                onClick={() => setShowTutorial(true)}
                className="flex items-center space-x-2 px-6 py-3 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
              >
                <Play className="w-4 h-4" />
                <span>Start Interactive Demo</span>
              </button>
              <button
                onClick={() => setActiveView(activeView === 'terminal' ? 'comparison' : 'terminal')}
                className="flex items-center space-x-2 px-6 py-3 border border-gray-300 text-gray-700 rounded-lg hover:bg-gray-50 transition-colors"
              >
                <span>
                  {activeView === 'terminal' ? 'View Comparison' : 'View Terminal'}
                </span>
                <ArrowRight className="w-4 h-4" />
              </button>
            </div>
          </motion.div>
        </div>
      </section>

      {/* View Toggle */}
      <section className="px-4 sm:px-6 lg:px-8 mb-8">
        <div className="max-w-7xl mx-auto">
          <div className="flex justify-center mb-6">
            <div className="bg-white rounded-lg p-1 border border-gray-200">
              <button
                onClick={() => setActiveView('terminal')}
                className={`px-4 py-2 rounded-md text-sm font-medium transition-colors ${
                  activeView === 'terminal'
                    ? 'bg-blue-600 text-white'
                    : 'text-gray-600 hover:text-gray-900'
                }`}
              >
                Interactive Terminal
              </button>
              <button
                onClick={() => setActiveView('comparison')}
                className={`px-4 py-2 rounded-md text-sm font-medium transition-colors ${
                  activeView === 'comparison'
                    ? 'bg-blue-600 text-white'
                    : 'text-gray-600 hover:text-gray-900'
                }`}
              >
                Performance Comparison
              </button>
            </div>
          </div>
        </div>
      </section>

      {/* Main Demo Area */}
      <section className="px-4 sm:px-6 lg:px-8 pb-16">
        <div className="max-w-7xl mx-auto">
          <motion.div
            key={activeView}
            initial={{ opacity: 0, y: 20 }}
            animate={{ opacity: 1, y: 0 }}
            className={`${
              highlightedElement === 'terminal' || highlightedElement === 'comparison'
                ? 'ring-4 ring-blue-500 ring-opacity-50 rounded-lg'
                : ''
            }`}
          >
            {activeView === 'terminal' ? (
              <div className="bg-white rounded-lg border border-gray-200 p-6">
                <div className="mb-4">
                  <h2 className="text-2xl font-bold text-gray-900 mb-2">
                    Interactive Terminal
                  </h2>
                  <p className="text-gray-600">
                    Try ContextLite commands on our React component library demo dataset.
                    Type commands or click the suggestions below.
                  </p>
                </div>
                
                {/* Quick commands */}
                <div className="mb-4 flex flex-wrap gap-2">
                  {[
                    'contextlite search "button component"',
                    'contextlite explain components/Button/',
                    'contextlite analyze --complexity components/'
                  ].map((cmd) => (
                    <button
                      key={cmd}
                      onClick={() => handleRunCommand(cmd)}
                      className="px-3 py-1 bg-gray-100 text-gray-700 rounded text-sm hover:bg-gray-200 transition-colors"
                    >
                      {cmd}
                    </button>
                  ))}
                </div>

                <Terminal 
                  className="h-96"
                  dataset="react-components"
                  onCommand={async (command) => {
                    // Mock command execution - in real implementation this would call the API
                    await new Promise(resolve => setTimeout(resolve, 300));
                    return `Mock result for: ${command}`;
                  }}
                />
              </div>
            ) : (
              <div className="bg-white rounded-lg border border-gray-200 p-6">
                <div className="mb-6">
                  <h2 className="text-2xl font-bold text-gray-900 mb-2">
                    Performance Comparison
                  </h2>
                  <p className="text-gray-600">
                    See how ContextLite compares to traditional vector search systems.
                    Run a comparison with any query to see the dramatic difference.
                  </p>
                </div>
                
                <Comparison />
              </div>
            )}
          </motion.div>
        </div>
      </section>

      {/* Features Overview */}
      <section className="py-16 bg-white border-t border-gray-200">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
          <div className="text-center mb-12">
            <h2 className="text-3xl font-bold text-gray-900 mb-4">
              Why ContextLite?
            </h2>
            <p className="text-xl text-gray-600">
              Traditional search falls short. ContextLite understands your code.
            </p>
          </div>

          <div className="grid grid-cols-1 md:grid-cols-3 gap-8">
            <motion.div
              initial={{ opacity: 0, y: 20 }}
              animate={{ opacity: 1, y: 0 }}
              transition={{ delay: 0.1 }}
              className="text-center"
            >
              <div className="w-16 h-16 bg-blue-100 rounded-lg flex items-center justify-center mx-auto mb-4">
                <Zap className="w-8 h-8 text-blue-600" />
              </div>
              <h3 className="text-xl font-semibold text-gray-900 mb-2">Lightning Fast</h3>
              <p className="text-gray-600">
                Get results in milliseconds, not seconds. 1500x faster than traditional vector search.
              </p>
            </motion.div>

            <motion.div
              initial={{ opacity: 0, y: 20 }}
              animate={{ opacity: 1, y: 0 }}
              transition={{ delay: 0.2 }}
              className="text-center"
            >
              <div className="w-16 h-16 bg-green-100 rounded-lg flex items-center justify-center mx-auto mb-4">
                <Target className="w-8 h-8 text-green-600" />
              </div>
              <h3 className="text-xl font-semibold text-gray-900 mb-2">Code-Aware</h3>
              <p className="text-gray-600">
                Understands code structure, syntax, and context. Find exactly what you're looking for.
              </p>
            </motion.div>

            <motion.div
              initial={{ opacity: 0, y: 20 }}
              animate={{ opacity: 1, y: 0 }}
              transition={{ delay: 0.3 }}
              className="text-center"
            >
              <div className="w-16 h-16 bg-purple-100 rounded-lg flex items-center justify-center mx-auto mb-4">
                <Clock className="w-8 h-8 text-purple-600" />
              </div>
              <h3 className="text-xl font-semibold text-gray-900 mb-2">Instant Setup</h3>
              <p className="text-gray-600">
                2-minute setup vs hours of configuration. Download and start searching immediately.
              </p>
            </motion.div>
          </div>
        </div>
      </section>

      {/* CTA Section */}
      <section className="py-16 bg-gradient-to-r from-blue-600 to-purple-600">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 text-center">
          <motion.div
            initial={{ opacity: 0, y: 20 }}
            animate={{ opacity: 1, y: 0 }}
            className="space-y-6"
          >
            <h2 className="text-3xl font-bold text-white">
              Ready to Transform Your Code Search?
            </h2>
            <p className="text-xl text-blue-100 max-w-2xl mx-auto">
              Join thousands of developers who've revolutionized their workflow with ContextLite.
              Download now and experience the difference.
            </p>
            <div className="flex flex-col sm:flex-row gap-4 justify-center items-center">
              <a
                href="https://contextlite.com/download"
                className="flex items-center space-x-2 px-8 py-4 bg-white text-blue-600 rounded-lg hover:bg-gray-50 transition-colors font-semibold"
              >
                <Download className="w-5 h-5" />
                <span>Download ContextLite</span>
              </a>
              <a
                href="https://contextlite.com"
                className="flex items-center space-x-2 px-8 py-4 border-2 border-white text-white rounded-lg hover:bg-white hover:text-blue-600 transition-colors"
              >
                <span>Learn More</span>
                <ArrowRight className="w-5 h-5" />
              </a>
            </div>
          </motion.div>
        </div>
      </section>

      {/* Tutorial Modal */}
      <Tutorial
        isOpen={showTutorial}
        onClose={handleTutorialClose}
        onRunCommand={handleRunCommand}
        onHighlight={handleHighlight}
      />
    </div>
  );
}
