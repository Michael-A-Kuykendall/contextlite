'use client';

import { useState, useEffect } from 'react';
import { motion } from 'framer-motion';
import { Clock, Target, Zap, TrendingUp } from 'lucide-react';

interface ComparisonResult {
  contextlite: {
    timing: number;
    accuracy: number;
    results: string[];
    setup: string;
  };
  vectorRAG: {
    timing: number;
    accuracy: number;
    results: string[];
    setup: string;
  };
}

interface ComparisonProps {
  query?: string;
  onRunComparison?: (query: string) => Promise<ComparisonResult>;
  className?: string;
}

export default function Comparison({ query = 'authentication middleware', onRunComparison, className }: ComparisonProps) {
  const [isRunning, setIsRunning] = useState(false);
  const [result, setResult] = useState<ComparisonResult | null>(null);
  const [currentQuery, setCurrentQuery] = useState(query);

  useEffect(() => {
    // Auto-run comparison on mount
    runComparison();
  }, []);

  const runComparison = async () => {
    setIsRunning(true);
    try {
      const comparisonResult = onRunComparison 
        ? await onRunComparison(currentQuery)
        : await mockComparison(currentQuery);
      setResult(comparisonResult);
    } catch (error) {
      console.error('Comparison failed:', error);
    }
    setIsRunning(false);
  };

  return (
    <div className={`w-full space-y-6 ${className}`}>
      {/* Query Input */}
      <div className="bg-white rounded-lg border border-gray-200 p-4">
        <label className="block text-sm font-medium text-gray-700 mb-2">
          Search Query
        </label>
        <div className="flex space-x-2">
          <input
            type="text"
            value={currentQuery}
            onChange={(e) => setCurrentQuery(e.target.value)}
            className="flex-1 px-3 py-2 border border-gray-300 rounded-md focus:outline-none focus:ring-2 focus:ring-blue-500"
            placeholder="Enter your search query..."
          />
          <button
            onClick={runComparison}
            disabled={isRunning}
            className="px-4 py-2 bg-blue-600 text-white rounded-md hover:bg-blue-700 disabled:opacity-50 disabled:cursor-not-allowed flex items-center space-x-2"
          >
            {isRunning ? (
              <>
                <div className="w-4 h-4 border-2 border-white border-t-transparent rounded-full animate-spin" />
                <span>Running...</span>
              </>
            ) : (
              <>
                <Zap className="w-4 h-4" />
                <span>Compare</span>
              </>
            )}
          </button>
        </div>
      </div>

      {/* Results Comparison */}
      {result && (
        <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
          {/* ContextLite Results */}
          <motion.div
            initial={{ opacity: 0, x: -20 }}
            animate={{ opacity: 1, x: 0 }}
            className="bg-gradient-to-br from-green-50 to-emerald-50 rounded-lg border border-green-200 p-6"
          >
            <div className="flex items-center space-x-3 mb-4">
              <div className="w-10 h-10 bg-green-600 rounded-lg flex items-center justify-center">
                <Zap className="w-5 h-5 text-white" />
              </div>
              <div>
                <h3 className="text-lg font-semibold text-gray-900">ContextLite</h3>
                <p className="text-sm text-gray-600">AI-Powered Code Search</p>
              </div>
            </div>

            {/* Performance Metrics */}
            <div className="grid grid-cols-2 gap-4 mb-4">
              <div className="bg-white rounded-lg p-3 border border-green-100">
                <div className="flex items-center space-x-2">
                  <Clock className="w-4 h-4 text-green-600" />
                  <span className="text-xs font-medium text-gray-600">Speed</span>
                </div>
                <div className="text-xl font-bold text-green-600">
                  {result.contextlite.timing}ms
                </div>
              </div>
              <div className="bg-white rounded-lg p-3 border border-green-100">
                <div className="flex items-center space-x-2">
                  <Target className="w-4 h-4 text-green-600" />
                  <span className="text-xs font-medium text-gray-600">Accuracy</span>
                </div>
                <div className="text-xl font-bold text-green-600">
                  {result.contextlite.accuracy}%
                </div>
              </div>
            </div>

            {/* Results */}
            <div className="space-y-2">
              <h4 className="font-medium text-gray-900">Results:</h4>
              {result.contextlite.results.map((item, index) => (
                <div key={index} className="bg-white rounded p-2 border border-green-100 text-sm">
                  <code className="text-blue-600">{item}</code>
                </div>
              ))}
            </div>

            <div className="mt-4 text-xs text-gray-600">
              Setup: {result.contextlite.setup}
            </div>
          </motion.div>

          {/* Vector RAG Results */}
          <motion.div
            initial={{ opacity: 0, x: 20 }}
            animate={{ opacity: 1, x: 0 }}
            className="bg-gradient-to-br from-orange-50 to-red-50 rounded-lg border border-orange-200 p-6"
          >
            <div className="flex items-center space-x-3 mb-4">
              <div className="w-10 h-10 bg-orange-600 rounded-lg flex items-center justify-center">
                <TrendingUp className="w-5 h-5 text-white" />
              </div>
              <div>
                <h3 className="text-lg font-semibold text-gray-900">Vector RAG</h3>
                <p className="text-sm text-gray-600">Traditional Semantic Search</p>
              </div>
            </div>

            {/* Performance Metrics */}
            <div className="grid grid-cols-2 gap-4 mb-4">
              <div className="bg-white rounded-lg p-3 border border-orange-100">
                <div className="flex items-center space-x-2">
                  <Clock className="w-4 h-4 text-orange-600" />
                  <span className="text-xs font-medium text-gray-600">Speed</span>
                </div>
                <div className="text-xl font-bold text-orange-600">
                  {result.vectorRAG.timing}ms
                </div>
              </div>
              <div className="bg-white rounded-lg p-3 border border-orange-100">
                <div className="flex items-center space-x-2">
                  <Target className="w-4 h-4 text-orange-600" />
                  <span className="text-xs font-medium text-gray-600">Accuracy</span>
                </div>
                <div className="text-xl font-bold text-orange-600">
                  {result.vectorRAG.accuracy}%
                </div>
              </div>
            </div>

            {/* Results */}
            <div className="space-y-2">
              <h4 className="font-medium text-gray-900">Results:</h4>
              {result.vectorRAG.results.map((item, index) => (
                <div key={index} className="bg-white rounded p-2 border border-orange-100 text-sm">
                  <code className="text-blue-600">{item}</code>
                </div>
              ))}
            </div>

            <div className="mt-4 text-xs text-gray-600">
              Setup: {result.vectorRAG.setup}
            </div>
          </motion.div>
        </div>
      )}

      {/* Performance Summary */}
      {result && (
        <motion.div
          initial={{ opacity: 0, y: 20 }}
          animate={{ opacity: 1, y: 0 }}
          className="bg-gradient-to-r from-blue-50 to-indigo-50 rounded-lg border border-blue-200 p-6"
        >
          <h3 className="text-lg font-semibold text-gray-900 mb-4">Performance Summary</h3>
          <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
            <div className="text-center">
              <div className="text-2xl font-bold text-green-600">
                {Math.round(result.vectorRAG.timing / result.contextlite.timing)}x
              </div>
              <div className="text-sm text-gray-600">Faster Search</div>
            </div>
            <div className="text-center">
              <div className="text-2xl font-bold text-blue-600">
                +{result.contextlite.accuracy - result.vectorRAG.accuracy}%
              </div>
              <div className="text-sm text-gray-600">Better Accuracy</div>
            </div>
            <div className="text-center">
              <div className="text-2xl font-bold text-purple-600">100%</div>
              <div className="text-sm text-gray-600">Code Context</div>
            </div>
          </div>
        </motion.div>
      )}
    </div>
  );
}

// Mock comparison function
async function mockComparison(query: string): Promise<ComparisonResult> {
  // Simulate API delay
  await new Promise(resolve => setTimeout(resolve, 2000));
  
  return {
    contextlite: {
      timing: Math.floor(Math.random() * 5) + 1, // 1-5ms
      accuracy: 94,
      results: [
        'auth/middleware/authenticate.go:15',
        'api/handlers/auth.go:45',
        'models/user.go:123'
      ],
      setup: '2 minutes'
    },
    vectorRAG: {
      timing: Math.floor(Math.random() * 200) + 400, // 400-600ms  
      accuracy: 67,
      results: [
        'docs/authentication.md:1',
        'config/auth.yaml:12',
        'tests/auth_test.go:89'
      ],
      setup: '2+ hours'
    }
  };
}
