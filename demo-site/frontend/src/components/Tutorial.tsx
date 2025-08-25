'use client';

import { useState } from 'react';
import { motion, AnimatePresence } from 'framer-motion';
import { X, ChevronRight, Play, Download } from 'lucide-react';

interface TutorialStep {
  id: string;
  title: string;
  description: string;
  command?: string;
  highlight?: string;
}

const tutorialSteps: TutorialStep[] = [
  {
    id: 'welcome',
    title: 'Welcome to ContextLite!',
    description: 'This interactive demo shows how ContextLite revolutionizes code search. No setup required - everything runs in your browser!',
  },
  {
    id: 'search',
    title: 'Lightning-fast search',
    description: 'Try searching for code in our React component library. Notice the instant results.',
    command: 'contextlite search "button component"',
    highlight: 'terminal'
  },
  {
    id: 'explain',
    title: 'Smart code analysis',
    description: 'ContextLite doesn\'t just find code - it understands it. Try explaining a component.',
    command: 'contextlite explain components/Button/',
    highlight: 'terminal'
  },
  {
    id: 'compare',
    title: 'See the difference',
    description: 'Compare ContextLite with traditional vector search. The performance difference is dramatic.',
    highlight: 'comparison'
  },
  {
    id: 'ready',
    title: 'Ready to try ContextLite?',
    description: 'Download ContextLite and transform your codebase search experience. Available for Windows, macOS, and Linux.',
  }
];

interface TutorialProps {
  isOpen: boolean;
  onClose: () => void;
  onRunCommand?: (command: string) => void;
  onHighlight?: (element: string) => void;
}

export default function Tutorial({ isOpen, onClose, onRunCommand, onHighlight }: TutorialProps) {
  const [currentStep, setCurrentStep] = useState(0);
  const [isCompleted, setIsCompleted] = useState(false);

  const nextStep = () => {
    if (currentStep < tutorialSteps.length - 1) {
      setCurrentStep(currentStep + 1);
      const step = tutorialSteps[currentStep + 1];
      if (step.highlight && onHighlight) {
        onHighlight(step.highlight);
      }
    } else {
      setIsCompleted(true);
    }
  };

  const prevStep = () => {
    if (currentStep > 0) {
      setCurrentStep(currentStep - 1);
      const step = tutorialSteps[currentStep - 1];
      if (step.highlight && onHighlight) {
        onHighlight(step.highlight);
      }
    }
  };

  const runCommand = () => {
    const step = tutorialSteps[currentStep];
    if (step.command && onRunCommand) {
      onRunCommand(step.command);
    }
    nextStep();
  };

  const closeTutorial = () => {
    if (onHighlight) {
      onHighlight('');
    }
    onClose();
  };

  const step = tutorialSteps[currentStep];

  return (
    <AnimatePresence>
      {isOpen && (
        <>
          {/* Backdrop */}
          <motion.div
            initial={{ opacity: 0 }}
            animate={{ opacity: 1 }}
            exit={{ opacity: 0 }}
            className="fixed inset-0 bg-black bg-opacity-50 z-40"
            onClick={closeTutorial}
          />

          {/* Tutorial Modal */}
          <motion.div
            initial={{ opacity: 0, scale: 0.9, y: 20 }}
            animate={{ opacity: 1, scale: 1, y: 0 }}
            exit={{ opacity: 0, scale: 0.9, y: 20 }}
            className="fixed top-1/2 left-1/2 transform -translate-x-1/2 -translate-y-1/2 bg-white rounded-lg shadow-xl z-50 w-full max-w-md mx-4"
          >
            {/* Header */}
            <div className="flex items-center justify-between p-6 border-b border-gray-200">
              <div className="flex items-center space-x-3">
                <div className="w-8 h-8 bg-blue-600 rounded-lg flex items-center justify-center">
                  <span className="text-white font-bold text-sm">{currentStep + 1}</span>
                </div>
                <div>
                  <h3 className="text-lg font-semibold text-gray-900">{step.title}</h3>
                  <p className="text-sm text-gray-500">
                    Step {currentStep + 1} of {tutorialSteps.length}
                  </p>
                </div>
              </div>
              <button
                onClick={closeTutorial}
                className="text-gray-400 hover:text-gray-600 transition-colors"
              >
                <X className="w-6 h-6" />
              </button>
            </div>

            {/* Content */}
            <div className="p-6">
              <p className="text-gray-700 mb-6 leading-relaxed">
                {step.description}
              </p>

              {/* Command to run */}
              {step.command && (
                <div className="bg-gray-900 rounded-lg p-4 mb-6">
                  <div className="flex items-center justify-between">
                    <code className="text-green-400 font-mono text-sm">
                      $ {step.command}
                    </code>
                    <button
                      onClick={runCommand}
                      className="ml-3 px-3 py-1 bg-blue-600 text-white rounded text-sm hover:bg-blue-700 transition-colors flex items-center space-x-1"
                    >
                      <Play className="w-3 h-3" />
                      <span>Run</span>
                    </button>
                  </div>
                </div>
              )}

              {/* Progress bar */}
              <div className="mb-6">
                <div className="flex justify-between text-sm text-gray-500 mb-2">
                  <span>Progress</span>
                  <span>{Math.round(((currentStep + 1) / tutorialSteps.length) * 100)}%</span>
                </div>
                <div className="w-full bg-gray-200 rounded-full h-2">
                  <motion.div
                    initial={{ width: 0 }}
                    animate={{ width: `${((currentStep + 1) / tutorialSteps.length) * 100}%` }}
                    className="bg-blue-600 h-2 rounded-full transition-all duration-300"
                  />
                </div>
              </div>

              {/* Special content for final step */}
              {isCompleted && (
                <motion.div
                  initial={{ opacity: 0, y: 10 }}
                  animate={{ opacity: 1, y: 0 }}
                  className="text-center space-y-4"
                >
                  <div className="w-16 h-16 bg-green-100 rounded-full flex items-center justify-center mx-auto">
                    <span className="text-2xl">🎉</span>
                  </div>
                  <h4 className="text-xl font-semibold text-gray-900">
                    Tutorial Complete!
                  </h4>
                  <p className="text-gray-600">
                    You've seen how ContextLite transforms code search. Ready to try it on your own codebase?
                  </p>
                  <a
                    href="https://contextlite.com/download"
                    target="_blank"
                    rel="noopener noreferrer"
                    className="inline-flex items-center space-x-2 px-6 py-3 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
                  >
                    <Download className="w-4 h-4" />
                    <span>Download ContextLite</span>
                  </a>
                </motion.div>
              )}
            </div>

            {/* Footer */}
            {!isCompleted && (
              <div className="flex items-center justify-between p-6 border-t border-gray-200">
                <button
                  onClick={prevStep}
                  disabled={currentStep === 0}
                  className="px-4 py-2 text-gray-600 hover:text-gray-800 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
                >
                  Previous
                </button>
                <div className="flex space-x-1">
                  {tutorialSteps.map((_, index) => (
                    <div
                      key={index}
                      className={`w-2 h-2 rounded-full transition-colors ${
                        index <= currentStep ? 'bg-blue-600' : 'bg-gray-300'
                      }`}
                    />
                  ))}
                </div>
                <button
                  onClick={step.command ? runCommand : nextStep}
                  className="px-4 py-2 bg-blue-600 text-white rounded hover:bg-blue-700 transition-colors flex items-center space-x-1"
                >
                  <span>{step.command ? 'Run & Continue' : 'Next'}</span>
                  <ChevronRight className="w-4 h-4" />
                </button>
              </div>
            )}
          </motion.div>
        </>
      )}
    </AnimatePresence>
  );
}
