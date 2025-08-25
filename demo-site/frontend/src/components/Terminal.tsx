'use client';

import { useEffect, useRef, useState } from 'react';
import { Terminal as XTerm } from '@xterm/xterm';
import { FitAddon } from '@xterm/addon-fit';
import { WebLinksAddon } from '@xterm/addon-web-links';
import '@xterm/xterm/css/xterm.css';

interface TerminalProps {
  onCommand?: (command: string) => Promise<string>;
  dataset?: string;
  className?: string;
}

export default function Terminal({ onCommand, dataset = 'react-components', className }: TerminalProps) {
  const terminalRef = useRef<HTMLDivElement>(null);
  const xtermRef = useRef<XTerm | null>(null);
  const fitAddonRef = useRef<FitAddon | null>(null);
  const [currentLine, setCurrentLine] = useState('');
  const [isProcessing, setIsProcessing] = useState(false);

  useEffect(() => {
    if (!terminalRef.current) return;

    // Initialize xterm
    const terminal = new XTerm({
      theme: {
        background: '#0f172a',
        foreground: '#e2e8f0',
        cursor: '#06b6d4',
        selection: '#334155',
        black: '#1e293b',
        red: '#ef4444',
        green: '#10b981',
        yellow: '#f59e0b',
        blue: '#3b82f6',
        magenta: '#8b5cf6',
        cyan: '#06b6d4',
        white: '#f1f5f9',
        brightBlack: '#475569',
        brightRed: '#f87171',
        brightGreen: '#34d399',
        brightYellow: '#fbbf24',
        brightBlue: '#60a5fa',
        brightMagenta: '#a78bfa',
        brightCyan: '#22d3ee',
        brightWhite: '#ffffff'
      },
      fontSize: 14,
      fontFamily: 'JetBrains Mono, Consolas, Monaco, monospace',
      cursorBlink: true,
      cursorStyle: 'block',
      scrollback: 1000,
      tabStopWidth: 4,
    });

    const fitAddon = new FitAddon();
    const webLinksAddon = new WebLinksAddon();
    
    terminal.loadAddon(fitAddon);
    terminal.loadAddon(webLinksAddon);
    
    terminal.open(terminalRef.current);
    fitAddon.fit();

    xtermRef.current = terminal;
    fitAddonRef.current = fitAddon;

    // Welcome message
    terminal.writeln('\\x1b[1;32m🚀 ContextLite Demo Terminal\\x1b[0m');
    terminal.writeln('\\x1b[90mDataset: ' + dataset + '\\x1b[0m');
    terminal.writeln('\\x1b[90mTry: contextlite search "button component"\\x1b[0m');
    terminal.writeln('');
    writePrompt();

    // Handle input
    terminal.onData((data) => {
      if (isProcessing) return;

      switch (data) {
        case '\\r': // Enter
          if (currentLine.trim()) {
            handleCommand(currentLine.trim());
          } else {
            terminal.writeln('');
            writePrompt();
          }
          break;
        case '\\u007F': // Backspace
          if (currentLine.length > 0) {
            setCurrentLine(currentLine.slice(0, -1));
            terminal.write('\\b \\b');
          }
          break;
        case '\\u0003': // Ctrl+C
          terminal.writeln('^C');
          setCurrentLine('');
          writePrompt();
          break;
        default:
          if (data >= ' ' && data <= '~') {
            setCurrentLine(currentLine + data);
            terminal.write(data);
          }
          break;
      }
    });

    function writePrompt() {
      terminal.write('\\x1b[1;36m$ \\x1b[0m');
    }

    async function handleCommand(command: string) {
      terminal.writeln('');
      setIsProcessing(true);
      
      try {
        const result = onCommand ? await onCommand(command) : await mockCommand(command);
        terminal.writeln(result);
      } catch (error) {
        terminal.writeln('\\x1b[31mError: ' + (error as Error).message + '\\x1b[0m');
      }
      
      setCurrentLine('');
      setIsProcessing(false);
      writePrompt();
    }

    // Handle resize
    const handleResize = () => {
      fitAddon.fit();
    };
    
    window.addEventListener('resize', handleResize);

    return () => {
      window.removeEventListener('resize', handleResize);
      terminal.dispose();
    };
  }, [dataset, onCommand, currentLine, isProcessing]);

  return (
    <div className={`w-full h-full bg-slate-900 rounded-lg border border-slate-700 ${className}`}>
      <div className="flex items-center justify-between p-3 bg-slate-800 rounded-t-lg border-b border-slate-700">
        <div className="flex space-x-2">
          <div className="w-3 h-3 bg-red-500 rounded-full"></div>
          <div className="w-3 h-3 bg-yellow-500 rounded-full"></div>
          <div className="w-3 h-3 bg-green-500 rounded-full"></div>
        </div>
        <div className="text-sm text-slate-400 font-mono">
          ContextLite Demo Terminal
        </div>
        <div className="text-xs text-slate-500">
          Dataset: {dataset}
        </div>
      </div>
      <div ref={terminalRef} className="p-4 h-[calc(100%-60px)]" />
    </div>
  );
}

// Mock command execution for demo
async function mockCommand(command: string): Promise<string> {
  await new Promise(resolve => setTimeout(resolve, 300)); // Simulate processing
  
  if (command.startsWith('contextlite search')) {
    const query = command.match(/"([^"]+)"/)?.[1] || command.split(' ').slice(2).join(' ');
    return `\\x1b[32m🔍 Found 3 matches in 0.3ms:\\x1b[0m

\\x1b[94m📁 components/Button/Button.tsx:15\\x1b[0m
   export const Button: FC<ButtonProps> = ({ children, variant = 'primary' }) => {

\\x1b[94m📁 components/Button/Button.stories.tsx:8\\x1b[0m
   export const PrimaryButton = () => <Button variant="primary">Click me</Button>;

\\x1b[94m📁 components/IconButton/IconButton.tsx:12\\x1b[0m
   export const IconButton: FC<IconButtonProps> = ({ icon, ...props }) => {

\\x1b[90m💡 Try: contextlite explain components/Button/\\x1b[0m`;
  }
  
  if (command.startsWith('contextlite explain')) {
    return `\\x1b[32m📖 Code Analysis:\\x1b[0m

\\x1b[1mButton Component Structure:\\x1b[0m
- TypeScript React component with variants
- Supports primary, secondary, danger styles  
- Uses Tailwind CSS for styling
- Includes accessibility props (aria-label)
- Has comprehensive Storybook stories

\\x1b[1mKey Features:\\x1b[0m
- ✅ Responsive design
- ✅ Dark mode support
- ✅ Loading states
- ✅ Icon support

\\x1b[90mUsage: <Button variant="primary" onClick={handleClick}>Text</Button>\\x1b[0m`;
  }
  
  if (command.startsWith('contextlite analyze')) {
    return `\\x1b[32m📊 Complexity Analysis:\\x1b[0m

\\x1b[1mComponents Directory:\\x1b[0m
- 47 total files
- Average complexity: Low (2.3/10)
- Test coverage: 94%
- TypeScript usage: 100%

\\x1b[1mMaintainability Score: A+\\x1b[0m
\\x1b[90m⚡ Analysis completed in 0.2ms\\x1b[0m`;
  }
  
  return `\\x1b[33mUnknown command: ${command}\\x1b[0m
\\x1b[90mTry: contextlite search "query", contextlite explain path/, contextlite analyze path/\\x1b[0m`;
}
