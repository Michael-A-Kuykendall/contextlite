const { spawn, execFile } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

class ContextLiteError extends Error {
  constructor(message) {
    super(message);
    this.name = 'ContextLiteError';
  }
}

class ContextLite {
  constructor(options = {}) {
    this.binaryPath = options.binaryPath || this._findBinary();
    if (!this.binaryPath) {
      throw new ContextLiteError('ContextLite binary not found. Run: npm run postinstall');
    }
  }

  _findBinary() {
    const binaryName = os.platform() === 'win32' ? 'contextlite.exe' : 'contextlite';
    
    // Check package installation location first
    const packageBinary = path.join(__dirname, 'bin', binaryName);
    if (fs.existsSync(packageBinary)) {
      return packageBinary;
    }

    // Check common locations
    const locations = [
      path.join(os.homedir(), '.local', 'bin', binaryName),
      path.join(os.homedir(), '.contextlite', binaryName),
      '/usr/local/bin/' + binaryName,
      '/usr/bin/' + binaryName,
    ];

    if (os.platform() === 'win32') {
      locations.push(
        path.join(os.homedir(), '.contextlite', 'contextlite.exe'),
        'C:\\Program Files\\ContextLite\\contextlite.exe'
      );
    }

    for (const location of locations) {
      if (fs.existsSync(location)) {
        return location;
      }
    }

    return null;
  }

  _runCommand(args, options = {}) {
    return new Promise((resolve, reject) => {
      const child = spawn(this.binaryPath, args, {
        stdio: ['pipe', 'pipe', 'pipe'],
        ...options
      });

      let stdout = '';
      let stderr = '';

      child.stdout.on('data', (data) => {
        stdout += data.toString();
      });

      child.stderr.on('data', (data) => {
        stderr += data.toString();
      });

      child.on('close', (code) => {
        if (code === 0) {
          resolve({ stdout: stdout.trim(), stderr: stderr.trim() });
        } else {
          reject(new ContextLiteError(`Command failed with code ${code}: ${stderr}`));
        }
      });

      child.on('error', (error) => {
        reject(new ContextLiteError(`Failed to start process: ${error.message}`));
      });
    });
  }

  async version() {
    const result = await this._runCommand(['--version']);
    return result.stdout;
  }

  async addDocument(content, options = {}) {
    const args = ['add'];
    
    if (options.id) {
      args.push('--id', options.id);
    }
    
    if (options.metadata) {
      args.push('--metadata', JSON.stringify(options.metadata));
    }
    
    args.push(content);
    
    const result = await this._runCommand(args);
    return result.stdout;
  }

  async query(queryText, options = {}) {
    const args = ['query', '--format', 'json'];
    
    if (options.maxResults) {
      args.push('--max-results', options.maxResults.toString());
    }
    
    if (options.noCache) {
      args.push('--no-cache');
    }
    
    args.push(queryText);
    
    const result = await this._runCommand(args);
    
    try {
      return JSON.parse(result.stdout);
    } catch (error) {
      throw new ContextLiteError(`Failed to parse JSON response: ${error.message}`);
    }
  }

  async indexDirectory(directory, options = {}) {
    const args = ['index'];
    
    if (options.recursive !== false) {
      args.push('--recursive');
    }
    
    args.push(directory);
    
    const result = await this._runCommand(args);
    return result.stdout;
  }

  async stats() {
    const result = await this._runCommand(['stats', '--format', 'json']);
    
    try {
      return JSON.parse(result.stdout);
    } catch (error) {
      throw new ContextLiteError(`Failed to parse JSON response: ${error.message}`);
    }
  }

  async clearCache() {
    const result = await this._runCommand(['cache', 'clear']);
    return result.stdout;
  }

  startServer(options = {}) {
    const port = options.port || 8080;
    const args = ['--port', port.toString()];
    
    const child = spawn(this.binaryPath, args, {
      stdio: 'inherit',
      detached: true
    });

    child.unref();
    
    return {
      pid: child.pid,
      port,
      stop: () => {
        try {
          process.kill(child.pid);
        } catch (error) {
          // Process might already be dead
        }
      }
    };
  }
}

// Convenience functions
async function query(queryText, options = {}) {
  const client = new ContextLite();
  return client.query(queryText, options);
}

async function addDocument(content, options = {}) {
  const client = new ContextLite();
  return client.addDocument(content, options);
}

async function indexDirectory(directory, options = {}) {
  const client = new ContextLite();
  return client.indexDirectory(directory, options);
}

module.exports = {
  ContextLite,
  ContextLiteError,
  query,
  addDocument,
  indexDirectory
};
