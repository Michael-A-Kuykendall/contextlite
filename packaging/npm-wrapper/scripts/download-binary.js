const fs = require('fs');
const path = require('path');
const os = require('os');
const https = require('https');
const tar = require('tar');
const yauzl = require('yauzl');

const GITHUB_API_URL = 'https://api.github.com/repos/Michael-A-Kuykendall/contextlite/releases/latest';

function getPlatformInfo() {
  const platform = os.platform();
  const arch = os.arch();
  
  // Map Node.js platform names to Go platform names
  const platformMap = {
    'darwin': 'darwin',
    'linux': 'linux',
    'win32': 'windows'
  };
  
  // Map Node.js arch names to Go arch names
  const archMap = {
    'x64': 'amd64',
    'arm64': 'arm64'
  };
  
  const goPlatform = platformMap[platform];
  const goArch = archMap[arch] || 'amd64';
  
  if (!goPlatform) {
    throw new Error(`Unsupported platform: ${platform}`);
  }
  
  return { platform: goPlatform, arch: goArch };
}

function downloadFile(url, dest) {
  return new Promise((resolve, reject) => {
    const file = fs.createWriteStream(dest);
    
    https.get(url, (response) => {
      if (response.statusCode === 302 || response.statusCode === 301) {
        // Follow redirect
        file.close();
        fs.unlinkSync(dest);
        return downloadFile(response.headers.location, dest).then(resolve).catch(reject);
      }
      
      if (response.statusCode !== 200) {
        file.close();
        fs.unlinkSync(dest);
        return reject(new Error(`HTTP ${response.statusCode}: ${response.statusMessage}`));
      }
      
      response.pipe(file);
      
      file.on('finish', () => {
        file.close();
        resolve();
      });
      
      file.on('error', (err) => {
        file.close();
        fs.unlinkSync(dest);
        reject(err);
      });
    }).on('error', (err) => {
      file.close();
      fs.unlinkSync(dest);
      reject(err);
    });
  });
}

function extractTarGz(archivePath, destDir) {
  return tar.x({
    file: archivePath,
    cwd: destDir
  });
}

function extractZip(archivePath, destDir) {
  return new Promise((resolve, reject) => {
    yauzl.open(archivePath, { lazyEntries: true }, (err, zipfile) => {
      if (err) return reject(err);
      
      zipfile.readEntry();
      zipfile.on('entry', (entry) => {
        const entryPath = path.join(destDir, entry.fileName);
        
        if (/\/$/.test(entry.fileName)) {
          // Directory
          fs.mkdirSync(entryPath, { recursive: true });
          zipfile.readEntry();
        } else {
          // File
          fs.mkdirSync(path.dirname(entryPath), { recursive: true });
          
          zipfile.openReadStream(entry, (err, readStream) => {
            if (err) return reject(err);
            
            const writeStream = fs.createWriteStream(entryPath);
            readStream.pipe(writeStream);
            
            writeStream.on('close', () => {
              // Make executable on Unix-like systems
              if (os.platform() !== 'win32' && entry.fileName.includes('contextlite')) {
                fs.chmodSync(entryPath, 0o755);
              }
              zipfile.readEntry();
            });
            
            writeStream.on('error', reject);
          });
        }
      });
      
      zipfile.on('end', resolve);
      zipfile.on('error', reject);
    });
  });
}

async function downloadBinary() {
  try {
    console.log('Downloading ContextLite binary...');
    
    // Get latest release info
    const response = await new Promise((resolve, reject) => {
      https.get(GITHUB_API_URL, { headers: { 'User-Agent': 'contextlite-npm' } }, resolve)
        .on('error', reject);
    });
    
    let data = '';
    response.on('data', chunk => data += chunk);
    
    const releaseInfo = await new Promise((resolve, reject) => {
      response.on('end', () => {
        try {
          resolve(JSON.parse(data));
        } catch (err) {
          reject(err);
        }
      });
      response.on('error', reject);
    });
    
    const { platform, arch } = getPlatformInfo();
    const binaryName = platform === 'windows' ? 'contextlite.exe' : 'contextlite';
    const extension = platform === 'windows' ? '.zip' : '.tar.gz';
    
    // Find matching asset
    const assetName = `contextlite_${platform}_${arch}${extension}`;
    const asset = releaseInfo.assets.find(a => a.name === assetName);
    
    if (!asset) {
      throw new Error(`No binary found for ${platform}/${arch}`);
    }
    
    console.log(`Found ${asset.name} (${(asset.size / 1024 / 1024).toFixed(1)}MB)`);
    
    // Create bin directory
    const binDir = path.join(__dirname, '..', 'bin');
    fs.mkdirSync(binDir, { recursive: true });
    
    // Download archive
    const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'contextlite-'));
    const archivePath = path.join(tempDir, asset.name);
    
    await downloadFile(asset.browser_download_url, archivePath);
    console.log('Download complete, extracting...');
    
    // Extract archive
    if (platform === 'windows') {
      await extractZip(archivePath, tempDir);
    } else {
      await extractTarGz(archivePath, tempDir);
    }
    
    // Find and copy binary
    const findBinary = (dir) => {
      const items = fs.readdirSync(dir);
      for (const item of items) {
        const itemPath = path.join(dir, item);
        const stat = fs.statSync(itemPath);
        
        if (stat.isDirectory()) {
          const found = findBinary(itemPath);
          if (found) return found;
        } else if (item === binaryName) {
          return itemPath;
        }
      }
      return null;
    };
    
    const binaryPath = findBinary(tempDir);
    if (!binaryPath) {
      throw new Error(`Binary ${binaryName} not found in archive`);
    }
    
    const destPath = path.join(binDir, binaryName);
    fs.copyFileSync(binaryPath, destPath);
    
    // Make executable on Unix-like systems
    if (platform !== 'windows') {
      fs.chmodSync(destPath, 0o755);
    }
    
    // Cleanup
    fs.rmSync(tempDir, { recursive: true, force: true });
    
    console.log(`ContextLite ${releaseInfo.tag_name} installed successfully`);
    
  } catch (error) {
    console.error('Failed to download ContextLite binary:', error.message);
    console.error('You can manually download from: https://github.com/Michael-A-Kuykendall/contextlite/releases/latest');
    // Don't exit with error code - allow installation to continue
  }
}

if (require.main === module) {
  downloadBinary();
}

module.exports = { downloadBinary };
