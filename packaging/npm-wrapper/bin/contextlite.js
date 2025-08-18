#!/usr/bin/env node

const { ContextLite } = require('../index');

async function main() {
  try {
    const client = new ContextLite();
    
    const args = process.argv.slice(2);
    
    if (args.length === 0) {
      console.log('Usage: contextlite <command> [options]');
      console.log('Commands:');
      console.log('  version              Show version');
      console.log('  query <text>         Query for context');
      console.log('  add <content>        Add document');
      console.log('  index <directory>    Index directory');
      console.log('  stats               Show statistics');
      console.log('  cache clear         Clear cache');
      process.exit(1);
    }
    
    const command = args[0];
    
    switch (command) {
      case 'version':
        console.log(await client.version());
        break;
        
      case 'query':
        if (args.length < 2) {
          console.error('Usage: contextlite query <text>');
          process.exit(1);
        }
        const results = await client.query(args[1]);
        console.log(JSON.stringify(results, null, 2));
        break;
        
      case 'add':
        if (args.length < 2) {
          console.error('Usage: contextlite add <content>');
          process.exit(1);
        }
        const addResult = await client.addDocument(args[1]);
        console.log(addResult);
        break;
        
      case 'index':
        if (args.length < 2) {
          console.error('Usage: contextlite index <directory>');
          process.exit(1);
        }
        const indexResult = await client.indexDirectory(args[1]);
        console.log(indexResult);
        break;
        
      case 'stats':
        const stats = await client.stats();
        console.log(JSON.stringify(stats, null, 2));
        break;
        
      case 'cache':
        if (args[1] === 'clear') {
          const clearResult = await client.clearCache();
          console.log(clearResult);
        } else {
          console.error('Usage: contextlite cache clear');
          process.exit(1);
        }
        break;
        
      default:
        console.error(`Unknown command: ${command}`);
        process.exit(1);
    }
  } catch (error) {
    console.error(`Error: ${error.message}`);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}
