#!/usr/bin/env node

import { spawn } from 'child_process';

// ae-ui scaffold command - alias for ae-framework ui-scaffold
const args = process.argv.slice(2);

// Check if first argument is 'scaffold'
if (args.length > 0 && args[0] === 'scaffold') {
  // ae-ui scaffold -> ae-framework ui-scaffold
  const remainingArgs = args.slice(1);
  const mainCLI = spawn('npx', ['ae-framework', 'ui-scaffold', ...remainingArgs], {
    stdio: 'inherit',
    shell: true
  });
  
  mainCLI.on('close', (code) => {
    process.exit(code || 0);
  });
} else {
  // Show help or delegate with default components flag
  console.log(`
Usage: ae-ui scaffold [options]

Alias for 'ae-framework ui-scaffold'

Examples:
  ae-ui scaffold --components     Generate React components
  ae-ui scaffold --state         Design state architecture  
  ae-ui scaffold --tokens        Integrate design tokens
  ae-ui scaffold --a11y          Validate accessibility

For full help: npx ae-framework ui-scaffold --help
`);
}