const path = require('path');
const fs = require('fs');
const tsx = require('tsx/cjs');

const repoRoot = path.resolve(__dirname, '..', '..');
const tsMain = path.join(repoRoot, 'src', 'runner', 'main.ts');

if (!fs.existsSync(tsMain)) {
  console.error('Source entry not found at:', tsMain);
  process.exit(1);
}

// Use tsx runtime to load TS directly
const { main } = tsx.require(tsMain);
Promise.resolve(main())
  .then(() => process.exit(0))
  .catch((err) => { console.error(err); process.exit(1); });
