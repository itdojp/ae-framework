import fs from 'fs';
import path from 'path';
import { fileURLToPath, pathToFileURL } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const repoRoot = path.resolve(__dirname, '..', '..');
const distMain = path.join(repoRoot, 'dist', 'src', 'runner', 'main.js');

if (!fs.existsSync(distMain)) {
  console.error('Build artifacts not found at:', distMain);
  console.error('Please run: pnpm build');
  process.exit(1);
}

const { main } = await import(pathToFileURL(distMain).href);
main().catch((err) => { console.error(err); process.exit(1); });
