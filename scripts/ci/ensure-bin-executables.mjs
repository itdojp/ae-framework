import fs from 'node:fs';
import path from 'node:path';

const repoRoot = process.cwd();
const EXECUTABLE_MASK = 0o111;
const pkgPath = path.join(repoRoot, 'package.json');
const packageJson = JSON.parse(fs.readFileSync(pkgPath, 'utf8'));
const binEntries = packageJson.bin ?? {};

if (Object.keys(binEntries).length === 0) {
  process.exit(0);
}

let exitCode = 0;
for (const [name, relativeLocation] of Object.entries(binEntries)) {
  const resolved = path.join(repoRoot, relativeLocation);
  if (!fs.existsSync(resolved)) {
    console.error(`[bins] Missing entry for ${name}: ${relativeLocation}`);
    exitCode = 1;
    continue;
  }

  try {
    const stats = fs.statSync(resolved);
    if (!stats.isFile()) {
      console.error(`[bins] Not a file for ${name}: ${relativeLocation}`);
      exitCode = 1;
      continue;
    }

    const currentMode = stats.mode & 0o777;
    if ((currentMode & EXECUTABLE_MASK) === 0) {
      const desiredMode = currentMode | EXECUTABLE_MASK;
      fs.chmodSync(resolved, desiredMode);
      console.log(`[bins] Applied executable bit to ${name}: ${relativeLocation}`);
    } else {
      console.log(`[bins] Already executable: ${name}`);
    }
  } catch (error) {
    console.error(`[bins] Failed to ensure executable for ${name}:`, error);
    exitCode = 1;
  }
}

process.exitCode = exitCode;
