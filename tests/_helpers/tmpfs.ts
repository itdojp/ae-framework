import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';

export function createTempDir(prefix = 'ae-test-'): string {
  return fs.mkdtempSync(path.join(os.tmpdir(), prefix));
}

export function writeTempJson(dir: string, filename: string, obj: unknown): string {
  const filePath = path.join(dir, filename);
  fs.writeFileSync(filePath, JSON.stringify(obj, null, 2), 'utf8');
  return filePath;
}

export function rmrf(targetPath: string | undefined | null): void {
  if (!targetPath) return;
  try {
    fs.rmSync(targetPath, { recursive: true, force: true });
  } catch {
    // ignore cleanup errors
  }
}
