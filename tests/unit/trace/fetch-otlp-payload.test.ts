import { describe, it, expect, afterEach } from 'vitest';
import { mkdtemp, writeFile, readFile, rm, mkdir, readdir } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { createServer } from 'node:http';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);
const scriptPath = process.env.KVONCE_FETCH_SCRIPT_PATH
  ? resolve(process.cwd(), process.env.KVONCE_FETCH_SCRIPT_PATH)
  : resolve(process.cwd(), 'scripts/trace/fetch-otlp-payload.mjs');

async function withTempDir<T>(fn: (dir: string) => Promise<T>) {
  const dir = await mkdtemp(join(tmpdir(), 'fetch-otlp-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

describe('fetch-otlp-payload CLI', () => {
  it('copies explicit payload and writes metadata', async () => {
    await withTempDir(async (dir) => {
      const source = join(dir, 'source.json');
      const target = join(dir, 'collected.json');
      await writeFile(source, JSON.stringify({ hello: 'world' }), 'utf8');

      await execFileAsync('node', [scriptPath, '--target', target, '--explicit', source]);

      const copied = JSON.parse(await readFile(target, 'utf8'));
      expect(copied).toEqual({ hello: 'world' });

      const metadata = JSON.parse(await readFile(join(dir, 'kvonce-payload-metadata.json'), 'utf8'));
      expect(metadata.sourceType).toBe('explicit');
      expect(metadata.sha256).toMatch(/^[a-f0-9]{64}$/);
      expect(metadata.sizeBytes).toBeGreaterThan(0);
    });
  });

  it('selects first JSON from artifact directory', async () => {
    await withTempDir(async (dir) => {
      const artifactDir = join(dir, 'artifact');
      await mkdir(artifactDir);
      await writeFile(join(artifactDir, 'other.json'), JSON.stringify({ skip: true }), 'utf8');
      await writeFile(join(artifactDir, 'kvonce-otlp.json'), JSON.stringify({ keep: true }), 'utf8');

      const target = join(dir, 'collected.json');
      await execFileAsync('node', [scriptPath, '--target', target, '--artifact-dir', artifactDir]);

      const copied = JSON.parse(await readFile(target, 'utf8'));
      expect(copied).toEqual({ keep: true });
    });
  });

  it('downloads payload from URL', async () => {
    await withTempDir(async (dir) => {
      const server = createServer((req, res) => {
        res.writeHead(200, { 'content-type': 'application/json' });
        res.end(JSON.stringify({ remote: true }));
      });
      await new Promise((resolveServer) => server.listen(0, resolveServer));
      const address = server.address();
      if (typeof address !== 'object' || !address) {
        throw new Error('server failed to listen');
      }
      const url = `http://127.0.0.1:${address.port}`;

      const target = join(dir, 'downloaded.json');
      try {
        await execFileAsync('node', [scriptPath, '--target', target, '--url', url]);
      } finally {
        server.close();
      }

      const copied = JSON.parse(await readFile(target, 'utf8'));
      expect(copied).toEqual({ remote: true });

      const metadata = JSON.parse(await readFile(join(dir, 'kvonce-payload-metadata.json'), 'utf8'));
      expect(metadata.sourceType).toBe('url');
      expect(metadata.sourceDetail).toBe(url);
    });
  });

  it('uses environment fallbacks when no CLI source is provided', async () => {
    await withTempDir(async (dir) => {
      const server = createServer((req, res) => {
        res.writeHead(200, { 'content-type': 'application/json' });
        res.end(JSON.stringify({ viaEnv: true }));
      });
      await new Promise((resolveServer) => server.listen(0, resolveServer));
      const address = server.address();
      if (typeof address !== 'object' || !address) {
        throw new Error('server failed to listen');
      }
      const url = `http://127.0.0.1:${address.port}`;

      const target = join(dir, 'env-download.json');
      try {
        await execFileAsync('node', [scriptPath, '--target', target], {
          env: { ...process.env, KVONCE_OTLP_PAYLOAD_URL: url }
        });
      } finally {
        server.close();
      }

      const copied = JSON.parse(await readFile(target, 'utf8'));
      expect(copied).toEqual({ viaEnv: true });
      const metadata = JSON.parse(await readFile(join(dir, 'kvonce-payload-metadata.json'), 'utf8'));
      expect(metadata.sourceType).toBe('url');
      expect(metadata.sourceDetail).toBe(url);
    });
  });

  it('fails when no source is provided', async () => {
    await withTempDir(async (dir) => {
      const target = join(dir, 'output.json');
      const result = await execFileAsync('node', [scriptPath, '--target', target]).catch((error) => error);
      expect(result.code).toBe(1);
      const files = await readdir(dir);
      expect(files).not.toContain('output.json');
    });
  });
});
