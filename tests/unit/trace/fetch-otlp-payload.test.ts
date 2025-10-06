import { describe, it, expect, afterEach } from 'vitest';
import { mkdtemp, writeFile, readFile, rm, mkdir, readdir } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve, dirname } from 'node:path';
import { createServer } from 'node:http';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);
const nodeBinary = process.execPath;
const envKeys = new Set<string>();
const setEnv = (key: string, value: string | undefined) => {
  if (typeof value === 'undefined') {
    return;
  }
  process.env[key] = value;
  envKeys.add(key);
};

afterEach(() => {
  for (const key of envKeys) {
    delete process.env[key];
  }
  envKeys.clear();
});
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

      await execFileAsync(nodeBinary, [scriptPath, '--target', target, '--explicit', source]);

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
      await execFileAsync(nodeBinary, [scriptPath, '--target', target, '--artifact-dir', artifactDir]);

      const copied = JSON.parse(await readFile(target, 'utf8'));
      expect(copied).toEqual({ keep: true });
    });
  });

  it('uses environment artifact directory fallback', async () => {
    await withTempDir(async (dir) => {
      const artifactDir = join(dir, 'artifact');
      await mkdir(artifactDir, { recursive: true });
      await writeFile(join(artifactDir, 'fallback.json'), JSON.stringify({ viaEnv: 'artifact' }), 'utf8');
      setEnv('KVONCE_OTLP_ARTIFACT_DIR', artifactDir);

      const target = join(dir, 'collected.json');
      const result = await execFileAsync(nodeBinary, [scriptPath, '--target', target]);

      expect(result.stderr).toBe('');
      const copied = JSON.parse(await readFile(target, 'utf8'));
      expect(copied).toEqual({ viaEnv: 'artifact' });
      const metadata = JSON.parse(await readFile(join(dir, 'kvonce-payload-metadata.json'), 'utf8'));
      expect(metadata.sourceType).toBe('artifact');
    });
  });

  it('uses environment explicit file fallback', async () => {
    await withTempDir(async (dir) => {
      const explicit = join(dir, 'explicit.json');
      await writeFile(explicit, JSON.stringify({ viaEnv: 'explicit' }), 'utf8');
      setEnv('KVONCE_OTLP_PAYLOAD_FILE', explicit);

      const target = join(dir, 'collected.json');
      const result = await execFileAsync(nodeBinary, [scriptPath, '--target', target]);

      expect(result.stderr).toBe('');
      const copied = JSON.parse(await readFile(target, 'utf8'));
      expect(copied).toEqual({ viaEnv: 'explicit' });
      const metadata = JSON.parse(await readFile(join(dir, 'kvonce-payload-metadata.json'), 'utf8'));
      expect(metadata.sourceType).toBe('env-file');
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
        await execFileAsync(nodeBinary, [scriptPath, '--target', target, '--url', url]);
      } finally {
        await new Promise<void>((resolve, reject) => {
          server.close((error) => (error ? reject(error) : resolve()));
        });
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
        await execFileAsync(nodeBinary, [scriptPath, '--target', target], {
          env: { ...process.env, KVONCE_OTLP_PAYLOAD_URL: url }
        });
      } finally {
        await new Promise<void>((resolve, reject) => {
          server.close((error) => (error ? reject(error) : resolve()));
        });
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
      const result = await execFileAsync(nodeBinary, [scriptPath, '--target', target]).catch((error) => error);
      expect(result.code).toBe(1);
      const files = await readdir(dir);
      expect(files).not.toContain('output.json');
    });
  });

  it('fetches payload from S3 mock directory', async () => {
    await withTempDir(async (dir) => {
      const mockRoot = join(dir, 's3-mock');
      const bucket = 'kvonce-bucket';
      const key = 'stage2/payload.json';
      const filePath = join(mockRoot, bucket, key);
      await mkdir(dirname(filePath), { recursive: true });
      await writeFile(filePath, JSON.stringify({ via: 's3-mock' }), 'utf8');
      setEnv('KVONCE_OTLP_S3_MOCK_DIR', mockRoot);
      setEnv('KVONCE_OTLP_S3_URI', `s3://${bucket}/${key}`);

      const target = join(dir, 'from-s3.json');
      const result = await execFileAsync(nodeBinary, [scriptPath, '--target', target]);

      expect(result.stderr).toBe('');
      const copied = JSON.parse(await readFile(target, 'utf8'));
      expect(copied).toEqual({ via: 's3-mock' });
      const metadata = JSON.parse(await readFile(join(dir, 'kvonce-payload-metadata.json'), 'utf8'));
      expect(metadata.sourceType).toBe('s3');
      expect(metadata.sourceDetail).toBe(`s3://${bucket}/${key}`);
    });
  });
});
