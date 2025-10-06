import { beforeAll, afterAll, describe, expect, it } from 'vitest';
import { mkdtemp, rm, readFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import http from 'node:http';

const fetchScript = join(process.cwd(), 'scripts/trace/fetch-otlp-payload.mjs');
const execFileAsync = promisify(execFile);

describe('stage2 presigned URL integration', () => {
  let server;
  let serverUrl;

  beforeAll(async () => {
    const payload = JSON.stringify({ trace: 'kvonce-stage2' });
    server = http.createServer((req, res) => {
      if (req.url === '/kvonce.json?token=test') {
        res.writeHead(200, { 'content-type': 'application/json' });
        res.end(payload);
      } else {
        res.writeHead(404);
        res.end();
      }
    });
    await new Promise((resolve) => server.listen(0, resolve));
    const address = server.address();
    serverUrl = `http://127.0.0.1:${address.port}/kvonce.json?token=test`;
  });

  afterAll(async () => {
    await new Promise((resolve) => server.close(resolve));
  });

  it('downloads payload via KVONCE_OTLP_PAYLOAD_URL env', async () => {
    const workdir = await mkdtemp(join(tmpdir(), 'stage2-presigned-'));
    try {
      const result = await execFileAsync(process.execPath, [fetchScript, '--target', 'download.json'], {
        cwd: workdir,
        env: {
          ...process.env,
          KVONCE_OTLP_PAYLOAD_URL: serverUrl
        },
        encoding: 'utf8'
      }).catch((error) => {
        console.error('stderr:', error.stderr);
        console.error('stdout:', error.stdout);
        throw error;
      });

      expect(result.stderr).toBe('');
      const payload = JSON.parse(await readFile(join(workdir, 'download.json'), 'utf8'));
      expect(payload.trace).toBe('kvonce-stage2');
      const metadata = JSON.parse(await readFile(join(workdir, 'kvonce-payload-metadata.json'), 'utf8'));
      expect(metadata.sourceType).toBe('url');
    } finally {
      await rm(workdir, { recursive: true, force: true });
    }
  });
});
