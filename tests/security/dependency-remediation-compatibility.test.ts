import { createRequire } from 'node:module';
import { readdirSync, readFileSync, realpathSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { describe, expect, it } from 'vitest';

const repoRoot = resolve('.');
const virtualStore = join(repoRoot, 'node_modules', '.pnpm');

function packageRoots(name: string, version: string): string[] {
  const prefix = `${name}@${version}`;
  return readdirSync(virtualStore)
    .filter((entry) => entry === prefix || entry.startsWith(`${prefix}_`))
    .sort()
    .map((entry) => join(virtualStore, entry, 'node_modules', name));
}

function readPackageVersion(packageRoot: string): string {
  const manifest = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')) as {
    version?: string;
  };
  return manifest.version ?? '';
}

function requirePackage(packageRoot: string): unknown {
  const requireFromPackage = createRequire(join(packageRoot, 'package.json'));
  return requireFromPackage(packageRoot);
}

describe('dependency security remediation compatibility', () => {
  it('uses brace-expansion 5.0.8 with a bounded aggregate output length', () => {
    const roots = packageRoots('brace-expansion', '5.0.8');
    expect(roots).toHaveLength(1);
    const { expand } = requirePackage(roots[0]) as {
      expand: (pattern: string, options: { max: number; maxLength: number }) => string[];
    };

    const maxLength = 128;
    const expanded = expand('{a,b}'.repeat(12), { max: 100_000, maxLength });
    const aggregateLength = expanded.reduce((total, value) => total + value.length, 0);
    expect(aggregateLength).toBeLessThanOrEqual(maxLength);
  });

  it.each(['3.1.4', '5.1.8', '9.0.9', '10.2.3'])(
    'keeps minimatch %s brace matching compatible with brace-expansion 5.0.8',
    (version) => {
      const roots = packageRoots('minimatch', version);
      expect(roots).toHaveLength(1);

      const packageRoot = roots[0];
      const loaded = requirePackage(packageRoot) as
        | ((candidate: string, pattern: string) => boolean)
        | {
            minimatch: (candidate: string, pattern: string) => boolean;
            braceExpand: (pattern: string) => string[];
          };
      const minimatch = typeof loaded === 'function' ? loaded : loaded.minimatch;
      const braceExpand = typeof loaded === 'function'
        ? (loaded as typeof loaded & { braceExpand: (pattern: string) => string[] }).braceExpand
        : loaded.braceExpand;

      expect(minimatch('src/index.ts', 'src/{index,test}.ts')).toBe(true);
      expect(minimatch('src/other.ts', 'src/{index,test}.ts')).toBe(false);
      expect(braceExpand('src/{index,test}.ts')).toEqual(['src/index.ts', 'src/test.ts']);

      const requireFromMinimatch = createRequire(join(packageRoot, 'package.json'));
      const braceManifestPath = requireFromMinimatch.resolve('brace-expansion/package.json');
      expect(readPackageVersion(realpathSync(join(braceManifestPath, '..')))).toBe('5.0.8');
    },
  );

  it('keeps Fastify routing compatible with find-my-way 9.7.0', async () => {
    const fastifyRoots = packageRoots('fastify', '5.10.0');
    expect(fastifyRoots).toHaveLength(1);
    const fastifyModule = requirePackage(fastifyRoots[0]) as () => {
      get: (path: string, handler: () => unknown) => void;
      inject: (request: { method: string; url: string }) => Promise<{ statusCode: number; json: () => unknown }>;
      close: () => Promise<void>;
    };
    const app = fastifyModule();
    app.get('/health', () => ({ status: 'ok' }));

    const response = await app.inject({ method: 'GET', url: '/health' });
    expect(response.statusCode).toBe(200);
    expect(response.json()).toEqual({ status: 'ok' });
    await app.close();

    expect(packageRoots('find-my-way', '9.7.0')).toHaveLength(1);
  });

  it('keeps PostCSS processing compatible with the patched 8.5 line', async () => {
    const roots = packageRoots('postcss', '8.5.25');
    expect(roots).toHaveLength(1);
    const postcss = requirePackage(roots[0]) as () => {
      process: (css: string, options: { from: undefined; map: false }) => Promise<{ css: string }>;
    };

    const result = await postcss().process('a { color: red; }', { from: undefined, map: false });
    expect(result.css).toBe('a { color: red; }');
  });

  it('loads the patched sharp runtime and materializes an image', async () => {
    const roots = packageRoots('sharp', '0.35.3');
    expect(roots.length).toBeGreaterThan(0);
    expect(roots.every((root) => readPackageVersion(root) === '0.35.3')).toBe(true);

    const sharp = requirePackage(roots[0]) as (input: {
      create: { width: number; height: number; channels: number; background: string };
    }) => { png: () => { toBuffer: () => Promise<Buffer> } };
    const output = await sharp({
      create: { width: 1, height: 1, channels: 4, background: '#00000000' },
    }).png().toBuffer();

    expect(output.subarray(1, 4).toString('ascii')).toBe('PNG');
  });
});
