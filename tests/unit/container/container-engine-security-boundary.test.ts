import * as fs from 'node:fs';
import * as path from 'node:path';
import { describe, expect, it } from 'vitest';

const readSource = (name: string) => fs.readFileSync(path.resolve(process.cwd(), 'src/services/container', name), 'utf8');

const methodBody = (source: string, signature: string) => {
  const start = source.indexOf(signature);
  if (start < 0) throw new Error(`method not found: ${signature}`);
  const next = source.indexOf('\n  async ', start + signature.length);
  return source.slice(start, next < 0 ? source.length : next);
};

describe('container engine security boundaries', () => {
  for (const [file, executable] of [
    ['docker-engine.ts', 'this.dockerPath'],
    ['podman-engine.ts', 'this.podmanPath'],
  ] as const) {
    it(`${file} uses argv-safe execution for caller-influenced run/build/push/cleanup paths`, () => {
      const source = readSource(file);
      expect(source).toContain('execFileAsync');

      for (const signature of ['async runContainer', 'async buildImage', 'async pushImage', 'async cleanup']) {
        const body = methodBody(source, signature);
        expect(body).toContain(`execFileAsync(${executable}`);
        expect(body).not.toMatch(/execAsync\(`\$\{this\.(?:dockerPath|podmanPath)\} \$\{args\.join\(' '\)\}`/);
        expect(body).not.toMatch(/execAsync\(`\$\{this\.(?:dockerPath|podmanPath)\} push/);
        expect(body).not.toMatch(/(?:container|image|volume|network) prune \$\{/);
      }
    });

    it(`${file} redacts build args from build-image events and errors`, () => {
      const body = methodBody(readSource(file), 'async buildImage');
      expect(body).toContain('redactImageBuildContext(buildContext)');
      expect(body).not.toContain('buildContext\n');
    });
  }
});
