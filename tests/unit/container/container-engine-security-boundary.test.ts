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
  for (const file of [
    'docker-engine.ts',
    'podman-engine.ts',
  ] as const) {
    it(`${file} uses argv-safe execution for caller-influenced run/build/push/cleanup paths`, () => {
      const source = readSource(file);
      expect(source).toContain('execFileAsync');
      expect(source).not.toContain('execAsync');
      expect(source).not.toContain('promisify(exec)');
      expect(source).not.toMatch(/args\.join\(' '\)/);

      for (const signature of [
        'async createContainer',
        'async startContainer',
        'async stopContainer',
        'async removeContainer',
        'async restartContainer',
        'async runContainer',
        'async executeInContainer',
        'async getContainerStatus',
        'async listContainers',
        'async getContainerStats',
        'async buildImage',
        'async pullImage',
        'async pushImage',
        'async removeImage',
        'async listImages',
        'async tagImage',
        'async createVolume',
        'async removeVolume',
        'async listVolumes',
        'async createNetwork',
        'async removeNetwork',
        'async listNetworks',
        'async runCompose',
        'async stopCompose',
        'async cleanup',
      ]) {
        const body = methodBody(source, signature);
        expect(body).toContain('execFileAsync(');
        expect(body).not.toMatch(/execAsync\(`\$\{this\.(?:dockerPath|podmanPath)\}/);
        expect(body).not.toMatch(/(?:container|image|volume|network) prune \$\{/);
      }
    });

    it(`${file} defaults cleanup prune filters to ae-framework-managed resources`, () => {
      const body = methodBody(readSource(file), 'async cleanup');
      expect(body).toContain('AE_CONTAINER_LABEL_FILTER');
      expect(body).toContain('scopedLabelFilters');
      expect(body).toContain("[AE_CONTAINER_LABEL_FILTER]");
    });

    it(`${file} redacts build args from build-image events and errors`, () => {
      const body = methodBody(readSource(file), 'async buildImage');
      expect(body).toContain('redactImageBuildContext(buildContext)');
      expect(body).not.toContain('buildContext\n');
    });
  }
});
