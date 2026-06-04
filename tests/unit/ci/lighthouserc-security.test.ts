import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { describe, expect, it } from 'vitest';

const repoRoot = process.cwd();
const configPath = resolve(repoRoot, 'configs/lighthouserc.cjs');
const DEFAULT_LOCAL_URLS = [
  'http://localhost:3000/ja/health',
  'http://localhost:3000/ja/e2e/semantic-form',
];

const writeQualityPolicy = (workdir: string, urls: string[]): void => {
  mkdirSync(join(workdir, 'policy'), { recursive: true });
  writeFileSync(
    join(workdir, 'policy', 'quality.json'),
    JSON.stringify({
      version: 'test',
      environments: {},
      quality: {
        lighthouse: {
          description: 'test lighthouse policy',
          enforcement: 'warn',
          thresholds: {
            performance: 90,
            accessibility: 95,
            bestPractices: 85,
            seo: 80,
            pwa: 'off',
          },
          config: {
            numberOfRuns: 1,
            urls,
          },
        },
      },
    }),
  );
};

const loadLighthouseConfigForUrls = (urls: string[]): string[] => {
  const workdir = mkdtempSync(join(tmpdir(), 'lighthouserc-security-'));
  try {
    writeQualityPolicy(workdir, urls);
    const script = [
      `const config = require(${JSON.stringify(configPath)});`,
      `process.stdout.write('\\n__COLLECT_URLS__' + JSON.stringify(config.ci.collect.url) + '\\n');`,
    ].join('\n');
    const output = execFileSync(process.execPath, ['-e', script], {
      cwd: workdir,
      encoding: 'utf8',
    });
    const markerLine = output.split(/\r?\n/).find((line) => line.startsWith('__COLLECT_URLS__'));
    if (!markerLine) {
      throw new Error(`Missing collect URL marker in lighthouserc output: ${output}`);
    }
    return JSON.parse(markerLine.slice('__COLLECT_URLS__'.length)) as string[];
  } finally {
    rmSync(workdir, { recursive: true, force: true });
  }
};

describe('lighthouserc collect URL security policy', () => {
  it('accepts only the locally started Lighthouse app origin after legacy route remapping', () => {
    const urls = loadLighthouseConfigForUrls([
      'http://localhost:3000',
      'http://127.0.0.1:3000/health',
    ]);

    expect(urls).toEqual([
      'http://localhost:3000/ja/e2e/semantic-form',
      'http://127.0.0.1:3000/ja/health',
    ]);
  });

  it('does not pass repository-configured non-local or non-http targets to LHCI', () => {
    const urls = loadLighthouseConfigForUrls([
      'https://example.com/',
      'http://localhost.evil.test:3000/health',
      'http://127.0.0.1.evil.test:3000/health',
      'http://localhost:3001/health',
      'file:///etc/passwd',
    ]);

    expect(urls).toEqual(DEFAULT_LOCAL_URLS);
    expect(urls).not.toContain('https://example.com/');
    expect(urls.every((url) => new URL(url).origin === 'http://localhost:3000')).toBe(true);
  });

  it('keeps approved local targets and drops unapproved targets from mixed policy input', () => {
    const urls = loadLighthouseConfigForUrls([
      'https://example.com/private',
      'http://localhost:3000/ja/health',
      'http://localhost:3000/ja/health#fragment',
    ]);

    expect(urls).toEqual(['http://localhost:3000/ja/health']);
  });
});
