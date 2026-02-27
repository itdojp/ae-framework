import { afterEach, describe, expect, it } from 'vitest';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const generateScript = resolve(repoRoot, 'scripts/change-package/generate.mjs');
const policyPath = resolve(repoRoot, 'policy/risk-policy.yml');
const workdirs: string[] = [];

async function createWorkdir(prefix: string): Promise<string> {
  const workdir = await mkdtemp(join(tmpdir(), prefix));
  workdirs.push(workdir);
  return workdir;
}

afterEach(async () => {
  await Promise.all(workdirs.splice(0).map((workdir) => rm(workdir, { recursive: true, force: true })));
});

describe('change-package generate', () => {
  it('generates change-package json/md from changed files and event payload', async () => {
    const workdir = await createWorkdir('change-package-generate-');
    const changedFilesPath = join(workdir, 'changed-files.txt');
    const eventPath = join(workdir, 'event.json');
    const outputJsonPath = join(workdir, 'artifacts', 'change-package', 'change-package.json');
    const outputMarkdownPath = join(workdir, 'artifacts', 'change-package', 'change-package.md');

    await writeFile(
      changedFilesPath,
      [
        '.github/workflows/pr-ci-status-comment.yml',
        'schema/change-package.schema.json',
      ].join('\n'),
      'utf8',
    );

    await writeFile(
      eventPath,
      `${JSON.stringify({
        repository: { full_name: 'itdojp/ae-framework' },
        pull_request: {
          number: 2289,
          title: 'Introduce Change Package v1',
          base: { ref: 'main' },
          head: { ref: 'feat/2289-change-package-v1' },
          labels: [{ name: 'risk:high' }],
        },
      }, null, 2)}\n`,
      'utf8',
    );

    await mkdir(join(workdir, 'artifacts', 'verify-lite'), { recursive: true });
    await writeFile(
      join(workdir, 'artifacts', 'verify-lite', 'verify-lite-run-summary.json'),
      `${JSON.stringify({ status: 'ok' })}\n`,
      'utf8',
    );

    const result = spawnSync(process.execPath, [
      generateScript,
      '--policy', policyPath,
      '--changed-files-file', changedFilesPath,
      '--event-path', eventPath,
      '--artifact-root', workdir,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--mode', 'detailed',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(0);

    const generated = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      schemaVersion: string;
      source: { repository: string; prNumber: number; baseRef: string; headRef: string };
      scope: { changedFileCount: number; areas: string[] };
      risk: {
        selected: string;
        requiredLabels: string[];
        missingRequiredLabels: string[];
        rationale: {
          highRiskPathMatches: string[];
        };
      };
      evidence: { presentCount: number; missingCount: number };
      exceptions: Array<{ code: string; message: string }>;
    };

    expect(generated.schemaVersion).toBe('change-package/v1');
    expect(generated.source.repository).toBe('itdojp/ae-framework');
    expect(generated.source.prNumber).toBe(2289);
    expect(generated.source.baseRef).toBe('main');
    expect(generated.source.headRef).toBe('feat/2289-change-package-v1');
    expect(generated.scope.changedFileCount).toBe(2);
    expect(generated.scope.areas).toContain('ci');
    expect(generated.scope.areas).toContain('schema');
    expect(generated.risk.selected).toBe('risk:high');
    expect(generated.risk.requiredLabels).toContain('run-ci-extended');
    expect(generated.risk.requiredLabels).toContain('enforce-artifacts');
    expect(generated.risk.missingRequiredLabels).toContain('run-ci-extended');
    expect(generated.risk.rationale.highRiskPathMatches).toContain('.github/workflows/pr-ci-status-comment.yml');
    expect(generated.evidence.presentCount).toBe(1);
    expect(generated.evidence.missingCount).toBeGreaterThan(0);
    expect(generated.exceptions.some((item) => item.code === 'missing-required-labels')).toBe(true);

    const markdown = await readFile(outputMarkdownPath, 'utf8');
    expect(markdown).toContain('## Change Package');
    expect(markdown).toContain('### Evidence');
  });

  it('records conflicting risk labels as exceptions and keeps high-risk true when inferred high', async () => {
    const workdir = await createWorkdir('change-package-generate-risk-conflict-');
    const changedFilesPath = join(workdir, 'changed-files.txt');
    const eventPath = join(workdir, 'event.json');
    const outputJsonPath = join(workdir, 'artifacts', 'change-package', 'change-package.json');
    const outputMarkdownPath = join(workdir, 'artifacts', 'change-package', 'change-package.md');

    await writeFile(
      changedFilesPath,
      ['schema/change-package.schema.json'].join('\n'),
      'utf8',
    );

    await writeFile(
      eventPath,
      `${JSON.stringify({
        repository: { full_name: 'itdojp/ae-framework' },
        pull_request: {
          number: 2290,
          title: 'Risk label conflict sample',
          base: { ref: 'main' },
          head: { ref: 'feat/risk-conflict' },
          labels: [{ name: 'risk:low' }, { name: 'risk:high' }],
        },
      }, null, 2)}\n`,
      'utf8',
    );

    const result = spawnSync(process.execPath, [
      generateScript,
      '--policy', policyPath,
      '--changed-files-file', changedFilesPath,
      '--event-path', eventPath,
      '--artifact-root', workdir,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--mode', 'digest',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(0);

    const generated = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      risk: {
        selected: string;
        inferred: string;
        isHighRisk: boolean;
      };
      exceptions: Array<{ code: string; message: string }>;
    };

    expect(generated.risk.selected).toBe('risk:high');
    expect(generated.risk.inferred).toBe('risk:high');
    expect(generated.risk.isHighRisk).toBe(true);
    expect(generated.exceptions.some((item) => item.code === 'multiple-risk-labels')).toBe(true);

    const markdown = await readFile(outputMarkdownPath, 'utf8');
    expect(markdown).toContain('### Change Package');
  });
});
