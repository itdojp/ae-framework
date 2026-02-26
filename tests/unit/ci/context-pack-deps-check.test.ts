import { afterEach, describe, expect, it } from 'vitest';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const checkDepsScript = resolve(repoRoot, 'scripts/context-pack/check-deps.mjs');
const workdirs: string[] = [];

type DependencyRulesPayload = {
  schemaVersion: string;
  sourceGlobs: string[];
  rules: Array<{
    id: string;
    from: string[];
    to: string[];
    reason: string;
  }>;
  cycleDetection: {
    enabled: boolean;
    scope: string[];
    groupBy: 'src-first-segment';
  };
};

async function writeJson(filePath: string, payload: unknown): Promise<void> {
  await writeFile(filePath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
}

async function setupWorkspace(prefix: string): Promise<string> {
  const workdir = await mkdtemp(join(tmpdir(), prefix));
  workdirs.push(workdir);
  await mkdir(join(workdir, 'src'), { recursive: true });
  await mkdir(join(workdir, 'configs', 'context-pack'), { recursive: true });
  return workdir;
}

async function writeRules(workdir: string, payload: DependencyRulesPayload): Promise<void> {
  await writeJson(join(workdir, 'configs', 'context-pack', 'dependency-rules.json'), payload);
}

function runCheckDeps(workdir: string, args: string[] = []) {
  return spawnSync(process.execPath, [checkDepsScript, ...args], {
    cwd: workdir,
    encoding: 'utf8',
  });
}

afterEach(async () => {
  await Promise.all(
    workdirs.splice(0).map((workdir) => rm(workdir, { recursive: true, force: true })),
  );
});

describe('context-pack dependency boundary check CLI', () => {
  it('passes in strict mode when no boundary violations are found', async () => {
    const workdir = await setupWorkspace('context-pack-deps-pass-');
    await mkdir(join(workdir, 'src', 'core'), { recursive: true });
    await mkdir(join(workdir, 'src', 'shared'), { recursive: true });
    await writeFile(
      join(workdir, 'src', 'core', 'service.ts'),
      "import { sharedValue } from '../shared/util';\nexport const serviceValue = sharedValue;\n",
      'utf8',
    );
    await writeFile(
      join(workdir, 'src', 'shared', 'util.ts'),
      'export const sharedValue = 1;\n',
      'utf8',
    );

    await writeRules(workdir, {
      schemaVersion: 'context-pack-dependency-rules/v1',
      sourceGlobs: ['src/**/*.ts'],
      rules: [
        {
          id: 'core-does-not-depend-on-agents',
          from: ['src/core/**'],
          to: ['src/agents/**'],
          reason: 'Core layer must stay independent from agent orchestration.',
        },
      ],
      cycleDetection: {
        enabled: true,
        scope: ['src/**'],
        groupBy: 'src-first-segment',
      },
    });

    const result = runCheckDeps(workdir, ['--strict=true']);
    expect(result.status).toBe(0);

    const report = JSON.parse(
      await readFile(join(workdir, 'artifacts', 'context-pack', 'deps-summary.json'), 'utf8'),
    ) as {
      status: string;
      metrics: {
        boundaryViolationCount: number;
        cycleCount: number;
      };
    };

    expect(report.status).toBe('pass');
    expect(report.metrics.boundaryViolationCount).toBe(0);
    expect(report.metrics.cycleCount).toBe(0);
  });

  it('returns warn status in report-only mode when boundary rules are violated', async () => {
    const workdir = await setupWorkspace('context-pack-deps-warn-');
    await mkdir(join(workdir, 'src', 'core'), { recursive: true });
    await mkdir(join(workdir, 'src', 'agents'), { recursive: true });
    await writeFile(
      join(workdir, 'src', 'core', 'service.ts'),
      "import { runAgent } from '../agents/runner';\nexport const invoke = runAgent;\n",
      'utf8',
    );
    await writeFile(
      join(workdir, 'src', 'agents', 'runner.ts'),
      'export const runAgent = () => true;\n',
      'utf8',
    );

    await writeRules(workdir, {
      schemaVersion: 'context-pack-dependency-rules/v1',
      sourceGlobs: ['src/**/*.ts'],
      rules: [
        {
          id: 'core-does-not-depend-on-agents',
          from: ['src/core/**'],
          to: ['src/agents/**'],
          reason: 'Core layer must stay independent from agent orchestration.',
        },
      ],
      cycleDetection: {
        enabled: true,
        scope: ['src/**'],
        groupBy: 'src-first-segment',
      },
    });

    const result = runCheckDeps(workdir);
    expect(result.status).toBe(0);

    const report = JSON.parse(
      await readFile(join(workdir, 'artifacts', 'context-pack', 'deps-summary.json'), 'utf8'),
    ) as {
      status: string;
      metrics: {
        boundaryViolationCount: number;
      };
      violations: Array<{
        ruleId: string;
      }>;
    };

    expect(report.status).toBe('warn');
    expect(report.metrics.boundaryViolationCount).toBe(1);
    expect(report.violations[0]?.ruleId).toBe('core-does-not-depend-on-agents');

    const markdown = await readFile(join(workdir, 'artifacts', 'context-pack', 'deps-summary.md'), 'utf8');
    expect(markdown).toContain('Violations (Top 10)');
    expect(markdown).toContain('core-does-not-depend-on-agents');
  });

  it('fails in strict mode when cycle detection finds module cycles', async () => {
    const workdir = await setupWorkspace('context-pack-deps-cycle-');
    await mkdir(join(workdir, 'src', 'core'), { recursive: true });
    await mkdir(join(workdir, 'src', 'orders'), { recursive: true });
    await writeFile(
      join(workdir, 'src', 'core', 'entry.ts'),
      "import { orderValue } from '../orders/entry';\nexport const coreValue = orderValue;\n",
      'utf8',
    );
    await writeFile(
      join(workdir, 'src', 'orders', 'entry.ts'),
      "import { coreValue } from '../core/entry';\nexport const orderValue = coreValue;\n",
      'utf8',
    );

    await writeRules(workdir, {
      schemaVersion: 'context-pack-dependency-rules/v1',
      sourceGlobs: ['src/**/*.ts'],
      rules: [],
      cycleDetection: {
        enabled: true,
        scope: ['src/**'],
        groupBy: 'src-first-segment',
      },
    });

    const result = runCheckDeps(workdir, ['--strict=true']);
    expect(result.status).toBe(2);

    const report = JSON.parse(
      await readFile(join(workdir, 'artifacts', 'context-pack', 'deps-summary.json'), 'utf8'),
    ) as {
      status: string;
      metrics: {
        cycleCount: number;
      };
      violations: Array<{
        type: string;
      }>;
    };

    expect(report.status).toBe('fail');
    expect(report.metrics.cycleCount).toBe(1);
    expect(report.violations.some((violation) => violation.type === 'dependency-cycle')).toBe(true);
  });
});
