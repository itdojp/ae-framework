import { spawnSync } from 'node:child_process';
import {
  chmodSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { afterEach, beforeAll, describe, expect, it } from 'vitest';
import {
  isSpinSemanticSuccess,
  parseSpinSemanticResult,
} from '../../../scripts/formal/verify-spin.mjs';

const repoRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../../..');
const scriptPath = join(repoRoot, 'scripts/formal/verify-spin.mjs');
const localTmpRoot = join(repoRoot, '.codex-local/tmp');
const sandboxes: string[] = [];
const panOptions = ['-a', '-m10000', '-N', 'p_done'];

const completedPanOutput = `(Spin Version 6.5.2 -- 6 December 2019)
Full statespace search for:
    never claim          + (p_done)
    assertion violations +
    acceptance cycles    +
State-vector 44 byte, depth reached 17, errors: 0
`;

const counterexamplePanOutput = `pan:1: acceptance cycle (at depth 8)
pan: wrote model.pml.trail
Warning: Search not completed
Full statespace search for:
    never claim          + (p_done)
State-vector 44 byte, depth reached 8, errors: 1
`;

interface SpinSummary {
  ran: boolean;
  status: string;
  ok: boolean | null;
  exitCode: number | null;
  semanticResult: Record<string, unknown>;
  runnerResult: {
    artifactStatus: string;
    executionEvidence: {
      artifactStatus: string;
      executionOccurred: boolean;
      result: { status: string; code: number | null; logPath: string | null };
      semanticResult: Record<string, unknown>;
    };
  };
}

function createSandbox() {
  const sandbox = mkdtempSync(join(localTmpRoot, 'verify-spin-'));
  sandboxes.push(sandbox);
  const binDir = join(sandbox, 'bin');
  mkdirSync(binDir, { recursive: true });
  writeFileSync(join(sandbox, 'model.pml'), 'ltl p_done { <> true }\n', 'utf8');

  const fakeSpin = join(binDir, 'spin');
  writeFileSync(fakeSpin, `#!/bin/sh
if [ "$#" -eq 0 ]; then
  exit 0
fi
if [ "\${1:-}" = "-V" ]; then
  printf '%s\\n' 'Spin Version 6.5.2'
  exit 0
fi
if [ "\${1:-}" = "-a" ]; then
  printf '%s\\n' "$*" > "\${FAKE_SPIN_TRACE_FILE}"
  : > pan.c
  exit 0
fi
exit 2
`, 'utf8');
  chmodSync(fakeSpin, 0o755);

  const fakeGcc = join(binDir, 'gcc');
  writeFileSync(fakeGcc, `#!/bin/sh
if [ "$#" -eq 0 ]; then
  exit 0
fi
cat > pan <<'PAN'
#!/bin/sh
printf '%s\\n' "$*" > "\${FAKE_PAN_TRACE_FILE}"
printf '%b' "\${FAKE_PAN_OUTPUT-}"
if [ "\${FAKE_PAN_TRAIL:-0}" = "1" ]; then
  : > model.pml.trail
fi
exit "\${FAKE_PAN_EXIT_CODE:-0}"
PAN
chmod +x pan
exit 0
`, 'utf8');
  chmodSync(fakeGcc, 0o755);
  return { sandbox, binDir };
}

function runFakeSpin({
  output = completedPanOutput,
  exitCode = 0,
  trail = false,
  timeout = false,
  ltl = 'p_done',
  maxDepth = 10000,
}: {
  output?: string;
  exitCode?: number;
  trail?: boolean;
  timeout?: boolean;
  ltl?: string | null;
  maxDepth?: number;
} = {}) {
  const { sandbox, binDir } = createSandbox();
  const spinTrace = join(sandbox, 'spin-args.txt');
  const panTrace = join(sandbox, 'pan-args.txt');
  const cliArgs = [scriptPath, '--file', 'model.pml', '--max-depth', String(maxDepth)];
  if (ltl) cliArgs.push('--ltl', ltl);
  if (timeout) cliArgs.push('--timeout', '1000');
  const result = spawnSync(process.execPath, cliArgs, {
    cwd: sandbox,
    encoding: 'utf8',
    env: {
      ...process.env,
      PATH: `${binDir}:${process.env.PATH ?? ''}`,
      FAKE_SPIN_TRACE_FILE: spinTrace,
      FAKE_PAN_TRACE_FILE: panTrace,
      FAKE_PAN_OUTPUT: output,
      FAKE_PAN_EXIT_CODE: String(exitCode),
      FAKE_PAN_TRAIL: trail ? '1' : '0',
    },
  });
  const summaryPath = join(sandbox, 'artifacts/hermetic-reports/formal/spin-summary.json');
  const summary = JSON.parse(readFileSync(summaryPath, 'utf8')) as SpinSummary;
  return {
    result,
    summary,
    spinArgs: readFileSync(spinTrace, 'utf8').trim(),
    panArgs: readFileSync(panTrace, 'utf8').trim(),
  };
}

beforeAll(() => {
  mkdirSync(localTmpRoot, { recursive: true });
});

afterEach(() => {
  while (sandboxes.length > 0) {
    rmSync(sandboxes.pop()!, { recursive: true, force: true });
  }
});

describe('parseSpinSemanticResult', () => {
  it('parses a completed, error-free Pan search and binds property and depth options', () => {
    const semanticResult = parseSpinSemanticResult({
      output: completedPanOutput,
      requestedProperty: 'p_done',
      requestedMaxDepth: 10000,
      options: panOptions,
    });
    expect(semanticResult).toEqual({
      domain: 'spin',
      parsed: true,
      errors: 0,
      trailPresent: false,
      counterexamplePresent: false,
      searchCompleted: true,
      requestedProperty: 'p_done',
      selectedProperty: 'p_done',
      requestedMaxDepth: 10000,
      depthReached: 17,
      options: panOptions,
      propertyMatched: true,
      boundsMatched: true,
      timeout: false,
    });
    expect(isSpinSemanticSuccess(semanticResult)).toBe(true);
  });

  it('records Pan errors, a trail, and an acceptance-cycle counterexample', () => {
    const semanticResult = parseSpinSemanticResult({
      output: counterexamplePanOutput,
      requestedProperty: 'p_done',
      requestedMaxDepth: 10000,
      options: panOptions,
      trailPresent: true,
    });
    expect(semanticResult).toMatchObject({
      parsed: true,
      errors: 1,
      trailPresent: true,
      counterexamplePresent: true,
      searchCompleted: false,
      propertyMatched: true,
      boundsMatched: true,
    });
    expect(isSpinSemanticSuccess(semanticResult)).toBe(false);
  });

  it('does not call a depth-truncated zero-error run a completed search', () => {
    const semanticResult = parseSpinSemanticResult({
      output: `error: max search depth too small
Warning: Search not completed
Full statespace search for:
    never claim + (p_done)
State-vector 44 byte, depth reached 10000, errors: 0
`,
      requestedProperty: 'p_done',
      requestedMaxDepth: 10000,
      options: panOptions,
    });
    expect(semanticResult).toMatchObject({
      parsed: true,
      errors: 0,
      searchCompleted: false,
      depthReached: 10000,
      boundsMatched: true,
    });
    expect(isSpinSemanticSuccess(semanticResult)).toBe(false);
  });

  it('detects a requested/selected LTL property mismatch', () => {
    const semanticResult = parseSpinSemanticResult({
      output: completedPanOutput.replaceAll('p_done', 'p_other'),
      requestedProperty: 'p_done',
      requestedMaxDepth: 10000,
      options: panOptions,
    });
    expect(semanticResult).toMatchObject({
      selectedProperty: 'p_other',
      propertyMatched: false,
      searchCompleted: true,
    });
    expect(isSpinSemanticSuccess(semanticResult)).toBe(false);
  });

  it('detects a depth option mismatch and an observed depth beyond the requested bound', () => {
    const semanticResult = parseSpinSemanticResult({
      output: completedPanOutput.replace('depth reached 17', 'depth reached 10001'),
      requestedProperty: 'p_done',
      requestedMaxDepth: 10000,
      options: ['-a', '-m9999', '-N', 'p_done'],
    });
    expect(semanticResult).toMatchObject({
      requestedMaxDepth: 10000,
      depthReached: 10001,
      boundsMatched: false,
    });
    expect(isSpinSemanticSuccess(semanticResult)).toBe(false);
  });

  it('records timeout independently and rejects otherwise parseable output', () => {
    const semanticResult = parseSpinSemanticResult({
      output: completedPanOutput,
      requestedProperty: 'p_done',
      requestedMaxDepth: 10000,
      options: panOptions,
      timeout: true,
    });
    expect(semanticResult).toMatchObject({ parsed: true, searchCompleted: false, timeout: true });
    expect(isSpinSemanticSuccess(semanticResult)).toBe(false);
  });
});

describe('verify-spin semantic evidence', () => {
  it('records completed semantics identically and selects LTL on the Pan command line', () => {
    const { result, summary, spinArgs, panArgs: actualPanArgs } = runFakeSpin();
    expect(result.status).toBe(0);
    expect(summary).toMatchObject({ ran: true, status: 'ran', ok: true, exitCode: 0 });
    expect(summary.runnerResult.executionEvidence.result.status).toBe('ok');
    expect(summary.runnerResult.executionEvidence.semanticResult).toEqual(summary.semanticResult);
    expect(spinArgs).toMatch(/^-a .*model\.pml$/u);
    expect(spinArgs.split(/\s+/u)).not.toContain('-N');
    expect(actualPanArgs).toBe('-a -m10000 -N p_done');
  });

  it('classifies a counterexample as failed execution evidence, not a tool error', () => {
    const { result, summary } = runFakeSpin({ output: counterexamplePanOutput, trail: true });
    expect(result.status).toBe(0);
    expect(summary).toMatchObject({ ran: true, status: 'ran', ok: false, exitCode: 0 });
    expect(summary.semanticResult).toMatchObject({ errors: 1, counterexamplePresent: true, trailPresent: true });
    expect(summary.runnerResult.executionEvidence).toMatchObject({
      artifactStatus: 'execution-report',
      executionOccurred: true,
      result: { status: 'failed', code: 0 },
    });
    expect(summary.runnerResult.executionEvidence.result.status).not.toBe('tool-error');
  });

  it('does not pass on exit code zero when the Pan summary is not parseable', () => {
    const { result, summary } = runFakeSpin({ output: '' });
    expect(result.status).toBe(0);
    expect(summary).toMatchObject({ ran: true, status: 'ran', ok: false, exitCode: 0 });
    expect(summary.semanticResult).toMatchObject({
      parsed: false,
      errors: null,
      searchCompleted: false,
      depthReached: null,
    });
    expect(summary.runnerResult.executionEvidence.result.status).toBe('failed');
  });

  it('distinguishes Pan timeout evidence from generic failure', () => {
    const { result, summary } = runFakeSpin({ output: '', exitCode: 124, timeout: true });
    expect(result.status).toBe(0);
    expect(summary).toMatchObject({ ran: true, status: 'timeout', ok: null, exitCode: 124 });
    expect(summary.semanticResult).toMatchObject({ parsed: false, timeout: true, searchCompleted: false });
    expect(summary.runnerResult.executionEvidence.result.status).toBe('timeout');
  });

  it('keeps a generic nonzero Pan result as failed execution evidence', () => {
    const { result, summary } = runFakeSpin({ output: completedPanOutput, exitCode: 3 });
    expect(result.status).toBe(0);
    expect(summary).toMatchObject({ ran: true, status: 'failed', ok: false, exitCode: 3 });
    expect(summary.runnerResult.executionEvidence.result.status).toBe('failed');
  });
});
