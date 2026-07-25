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
  isSmtSemanticSuccess,
  parseSmtSemanticResult,
} from '../../../scripts/formal/verify-smt.mjs';

const repoRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../../..');
const scriptPath = join(repoRoot, 'scripts/formal/verify-smt.mjs');
const localTmpRoot = join(repoRoot, '.codex-local/tmp');
const sandboxes: string[] = [];

interface SmtSummary {
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
      result: { status: string; code: number | null };
      semanticResult: Record<string, unknown>;
    };
  };
}

function createSandbox() {
  const sandbox = mkdtempSync(join(localTmpRoot, 'verify-smt-'));
  sandboxes.push(sandbox);
  const binDir = join(sandbox, 'bin');
  mkdirSync(binDir, { recursive: true });
  writeFileSync(join(sandbox, 'input.smt2'), '(check-sat)\n', 'utf8');

  const fakeZ3 = join(binDir, 'z3');
  writeFileSync(fakeZ3, `#!/bin/sh
if [ "\${1:-}" = "--version" ]; then
  printf '%s\\n' 'Z3 version 4.12.2'
  exit 0
fi
if [ "$#" -eq 0 ]; then
  exit 0
fi
printf '%b' "\${FAKE_SMT_STDOUT-sat\\n}"
printf '%b' "\${FAKE_SMT_STDERR:-}" >&2
exit "\${FAKE_SMT_EXIT_CODE:-0}"
`, 'utf8');
  chmodSync(fakeZ3, 0o755);
  return { sandbox, binDir };
}

function runFakeSmt({
  expectedResult,
  stdout = 'sat\n',
  stderr = '',
  exitCode = 0,
  timeout = false,
}: {
  expectedResult?: 'sat' | 'unsat';
  stdout?: string;
  stderr?: string;
  exitCode?: number;
  timeout?: boolean;
}) {
  const { sandbox, binDir } = createSandbox();
  const cliArgs = [scriptPath, '--solver=z3', '--file', 'input.smt2'];
  if (expectedResult) cliArgs.push('--expected-result', expectedResult);
  if (timeout) cliArgs.push('--timeout', '1000');
  const result = spawnSync(process.execPath, cliArgs, {
    cwd: sandbox,
    encoding: 'utf8',
    env: {
      ...process.env,
      PATH: `${binDir}:${process.env.PATH ?? ''}`,
      FAKE_SMT_STDOUT: stdout,
      FAKE_SMT_STDERR: stderr,
      FAKE_SMT_EXIT_CODE: String(exitCode),
    },
  });
  const summaryPath = join(sandbox, 'artifacts/hermetic-reports/formal/smt-summary.json');
  const summary = JSON.parse(readFileSync(summaryPath, 'utf8')) as SmtSummary;
  return { result, summary };
}

beforeAll(() => {
  mkdirSync(localTmpRoot, { recursive: true });
});

afterEach(() => {
  while (sandboxes.length > 0) {
    rmSync(sandboxes.pop()!, { recursive: true, force: true });
  }
});

describe('parseSmtSemanticResult', () => {
  it.each([
    ['sat', 'sat'],
    ['unsat', 'unsat'],
  ] as const)('accepts exactly one %s result matching the expectation', (stdout, expectedResult) => {
    const semanticResult = parseSmtSemanticResult({ stdout, expectedResult });
    expect(semanticResult).toEqual({
      domain: 'smt',
      parsed: true,
      expectedResult,
      actualResult: stdout,
      matchesExpected: true,
      timeout: false,
    });
    expect(isSmtSemanticSuccess(semanticResult)).toBe(true);
  });

  it('recognizes unknown but never treats it as semantic success', () => {
    const semanticResult = parseSmtSemanticResult({ stdout: 'unknown\n', expectedResult: 'sat' });
    expect(semanticResult).toMatchObject({
      parsed: true,
      actualResult: 'unknown',
      matchesExpected: false,
    });
    expect(isSmtSemanticSuccess(semanticResult)).toBe(false);
  });

  it('marks multiple solver result tokens as malformed instead of choosing one', () => {
    const semanticResult = parseSmtSemanticResult({
      stdout: 'sat\n(model)\nunsat\n',
      expectedResult: 'sat',
    });
    expect(semanticResult).toMatchObject({
      parsed: false,
      actualResult: 'malformed',
      matchesExpected: false,
    });
  });

  it('rejects an inline result-like token that is not a complete solver result line', () => {
    const semanticResult = parseSmtSemanticResult({
      stdout: 'solver warning: sat\n',
      expectedResult: 'sat',
    });
    expect(semanticResult).toMatchObject({
      parsed: false,
      actualResult: 'malformed',
      matchesExpected: false,
    });
  });

  it('accepts one exact result line while retaining additional model output in the log', () => {
    const semanticResult = parseSmtSemanticResult({
      stdout: 'sat\n(\n  (define-fun x () Int 1)\n)\n',
      expectedResult: 'sat',
    });
    expect(semanticResult).toMatchObject({
      parsed: true,
      actualResult: 'sat',
      matchesExpected: true,
    });
  });

  it('rejects a parsed result that mismatches the expected result', () => {
    const semanticResult = parseSmtSemanticResult({ stdout: 'unsat\n', expectedResult: 'sat' });
    expect(semanticResult).toMatchObject({
      parsed: true,
      expectedResult: 'sat',
      actualResult: 'unsat',
      matchesExpected: false,
    });
  });

  it('preserves a parsed execution with no expectation as ineligible', () => {
    const semanticResult = parseSmtSemanticResult({ stdout: 'sat\n' });
    expect(semanticResult).toMatchObject({
      parsed: true,
      expectedResult: null,
      actualResult: 'sat',
      matchesExpected: null,
    });
    expect(isSmtSemanticSuccess(semanticResult)).toBe(false);
  });

  it('does not infer a result from arbitrary stdout and records timeout independently', () => {
    expect(parseSmtSemanticResult({
      stdout: 'solver completed without a result token',
      expectedResult: 'sat',
      timeout: true,
    })).toMatchObject({
      parsed: false,
      actualResult: 'malformed',
      matchesExpected: false,
      timeout: true,
    });
  });
});

describe('verify-smt semantic evidence', () => {
  it('records a matching result identically in the summary and execution evidence', () => {
    const { result, summary } = runFakeSmt({ expectedResult: 'sat' });
    expect(result.status).toBe(0);
    expect(summary).toMatchObject({ ran: true, status: 'ran', ok: true, exitCode: 0 });
    expect(summary.semanticResult).toMatchObject({ actualResult: 'sat', matchesExpected: true });
    expect(summary.runnerResult.executionEvidence).toMatchObject({
      executionOccurred: true,
      result: { status: 'ok', code: 0 },
    });
    expect(summary.runnerResult.executionEvidence.semanticResult).toEqual(summary.semanticResult);
  });

  it('keeps a matching token from a nonzero solver run as failed execution evidence', () => {
    const { result, summary } = runFakeSmt({ expectedResult: 'sat', exitCode: 7 });
    expect(result.status).toBe(0);
    expect(summary).toMatchObject({ ran: true, status: 'failed', ok: false, exitCode: 7 });
    expect(summary.semanticResult).toMatchObject({ actualResult: 'sat', matchesExpected: true, timeout: false });
    expect(summary.runnerResult.executionEvidence.result).toEqual({
      status: 'failed',
      code: 7,
      logPath: 'artifacts/hermetic-reports/formal/smt-output.txt',
    });
  });

  it('distinguishes a timeout from a generic nonzero solver exit', () => {
    const { result, summary } = runFakeSmt({ expectedResult: 'sat', stdout: '', exitCode: 124, timeout: true });
    expect(result.status).toBe(0);
    expect(summary).toMatchObject({ ran: true, status: 'timeout', ok: null, exitCode: 124 });
    expect(summary.semanticResult).toMatchObject({ actualResult: null, matchesExpected: false, timeout: true });
    expect(summary.runnerResult.executionEvidence.result.status).toBe('timeout');
  });

  it('keeps a missing expectation as an execution report but does not mark it ok', () => {
    const { result, summary } = runFakeSmt({});
    expect(result.status).toBe(0);
    expect(summary).toMatchObject({ ran: true, status: 'ran', ok: false, exitCode: 0 });
    expect(summary.semanticResult).toMatchObject({ expectedResult: null, actualResult: 'sat', matchesExpected: null });
    expect(summary.runnerResult).toMatchObject({ artifactStatus: 'execution-report' });
    expect(summary.runnerResult.executionEvidence).toMatchObject({
      artifactStatus: 'execution-report',
      executionOccurred: true,
      result: { status: 'failed', code: 0 },
    });
  });

  it('fails closed on exit zero when the semantic result mismatches its expectation', () => {
    const { result, summary } = runFakeSmt({ expectedResult: 'unsat', stdout: 'sat\n' });
    expect(result.status).toBe(0);
    expect(summary).toMatchObject({ ran: true, status: 'ran', ok: false, exitCode: 0 });
    expect(summary.semanticResult).toMatchObject({
      expectedResult: 'unsat',
      actualResult: 'sat',
      matchesExpected: false,
    });
    expect(summary.runnerResult.executionEvidence.result).toMatchObject({ status: 'failed', code: 0 });
  });

  it('binds the sample workflow to the expected sat result', () => {
    const workflow = readFileSync(join(repoRoot, '.github/workflows/formal-verify.yml'), 'utf8');
    expect(workflow).toContain('verify-smt.mjs --solver="$SMT_SOLVER" --file spec/smt/sample.smt2 --expected-result sat');
    const packageJson = JSON.parse(readFileSync(join(repoRoot, 'package.json'), 'utf8'));
    expect(packageJson.scripts['verify:formal']).toContain(
      'verify-smt.mjs --solver=z3 --file spec/smt/sample.smt2 --expected-result=sat',
    );
  });
});
