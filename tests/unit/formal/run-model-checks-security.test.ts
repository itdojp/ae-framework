import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { delimiter, dirname, join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { validateModelCheckReportContract } from '../../../scripts/verify/enforce-model-check-report.mjs';

const scriptPath = resolve('scripts/verify/run-model-checks.mjs');
const tmpRoot = resolve('.codex-local/tmp');
const reportSchema = JSON.parse(readFileSync(resolve('schema/model-check-execution-v1.schema.json'), 'utf8'));
const executionEvidenceSchema = JSON.parse(readFileSync(resolve('schema/formal-execution-evidence-v1.schema.json'), 'utf8'));
const ajv = new Ajv2020({ allErrors: true, strict: false });
addFormats(ajv);
ajv.addSchema(executionEvidenceSchema);
const validateReport = ajv.compile(reportSchema);
const expectValidReport = (summary: unknown) => {
  expect(validateReport(summary), JSON.stringify(validateReport.errors)).toBe(true);
  expect(validateModelCheckReportContract(summary)).toEqual([]);
};

const makeRepo = () => {
  mkdirSync(tmpRoot, { recursive: true });
  const dir = mkdtempSync(join(tmpRoot, 'run-model-checks-security-'));
  mkdirSync(join(dir, 'spec', 'formal'), { recursive: true });
  writeFileSync(join(dir, 'spec', 'formal', 'safe;name.als'), 'sig A {}\n', 'utf8');
  return dir;
};

const makeFakeJava = (dir: string, exitCode = 0) => {
  const bin = join(dir, 'bin');
  mkdirSync(bin, { recursive: true });
  const log = join(dir, 'java-argv.json');
  const java = join(bin, 'java');
  const javaHelper = join(bin, 'java-helper.cjs');
  writeFileSync(
    javaHelper,
    `const fs = require('node:fs');\nconst args=process.argv.slice(2);\nfs.writeFileSync(${JSON.stringify(log)}, JSON.stringify(args));\nconsole.log(args.at(-1)==='version' ? 'Alloy 6.2.0' : 'fake alloy result');\nprocess.exit(${exitCode});\n`,
    { mode: 0o755 },
  );
  writeFileSync(java, `#!/bin/sh\nexec "${process.execPath}" "${javaHelper}" "$@"\n`, { mode: 0o755 });
  writeFileSync(join(bin, 'java.cmd'), `@echo off\r\n"${process.execPath}" "${javaHelper}" %*\r\n`, {
    mode: 0o755,
  });
  return { bin, log };
};

describe('run-model-checks Alloy execution security', () => {
  it('keeps the integration example on the truthful execution-report contract', () => {
    const example = JSON.parse(readFileSync(resolve('docs/integrations/examples/model-check.example.json'), 'utf8'));
    expectValidReport(example);
    expect(example).toMatchObject({ status: 'not-run', ok: null });
  });

  it('ignores ALLOY_RUN_CMD shell templates and passes Alloy file paths as argv', () => {
    const dir = makeRepo();
    try {
      const marker = join(dir, 'shell-marker');
      const alloyJar = join(dir, '.cache', 'tools', 'alloy.jar');
      mkdirSync(dirname(alloyJar), { recursive: true });
      writeFileSync(alloyJar, 'fake jar', 'utf8');
      const fakeJava = makeFakeJava(dir);

      const result = spawnSync(process.execPath, [scriptPath], {
        cwd: dir,
        encoding: 'utf8',
        env: {
          ...process.env,
          ALLOY_JAR: alloyJar,
          ALLOY_RUN_CMD: `node -e "require('fs').writeFileSync('${marker}', 'executed')"`,
          ALLOY_CMD_JSON: '["exec","-q","-o","-","-f","{file}"]',
          PATH: [fakeJava.bin, process.env.PATH ?? ''].filter(Boolean).join(delimiter),
        },
      });

      expect(result.status).toBe(0);
      expect(existsSync(marker)).toBe(false);
      expect(result.stderr + result.stdout).toContain('ALLOY_RUN_CMD shell templates are ignored');
      const argv = JSON.parse(readFileSync(fakeJava.log, 'utf8')) as string[];
      expect(argv.slice(0, 6)).toEqual(['-jar', alloyJar, 'exec', '-q', '-o', '-']);
      expect(argv[6]).toBe('-f');
      expect(argv[7]).toBe(join(dir, 'spec', 'formal', 'safe;name.als'));

      const summary = JSON.parse(readFileSync(join(dir, 'artifacts', 'codex', 'model-check.json'), 'utf8'));
      expectValidReport(summary);
      expect(validateModelCheckReportContract(summary, {
        artifactRoot: join(dir, 'artifacts', 'codex'),
      })).toEqual([]);
      expect(summary).toMatchObject({
        schemaVersion: 'model-check-report/v1',
        artifactStatus: 'execution-report',
        status: 'executed',
        ok: true,
        detectedInputs: 1,
        executedInputs: 1,
        skippedInputs: 0,
      });
      expect(summary.alloy.results[0]).toMatchObject({
        ok: true,
        executionStatus: 'executed',
        evidence: {
          schemaVersion: 'formal-runner-result/v1',
          artifactStatus: 'execution-report',
          producer: { id: 'ae.formal.run-model-checks' },
          executionOccurred: true,
          verificationKind: 'model-check',
          tool: {
            name: 'Alloy',
            version: '6.2.0',
            versionStatus: 'verified',
            versionSource: 'cli',
            artifactSha256: expect.stringMatching(/^[a-f0-9]{64}$/),
          },
          input: ['spec/formal/safe;name.als'],
          result: { status: 'ok', code: 0 },
          scope: expect.stringContaining('safe;name'),
          assumptions: expect.arrayContaining([
            expect.stringContaining('supplied Alloy model'),
          ]),
        },
      });
      expect(existsSync(join(dir, 'artifacts', 'codex', 'safe;name.alloy.log.txt'))).toBe(true);
      expect(readdirSync(join(dir, 'artifacts', 'codex')).some((name) => name.endsWith('.tmp'))).toBe(false);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('writes an explicit not-run report instead of success when no checker input executes', () => {
    mkdirSync(tmpRoot, { recursive: true });
    const dir = mkdtempSync(join(tmpRoot, 'run-model-checks-not-run-'));
    try {
      const result = spawnSync(process.execPath, [scriptPath], {
        cwd: dir,
        encoding: 'utf8',
        env: process.env,
      });

      expect(result.status).toBe(0);
      const summary = JSON.parse(readFileSync(join(dir, 'artifacts', 'codex', 'model-check.json'), 'utf8'));
      expectValidReport(summary);
      expect(summary).toMatchObject({
        schemaVersion: 'model-check-report/v1',
        artifactStatus: 'execution-report',
        status: 'not-run',
        ok: null,
        detectedInputs: 0,
        executedInputs: 0,
        skippedInputs: 0,
        tlc: { results: [], errors: [] },
        alloy: { results: [], errors: [] },
      });
      expect(summary.tlc.skipped).toEqual([]);
      expect(summary.alloy.skipped).toEqual([]);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('records a completed Alloy checker failure as executed/fail rather than tool-error', () => {
    const dir = makeRepo();
    try {
      const alloyJar = join(dir, '.cache', 'tools', 'alloy.jar');
      mkdirSync(dirname(alloyJar), { recursive: true });
      writeFileSync(alloyJar, 'fake jar', 'utf8');
      const fakeJava = makeFakeJava(dir, 2);

      const result = spawnSync(process.execPath, [scriptPath], {
        cwd: dir,
        encoding: 'utf8',
        env: {
          ...process.env,
          ALLOY_JAR: alloyJar,
          ALLOY_CMD_JSON: '["exec","-f","{file}"]',
          PATH: [fakeJava.bin, process.env.PATH ?? ''].filter(Boolean).join(delimiter),
        },
      });

      expect(result.status).toBe(0);
      const summary = JSON.parse(readFileSync(join(dir, 'artifacts', 'codex', 'model-check.json'), 'utf8'));
      expectValidReport(summary);
      expect(summary).toMatchObject({ status: 'failed', ok: false });
      expect(summary.alloy.results[0]).toMatchObject({
        ok: false,
        code: 2,
        executionStatus: 'executed',
        evidence: { result: { status: 'failed', code: 2 } },
      });
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('records tool-error when Java cannot be started instead of reporting model-check success', () => {
    mkdirSync(tmpRoot, { recursive: true });
    const dir = mkdtempSync(join(tmpRoot, 'run-model-checks-tool-error-'));
    try {
      const specDir = join(dir, 'spec', 'formal');
      mkdirSync(specDir, { recursive: true });
      writeFileSync(join(specDir, 'Safe.tla'), '---- MODULE Safe ----\n====\n', 'utf8');
      writeFileSync(join(specDir, 'Safe.cfg'), 'SPECIFICATION Spec\n', 'utf8');
      const tlaJar = join(dir, '.cache', 'tools', 'tla2tools.jar');
      mkdirSync(dirname(tlaJar), { recursive: true });
      writeFileSync(tlaJar, 'fake jar', 'utf8');

      const result = spawnSync(process.execPath, [scriptPath], {
        cwd: dir,
        encoding: 'utf8',
        timeout: 30_000,
        env: { ...process.env, PATH: '' },
      });

      expect(result.status).toBe(0);
      const summary = JSON.parse(readFileSync(join(dir, 'artifacts', 'codex', 'model-check.json'), 'utf8'));
      expectValidReport(summary);
      expect(summary).toMatchObject({ status: 'tool-error', ok: null });
      expect(summary.tlc.results[0]).toMatchObject({
        ok: false,
        executionStatus: 'tool-error',
        evidence: {
          result: {
            status: 'tool-error',
            code: null,
          },
        },
      });
      expect(summary.tlc.results[0].error).toContain('spawn java');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('emits a tool-error report when the checker artifact cannot be downloaded', () => {
    mkdirSync(tmpRoot, { recursive: true });
    const dir = mkdtempSync(join(tmpRoot, 'run-model-checks-download-error-'));
    try {
      const specDir = join(dir, 'spec', 'formal');
      const emptyBin = join(dir, 'empty-bin');
      mkdirSync(specDir, { recursive: true });
      mkdirSync(emptyBin, { recursive: true });
      writeFileSync(join(specDir, 'Safe.tla'), '---- MODULE Safe ----\n====\n', 'utf8');
      writeFileSync(join(specDir, 'Safe.cfg'), 'SPECIFICATION Spec\n', 'utf8');

      const result = spawnSync(process.execPath, [scriptPath], {
        cwd: dir,
        encoding: 'utf8',
        timeout: 30_000,
        env: { ...process.env, PATH: emptyBin, TLA_TOOLS_URL: 'https://invalid.example/tla2tools.jar' },
      });

      expect(result.status).toBe(0);
      const summary = JSON.parse(readFileSync(join(dir, 'artifacts', 'codex', 'model-check.json'), 'utf8'));
      expectValidReport(summary);
      expect(summary).toMatchObject({ status: 'tool-error', ok: null });
      expect(summary.tlc.results).toEqual([]);
      expect(summary.tlc.errors[0]).toMatchObject({
        file: '.cache/tools/tla2tools.jar',
        error: expect.stringContaining('spawn curl'),
      });
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});
