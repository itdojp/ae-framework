import { spawnSync } from 'node:child_process';
import { chmodSync, cpSync, existsSync, mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { afterEach, describe, expect, it } from 'vitest';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const REPO_ROOT = path.resolve(__dirname, '..', '..');
const MAIN_NODE_MODULES = path.resolve(REPO_ROOT, '..', 'ae-framework', 'node_modules');
const describePosixOnly = process.platform === 'win32' ? describe.skip : describe;

const tempDirs: string[] = [];

const writeExecutable = (filePath: string, content: string) => {
  writeFileSync(filePath, content, { encoding: 'utf8' });
  chmodSync(filePath, 0o755);
};

const setupWorkspace = () => {
  const workspace = mkdtempSync(path.join(tmpdir(), 'ae-run-verify-lite-'));
  tempDirs.push(workspace);

  mkdirSync(path.join(workspace, 'scripts', 'ci', 'lib'), { recursive: true });
  mkdirSync(path.join(workspace, 'scripts', 'discovery-pack'), { recursive: true });
  mkdirSync(path.join(workspace, 'bin'), { recursive: true });
  mkdirSync(path.join(workspace, 'custom-discovery'), { recursive: true });
  symlinkSync(MAIN_NODE_MODULES, path.join(workspace, 'node_modules'));

  cpSync(path.join(REPO_ROOT, 'scripts', 'ci', 'run-verify-lite-local.sh'), path.join(workspace, 'scripts', 'ci', 'run-verify-lite-local.sh'));
  cpSync(path.join(REPO_ROOT, 'scripts', 'ci', 'write-verify-lite-summary.mjs'), path.join(workspace, 'scripts', 'ci', 'write-verify-lite-summary.mjs'));
  cpSync(path.join(REPO_ROOT, 'scripts', 'ci', 'lib', 'artifact-metadata.mjs'), path.join(workspace, 'scripts', 'ci', 'lib', 'artifact-metadata.mjs'));
  cpSync(path.join(REPO_ROOT, 'scripts', 'discovery-pack', 'lib.mjs'), path.join(workspace, 'scripts', 'discovery-pack', 'lib.mjs'));
  chmodSync(path.join(workspace, 'scripts', 'ci', 'run-verify-lite-local.sh'), 0o755);

  writeFileSync(path.join(workspace, 'custom-discovery', 'sample.yaml'), 'version: 1\nactors: []\n', 'utf8');

  writeExecutable(
    path.join(workspace, 'bin', 'pnpm'),
    `#!/usr/bin/env bash
set -euo pipefail
if [[ "\${*}" == *" conformance report "* ]]; then
  output=""
  markdown=""
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --output)
        output="$2"
        shift 2
        ;;
      --markdown-output)
        markdown="$2"
        shift 2
        ;;
      *)
        shift
        ;;
    esac
  done
  if [[ -n "$output" ]]; then
    mkdir -p "$(dirname "$output")"
    printf '{"status":"success","runsAnalyzed":1,"totals":{"totalViolations":0}}' > "$output"
  fi
  if [[ -n "$markdown" ]]; then
    mkdir -p "$(dirname "$markdown")"
    printf '# conformance\\n' > "$markdown"
  fi
fi
exit 0
`,
  );

  writeExecutable(
    path.join(workspace, 'bin', 'node'),
    `#!/usr/bin/env bash
set -euo pipefail
REAL_NODE=${JSON.stringify(process.execPath)}
case "\${1:-}" in
  --input-type=module)
    exec "$REAL_NODE" "$@"
    ;;
  scripts/ci/write-verify-lite-summary.mjs)
    exec "$REAL_NODE" "$@"
    ;;
  scripts/discovery-pack/validate.mjs)
    mkdir -p artifacts/discovery-pack
    cat > artifacts/discovery-pack/discovery-pack-validate-report.json <<'JSON'
{"status":"warn","scannedFiles":1,"warningFiles":0,"failedFiles":0,"summary":{"blockingOpenQuestions":0,"orphanApprovedRequirements":0,"orphanApprovedBusinessUseCases":0}}
JSON
    printf '# validate\\n' > artifacts/discovery-pack/discovery-pack-validate-report.md
    exit "\${VERIFY_TEST_VALIDATE_EXIT:-0}"
    ;;
  scripts/discovery-pack/compile.mjs)
    mkdir -p artifacts/discovery-pack
    printf '' > artifacts/discovery-pack/compile-invoked.marker
    cat > artifacts/discovery-pack/discovery-pack-compile-report.json <<'JSON'
{"status":"success","summary":{"selectedCount":1,"excludedByStatusCount":0,"skippedByTargetCount":0}}
JSON
    printf '# compile\\n' > artifacts/discovery-pack/discovery-pack-compile-report.md
    exit "\${VERIFY_TEST_COMPILE_EXIT:-0}"
    ;;
  dist/src/cli/index.js|scripts/ci/validate-reason-codes.mjs|scripts/context-pack/validate.mjs|scripts/context-pack/verify-functor.mjs|scripts/context-pack/verify-natural-transformation.mjs|scripts/context-pack/verify-product-coproduct.mjs|scripts/context-pack/verify-phase5-templates.mjs|scripts/bdd/lint.mjs|scripts/mutation/mutation-report.mjs|scripts/mutation/list-survivors.mjs)
    exit 0
    ;;
  *)
    exec "$REAL_NODE" "$@"
    ;;
esac
`,
  );

  return workspace;
};

const runVerifyLite = (workspace: string, envOverrides: Record<string, string> = {}) =>
  spawnSync('bash', ['scripts/ci/run-verify-lite-local.sh'], {
    cwd: workspace,
    encoding: 'utf8',
    env: {
      ...process.env,
      PATH: `${path.join(workspace, 'bin')}:${process.env.PATH ?? ''}`,
      VERIFY_LITE_DISCOVERY_SOURCES: 'custom-discovery/*.yaml',
      ...envOverrides,
    },
  });

afterEach(() => {
  while (tempDirs.length > 0) {
    const dir = tempDirs.pop();
    if (dir) {
      rmSync(dir, { recursive: true, force: true });
    }
  }
});

describePosixOnly('scripts/ci/run-verify-lite-local.sh discovery-pack rollout', () => {
  it('writes summary before exiting on strict discovery validation failure', () => {
    const workspace = setupWorkspace();

    const result = runVerifyLite(workspace, {
      VERIFY_LITE_DISCOVERY_MODE: 'strict',
      VERIFY_TEST_VALIDATE_EXIT: '23',
    });

    const summaryPath = path.join(workspace, 'artifacts', 'verify-lite', 'verify-lite-run-summary.json');
    const summary = JSON.parse(readFileSync(summaryPath, 'utf8'));

    expect(result.status).toBe(23);
    expect(summary.steps.discoveryPackValidation.status).toBe('failure');
    expect(summary.steps.discoveryPackCompile.status).toBe('skipped');
    expect(summary.discoveryPack.sourcePresent).toBe(true);
    expect(summary.steps.discoveryPackCompile.notes).toContain('skipped-after-validation-failure');
    expect(existsSync(path.join(workspace, 'artifacts', 'discovery-pack', 'compile-invoked.marker'))).toBe(false);
  });

  it('records validator process failures as failure in report-only mode and respects configured sources', () => {
    const workspace = setupWorkspace();

    const result = runVerifyLite(workspace, {
      VERIFY_LITE_DISCOVERY_MODE: 'report-only',
      VERIFY_TEST_VALIDATE_EXIT: '31',
    });

    const summaryPath = path.join(workspace, 'artifacts', 'verify-lite', 'verify-lite-run-summary.json');
    const summary = JSON.parse(readFileSync(summaryPath, 'utf8'));

    expect(result.status).toBe(0);
    expect(summary.discoveryPack.sourcePresent).toBe(true);
    expect(summary.discoveryPack.reason).not.toBe('source-not-found');
    expect(summary.steps.discoveryPackValidation.status).toBe('failure');
    expect(summary.steps.discoveryPackCompile.status).toBe('skipped');
    expect(summary.traceability).toEqual({
      status: 'skipped',
      missingCount: 0,
      matrixPath: null,
      notes: 'matrix_not_found',
    });
  });
});
