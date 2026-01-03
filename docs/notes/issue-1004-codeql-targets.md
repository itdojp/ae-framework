# Issue #1004: CodeQL Alert Triage Targets (2026-01-03)

This note captures the current open CodeQL alerts related to Issue #1004 so fixes can be planned in small PRs.

## Current alert status (open)

### Severity distribution

- Open **CodeQL code scanning alerts** are currently **note** and **warning** only (no error/critical severities in the CodeQL list). This statement applies only to CodeQL alerts and does **not** include dependency vulnerability alerts (e.g., CVEs), which are tracked separately in Issue #1004 and may still include HIGH/CRITICAL severities.

### Warning rules (open counts)

| Rule | Count |
| --- | --- |
| `js/file-system-race` | 15 |
| `js/shell-command-injection-from-environment` | 15 |
| `js/file-access-to-http` | 7 |
| `js/useless-assignment-to-local` | 5 |
| `js/http-to-file-access` | 2 |
| `js/incomplete-sanitization` | 2 |
| `js/indirect-command-line-injection` | 2 |
| `js/insecure-randomness` | 1 |

### Warning hotspots: `js/file-system-race` (top paths)

- `scripts/cegis-report-cleanup.mjs`: 2
- `src/commands/adapt/jest.ts`: 2
- `src/commands/adapt/vitest.ts`: 2
- `scripts/check-a11y-threshold.cjs`: 1
- `scripts/check-opa-compliance.cjs`: 1
- `scripts/hermetic-ci-enhancer.js`: 1
- `scripts/integrated-ci-test-optimizer.mjs`: 1
- `src/cli/quality-cli.ts`: 1
- `src/commands/ci/scaffold.ts`: 1
- `src/integration/hybrid-intent-system.ts`: 1
- `src/providers/recorder.ts`: 1
- `src/self-improvement/setup-git-hooks.ts`: 1

### Warning hotspots: `js/shell-command-injection-from-environment` (top paths)

- `src/agents/rust-verification-agent.ts`: 6
- `scripts/accessibility-analyzer.js`: 4
- `scripts/security-analyzer.js`: 3
- `src/services/container/docker-engine.ts`: 1
- `src/services/container/podman-engine.ts`: 1

### `src/testing/repro-writer.ts`

- **No open alerts** found in the current CodeQL open list.
- The previously referenced "improper code sanitization" issue does not appear in open alerts; confirm if it is already resolved or now suppressed.

### `scripts/coverage/pr-coverage-summary.mjs`

| Alert | Rule | Severity | Line | Message | Link |
| --- | --- | --- | --- | --- | --- |
| #936 | `js/file-access-to-http` | warning | 255 | Outbound network request depends on file data. | https://github.com/itdojp/ae-framework/security/code-scanning/936 |
| #935 | `js/file-access-to-http` | warning | 255 | Outbound network request depends on file data. | https://github.com/itdojp/ae-framework/security/code-scanning/935 |
| #934 | `js/file-access-to-http` | warning | 248 | Outbound network request depends on file data. | https://github.com/itdojp/ae-framework/security/code-scanning/934 |
| #933 | `js/file-access-to-http` | warning | 248 | Outbound network request depends on file data. | https://github.com/itdojp/ae-framework/security/code-scanning/933 |
| #932 | `js/file-access-to-http` | warning | 240 | Outbound network request depends on file data. | https://github.com/itdojp/ae-framework/security/code-scanning/932 |

## Dependency notes

- `package.json` specifies `ws` **8.18.3** (issue text referenced 8.13.0).
- `pnpm-lock.yaml` shows `esbuild` **0.27.2** and `@esbuild/linux-x64` **0.27.2** (issue text referenced 0.21.5).
- If the security alerts still reference older versions, confirm whether other workspaces or cached artifacts are being scanned.

## Next steps (proposed)

1. Address `scripts/coverage/pr-coverage-summary.mjs` alerts by narrowing outbound requests to exclude file-derived payloads or introducing explicit sanitization/allowlists.
2. Re-validate dependency alerts in GitHub Security to confirm whether any critical/high CVEs remain open for `ws` or `esbuild`.
