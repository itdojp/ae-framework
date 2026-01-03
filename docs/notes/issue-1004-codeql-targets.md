# Issue #1004: CodeQL Alert Triage Targets (2026-01-03)

This note captures the current open CodeQL alerts related to Issue #1004 so fixes can be planned in small PRs.

## Current alert status (open)

### `src/testing/repro-writer.ts`

- **No open alerts** found in the current CodeQL open list.
- The previously referenced "improper code sanitization" issue does not appear in open alerts; confirm if it is already resolved or now suppressed.

### `scripts/coverage/pr-coverage-summary.mjs`

| Alert | Rule | Severity | Line | Message | Link |
| --- | --- | --- | --- | --- | --- |
| #936 | `js/file-access-to-http` | warning | 257 | Outbound network request depends on file data. | https://github.com/itdojp/ae-framework/security/code-scanning/936 |
| #935 | `js/file-access-to-http` | warning | 257 | Outbound network request depends on file data. | https://github.com/itdojp/ae-framework/security/code-scanning/935 |
| #934 | `js/file-access-to-http` | warning | 249 | Outbound network request depends on file data. | https://github.com/itdojp/ae-framework/security/code-scanning/934 |
| #933 | `js/file-access-to-http` | warning | 249 | Outbound network request depends on file data. | https://github.com/itdojp/ae-framework/security/code-scanning/933 |
| #932 | `js/file-access-to-http` | warning | 240 | Outbound network request depends on file data. | https://github.com/itdojp/ae-framework/security/code-scanning/932 |

## Dependency notes

- `package.json` specifies `ws` **8.18.3** (issue text referenced 8.13.0).
- `pnpm-lock.yaml` shows `esbuild` **0.27.2** and `@esbuild/linux-x64` **0.27.2** (issue text referenced 0.21.5).
- If the security alerts still reference older versions, confirm whether other workspaces or cached artifacts are being scanned.

## Next steps (proposed)

1. Address `scripts/coverage/pr-coverage-summary.mjs` alerts by narrowing outbound requests to exclude file-derived payloads or introducing explicit sanitization/allowlists.
2. Re-validate dependency alerts in GitHub Security to confirm whether any critical/high CVEs remain open for `ws` or `esbuild`.

