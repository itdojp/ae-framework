# Issue #1006: Script Alias Map (Draft, Phase 1)

## Purpose
- Track alias mapping during the transition without removing existing scripts.
- Provide a reference for which legacy scripts should point to the new entry points.

## Draft aliases (Phase 1)
Note: the JSON source of truth is `scripts/admin/script-alias-map.json`. This document summarizes it for review.
| Legacy script | Proposed alias target | Rationale |
| --- | --- | --- |
| `test:ci` | `node scripts/test/run.mjs --profile=ci` | Preserve CI entry while moving to unified test entry point. |
| `test:ci:lite` | `node scripts/test/run.mjs --profile=ci-lite` | Keep Verify Lite split intact. |
| `test:ci:extended` | `node scripts/test/run.mjs --profile=ci-extended` | Heavy suite remains opt-in via profile. |
| `quality:run:all` | `node scripts/quality/run.mjs --profile=all` | Keep existing aggregation behavior. |
| `quality:gates` | `node scripts/quality/run.mjs --profile=gates` | CI still calls gates; alias keeps the entry stable. |
| `verify:lite` | `node scripts/verify/run.mjs --profile=lite` | Map to Verify Lite default profile. |
| `verify:conformance` | `node scripts/verify/run.mjs --profile=conformance` | Maintain conformance as a named profile. |
| `flake:detect` | `node scripts/flake/run.mjs --profile=detect` | Align detect with unified flake entry. |
| `flake:detect:quick` | `node scripts/flake/run.mjs --profile=quick` | Keep quick as profile flag. |
| `security:integrated:quick` | `node scripts/security/run.mjs --profile=quick` | Default quick path for PR gating. |

## Notes
- `scripts/admin/run-script-alias.mjs` で alias 実行時の警告と転送を行う。
- 既存スクリプト名は 2 リリース維持（詳細は `docs/notes/issue-1006-script-migration-plan.md`）。

## Next
- `pnpm run help` の出力と docs を移行ガイドに合わせて調整。
