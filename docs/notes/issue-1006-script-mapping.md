# Issue #1006: Script Mapping Draft (2026-01-08)

## Goal
- Phase 1 categories for script consolidation (test/quality/verify/flake/security) into draft entry points.
- Provide a starting point for the migration work without changing behavior yet.

## Draft mapping (Phase 1)
| Category | Current scripts (candidates) | Proposed entry point (draft) | Notes |
| --- | --- | --- | --- |
| test | test, test:ci:lite, test:ci:extended, test:fast, test:int | scripts/test/run.mjs --profile=ci-lite | Profiles are placeholders; map to existing commands first. |
| quality | quality:run:all, quality:gates, quality:policy, quality:report, quality:validate | scripts/quality/run.mjs --profile=all | Keep `quality:gates` as the CI alias during transition. |
| verify | verify:lite, verify:conformance, verify:formal, verify:tla, verify:smt | scripts/verify/run.mjs --profile=lite | Align with Verify Lite / Extended split. |
| flake | flake:detect, flake:detect:quick, flake:isolate, flake:report, flake:recover | scripts/flake/run.mjs --profile=detect | Keep quick/thorough as flags. |
| security | security:scan, security:audit, security:secrets, security:check-headers, security:integrated:quick | scripts/security/run.mjs --profile=quick | CI uses integrated:quick as default. |

## Notes
- "Proposed entry point" は実装済みだが、後方互換のため alias/deprecation を併用する。
- Mapping は削除前提ではなく、移行期間中の互換を優先する。

## Next steps
- Validate this mapping against CI usage (workflows + docs).
- Add a detailed alias map (scripts/admin/script-alias-map.json) before any script removal.
