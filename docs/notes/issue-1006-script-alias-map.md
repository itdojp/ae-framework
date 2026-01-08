# Issue #1006: Script Alias Map (Draft, Phase 1)

## Purpose
- Track alias mapping during the transition without removing existing scripts.
- Provide a reference for which legacy scripts should point to the new entry points.

## Draft aliases (Phase 1)
| Legacy script | Proposed alias target | Rationale |
| --- | --- | --- |
| `test:ci` | `scripts/test/run.mjs --profile=ci` | Preserve CI entry while moving to unified test entry point. |
| `test:ci:lite` | `scripts/test/run.mjs --profile=ci-lite` | Keep Verify Lite split intact. |
| `test:ci:extended` | `scripts/test/run.mjs --profile=ci-extended` | Heavy suite remains opt-in via profile. |
| `quality:run:all` | `scripts/quality/run.mjs --profile=all` | Keep existing aggregation behavior. |
| `quality:gates` | `scripts/quality/run.mjs --profile=gates` | CI still calls gates; alias keeps the entry stable. |
| `verify:lite` | `scripts/verify/run.mjs --profile=lite` | Map to Verify Lite default profile. |
| `verify:conformance` | `scripts/verify/run.mjs --profile=conformance` | Maintain conformance as a named profile. |
| `flake:detect` | `scripts/flake/run.mjs --profile=detect` | Align detect with unified flake entry. |
| `flake:detect:quick` | `scripts/flake/run.mjs --profile=quick` | Keep quick as profile flag. |
| `security:integrated:quick` | `scripts/security/run.mjs --profile=quick` | Default quick path for PR gating. |

## Notes
- This file is a planning artifact; no runtime behavior changes are implied yet.
- Any alias should emit a deprecation warning once the entry points exist.

## Next
- Implement `scripts/<category>/run.mjs` shells and wire aliases.
- Move this mapping into `scripts/admin/script-alias-map.json` once the runner exists.
