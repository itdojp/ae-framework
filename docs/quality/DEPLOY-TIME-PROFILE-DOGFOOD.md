---
docRole: ssot
canonicalSource:
- profiles/minimal.yaml
- profiles/standard.yaml
- profiles/full.yaml
- scripts/profiles/dogfood-ci-profiles.mjs
- scripts/ci/run-verify-lite-local.sh
lastVerified: '2026-07-04'
owner: quality-maintainers
verificationCommand: pnpm -s run profiles:dogfood -- --profile all --no-write
---

# Deploy-time profile dogfood policy

This document records the Phase 3 dogfood boundary for deploy-time profiles.

## Profile to CI mapping

| Repository CI surface | Deploy-time profile | Decision semantics |
| --- | --- | --- |
| `verify:lite` / Verify Lite required check | `minimal` | Required deploy-time checks: `verify-lite`, `policy-gate`, `gate`. The local `verify:lite` runner runs the minimal profile replay during the existing Verify Lite pipeline after the root build and before state-machine/context-pack checks. |
| Current PR verification | `standard` | Same required checks as minimal, with Context Pack / property / MBT / conformance lanes recorded as advisory profile lanes where present. |
| Nightly and label-gated heavy lanes | `full` | Same required checks as current PR gating, with formal, mutation, and heavy-test trend lanes recorded as advisory profile lanes unless a future policy promotes them. |

## Replay evidence

Run:

```bash
pnpm -s run profiles:dogfood -- --profile all --fixture fixtures/profiles/dogfood/recent-pr-gate-decisions.json
```

The replay uses `@ae-framework/core` to validate `profiles/{minimal,standard,full}.yaml`, aggregate
profile evidence, and evaluate required-check decisions from the deterministic fixture. The fixture
contains 20 documented PR-equivalent cases and covers both pass and blocking outcomes.

## Drift handling

A drift is any case where the profile-derived required-check decision differs from the recorded
current CI decision. The dogfood report exits non-zero when drift is present. Drift must be fixed
in the profile mapping or documented in a follow-up issue before merge.

The report is intentionally a repository dogfood signal, not a new external adoption claim. It does
not publish Marketplace or npm assets; that remains Phase 4.
